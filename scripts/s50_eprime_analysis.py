"""Step s50 -- arm E' analysis. CPU only, no generation.

Governed by spec/EPRIME_SPEC.md. Every estimand, contrast and multiplicity decision below
was fixed in that document before data/eprime.sqlite held a single completion.

THE QUESTION. Arm C shows the failed proof without saying why it failed. E' supplies the
model's own native correction content and holds turn structure fixed, so:

    E' - C   isolates the diagnosis
    E' - A   is the deployed configuration against fresh generation
    E' - E   is conversation structure alone (content byte-identical)

ALL CONTRASTS ARE ON THE MATCHED 21-ROOT NATIVE-FEEDBACK SUBSET. Arm C verifies 0/21 on
that subset while A verifies 5/21; comparing E' against C's full-40 rate would compare two
different root sets and is not done here.

MULTIPLICITY. E' forms no Holm family and joins none; p-values are unadjusted. Adding a
post-hoc arm to a pre-specified family would change the correction applied to the
registered tests. Spec section 5.
"""

from __future__ import annotations

import json
import sqlite3
import statistics
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT / "src"))
sys.path.insert(0, str(HERE))

import anchoring as anch  # noqa: E402
import stats as st  # noqa: E402
from s17_statistical_tests import mcnemar_exact  # noqa: E402

RUNS = ROOT / "data/runs.sqlite"
EPRIME = ROOT / "data/eprime.sqlite"
OUT = ROOT / "audit/eprime_analysis.json"
BASE_URL = "http://127.0.0.1:8080"
EXPECTED = 21


def main() -> int:
    try:
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    except (AttributeError, ValueError):
        pass

    print("[1/4] loading and gating")
    con = sqlite3.connect(f"file:{EPRIME}?mode=ro", uri=True)
    ep = {r[0]: {"verified": bool(r[1]), "state": r[2], "tokens": r[3] or 0,
                 "completion": r[4] or ""}
          for r in con.execute(
              "SELECT root_id, verified, outcome_state, completion_tokens, completion "
              "FROM branches WHERE cohort='eval_eprime' AND status='done'")}
    n_all = con.execute("SELECT count(*) FROM branches").fetchone()[0]
    con.close()
    assert len(ep) == n_all == EXPECTED, (
        f"cohort incomplete: {len(ep)} done of {n_all}. Spec section 8 of "
        "ALLOCATION_SPEC and the same rule here: a partly-generated cohort is reported "
        "as not run, never as a subset.")
    roots = sorted(ep)
    print(f"      E' complete: {len(roots)}/{EXPECTED} branches")

    con = sqlite3.connect(f"file:{RUNS}?mode=ro", uri=True)
    base: dict[str, dict[str, bool]] = {}
    for arm in ("A", "B", "C", "D", "E"):
        for rid, ver in con.execute(
                "SELECT root_id, verified FROM branches WHERE cohort='primary_eval' "
                "AND arm=? AND status='done'", (arm,)):
            base.setdefault(rid, {})[arm] = bool(ver)
    con.close()

    # the 21 E'-eligible roots must be exactly the 21 arm-E roots
    e_roots = sorted(r for r, d in base.items() if "E" in d)
    assert e_roots == roots, (
        "E' eligibility does not match arm E's. The matched subset is not the same set.\n"
        f"  only in E : {sorted(set(e_roots) - set(roots))[:3]}\n"
        f"  only in E': {sorted(set(roots) - set(e_roots))[:3]}")
    print(f"      matched subset gate ok: E' and E cover the same {len(roots)} roots")

    print("\n[2/4] per-arm verification on the matched subset")
    counts = {}
    for arm in ("A", "B", "C", "D", "E"):
        counts[arm] = sum(1 for r in roots if base[r][arm])
    counts["Ep"] = sum(1 for r in roots if ep[r]["verified"])
    for arm in ("A", "B", "C", "D", "E", "Ep"):
        print(f"      {arm:>2}: {counts[arm]}/{len(roots)}")

    print("\n[3/4] contrasts -- exploratory, unadjusted, in no Holm family")

    def get(arm):
        if arm == "Ep":
            return lambda r: ep[r]["verified"]
        return lambda r: base[r][arm]

    contrasts = []
    for x, y in (("Ep", "C"), ("Ep", "A"), ("Ep", "E")):
        gx, gy = get(x), get(y)
        x_only = sum(1 for r in roots if gx(r) and not gy(r))
        y_only = sum(1 for r in roots if gy(r) and not gx(r))
        both = sum(1 for r in roots if gx(r) and gy(r))
        diffs = [(1.0 if gx(r) else 0.0) - (1.0 if gy(r) else 0.0) for r in roots]
        lo, hi = st.bootstrap_ci(diffs)
        rec = {"contrast": f"{x}-{y}", "n": len(roots),
               "x_verified": counts[x], "y_verified": counts[y],
               "x_only": x_only, "y_only": y_only, "both": both,
               "effect": round(sum(diffs) / len(roots), 4),
               "ci95": [round(lo, 4), round(hi, 4)],
               "p_exact_mcnemar": round(mcnemar_exact(x_only, y_only), 6),
               "holm_family": None, "tier": "exploratory"}
        contrasts.append(rec)
        print(f"      {rec['contrast']:>6}: {counts[x]}/{len(roots)} vs "
              f"{counts[y]}/{len(roots)}  discordant {x_only}/{y_only}  "
              f"effect {100 * rec['effect']:+.1f} pts "
              f"[{100 * rec['ci95'][0]:+.1f}, {100 * rec['ci95'][1]:+.1f}]  "
              f"p={rec['p_exact_mcnemar']:.4f}")

    states: dict[str, int] = {}
    for r in roots:
        states[ep[r]["state"]] = states.get(ep[r]["state"], 0) + 1
    toks = [ep[r]["tokens"] for r in roots]
    print(f"      E' terminal states: {states}")
    print(f"      E' completion tokens: median {statistics.median(toks):.0f}")

    results = {
        "n": len(roots), "cohort": "eval_eprime", "tier": "exploratory",
        "registered": False, "spec": "spec/EPRIME_SPEC.md",
        "subset": "matched native-feedback roots (same 21 as arm E)",
        "verified_counts": counts, "contrasts": contrasts,
        "outcome_states": states,
        "completion_tokens": {"median": statistics.median(toks),
                              "mean": round(statistics.mean(toks), 1)},
        "roots": roots,
    }

    print("\n[4/4] anchoring: does supplying the diagnosis change how much is copied?")
    tok = anch.ServerTokenizer(BASE_URL)
    live, detail = tok.probe()
    if not live:
        print(f"      tokenizer unavailable ({detail}); anchoring section skipped.")
        print("      Start the server and re-run; the macros simply will not be emitted.")
    else:
        prior = {r: tok.tokens((ROOT / "artifacts/roots" / r
                                / "raw_completion.txt").read_text(encoding="utf-8"))
                 for r in roots}
        s_ep = [anch.similarity(tok.tokens(ep[r]["completion"]), prior[r]) for r in roots]
        import csv as _csv
        s_c, s_a = [], []
        with (ROOT / "audit/anchoring_results.csv").open(encoding="utf-8") as fh:
            for row in _csv.DictReader(fh):
                if row["cohort"] == "primary_eval" and row["root_id"] in ep:
                    if row["arm"] == "C":
                        s_c.append(float(row["anchoring_S"]))
                    elif row["arm"] == "A":
                        s_a.append(float(row["anchoring_S"]))
        band = json.loads((ROOT / "audit/receipts/s04.json").read_text(
            encoding="utf-8"))["stats"]
        results["anchoring"] = {
            "mean_S_Ep_own": round(statistics.mean(s_ep), 4),
            "mean_S_C_own": round(statistics.mean(s_c), 4) if s_c else None,
            "mean_S_A_own": round(statistics.mean(s_a), 4) if s_a else None,
            "null_band": {k: band[k] for k in
                          ("null_band_p50", "null_band_p95", "null_band_max")},
            "n": len(s_ep),
        }
        a = results["anchoring"]
        print(f"      S(E', own prior) mean {a['mean_S_Ep_own']:.4f}")
        print(f"      S(C , own prior) mean {a['mean_S_C_own']:.4f}")
        print(f"      S(A , own prior) mean {a['mean_S_A_own']:.4f}")
        print(f"      null band p50 {band['null_band_p50']:.3f} / "
              f"p95 {band['null_band_p95']:.3f}")

    OUT.write_text(json.dumps(results, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"\nwrote {OUT.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
