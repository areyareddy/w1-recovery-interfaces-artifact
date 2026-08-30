"""Step s52 -- arm F and the completed feedback x prior-attempt factorial. CPU only.

Governed by spec/ARM_F_SPEC.md. Every contrast below was frozen in that document before
data/armf.sqlite held a completion. All are EXPLORATORY: E' was already generated and
analysed when these contrasts were chosen, which is disclosed in ARM_F_SPEC.md section 5.

                 no attempt    attempt
    no feedback      A            C
    feedback         F            E'

    E' - F   prior-attempt access with genuine feedback present   <- primary interest
    F  - A   feedback alone (referent asymmetry, spec section 2)
    F  - B   grounded compiler error vs static failure-class guidance
    F  - C   swapping the attempt for its diagnosis
    (E'-F) - (C-A)   the interaction: INTERVAL ONLY, never a test at this n

ONE EXTRA QUANTITY, NOT IN THE SPEC AS A CONTRAST. S(F, own prior) asks whether the
compiler error block alone lets the model reconstruct the rejected proof: the <error>
markers quote fragments of the submitted code, so some leakage is possible by
construction. If S(F, own) sits in the unrelated-root null band there is no leak worth
worrying about; if it is elevated, that is a confound in F - A and must be disclosed.
It is reported descriptively either way and enters no contrast.
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
ARMF = ROOT / "data/armf.sqlite"
OUT = ROOT / "audit/armf_analysis.json"
BASE_URL = "http://127.0.0.1:8080"
EXPECTED = 21


def load(db: Path, cohort: str) -> dict:
    con = sqlite3.connect(f"file:{db}?mode=ro", uri=True)
    rows = {r[0]: {"verified": bool(r[1]), "state": r[2], "tokens": r[3] or 0,
                   "completion": r[4] or ""}
            for r in con.execute(
                "SELECT root_id, verified, outcome_state, completion_tokens, completion "
                "FROM branches WHERE cohort=? AND status='done'", (cohort,))}
    total = con.execute("SELECT count(*) FROM branches").fetchone()[0]
    con.close()
    assert len(rows) == total == EXPECTED, (
        f"{cohort} incomplete: {len(rows)} done of {total}. A partly-generated cohort is "
        "reported as not run, never as a subset.")
    return rows


def main() -> int:
    try:
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    except (AttributeError, ValueError):
        pass

    print("[1/4] loading and gating")
    f = load(ARMF, "eval_armf")
    ep = load(EPRIME, "eval_eprime")
    con = sqlite3.connect(f"file:{RUNS}?mode=ro", uri=True)
    base: dict[str, dict[str, bool]] = {}
    for arm in ("A", "B", "C", "D", "E"):
        for rid, ver in con.execute(
                "SELECT root_id, verified FROM branches WHERE cohort='primary_eval' "
                "AND arm=? AND status='done'", (arm,)):
            base.setdefault(rid, {})[arm] = bool(ver)
    con.close()

    roots = sorted(f)
    assert sorted(ep) == roots, "F and E' do not cover the same roots"
    assert sorted(r for r, d in base.items() if "E" in d) == roots, \
        "F/E' subset differs from arm E's 21 roots"
    print(f"      F, E' and arm E all cover the same {len(roots)} roots")

    print("\n[2/4] per-arm verification on the matched subset")
    counts = {a: sum(1 for r in roots if base[r][a]) for a in ("A", "B", "C", "D", "E")}
    counts["Ep"] = sum(1 for r in roots if ep[r]["verified"])
    counts["F"] = sum(1 for r in roots if f[r]["verified"])
    for a in ("A", "B", "C", "D", "E", "F", "Ep"):
        print(f"      {a:>2}: {counts[a]}/{len(roots)}")
    print("\n      the 2x2 (feedback x prior attempt), verified of "
          f"{len(roots)}:")
    print(f"                     no attempt   attempt")
    print(f"        no feedback  A {counts['A']:>2}        C {counts['C']:>2}")
    print(f"        feedback     F {counts['F']:>2}        E' {counts['Ep']:>2}")

    def get(arm):
        if arm == "Ep":
            return lambda r: ep[r]["verified"]
        if arm == "F":
            return lambda r: f[r]["verified"]
        return lambda r: base[r][arm]

    print("\n[3/4] contrasts -- all exploratory, unadjusted, in no Holm family")
    contrasts = []
    for x, y in (("Ep", "F"), ("F", "A"), ("F", "B"), ("F", "C")):
        gx, gy = get(x), get(y)
        x_only = sum(1 for r in roots if gx(r) and not gy(r))
        y_only = sum(1 for r in roots if gy(r) and not gx(r))
        diffs = [(1.0 if gx(r) else 0.0) - (1.0 if gy(r) else 0.0) for r in roots]
        lo, hi = st.bootstrap_ci(diffs)
        rec = {"contrast": f"{x}-{y}", "n": len(roots),
               "x_verified": counts[x], "y_verified": counts[y],
               "x_only": x_only, "y_only": y_only,
               "both": sum(1 for r in roots if gx(r) and gy(r)),
               "effect": round(sum(diffs) / len(roots), 4),
               "ci95": [round(lo, 4), round(hi, 4)],
               "p_exact_mcnemar": round(mcnemar_exact(x_only, y_only), 6),
               "holm_family": None, "tier": "exploratory"}
        contrasts.append(rec)
        print(f"      {rec['contrast']:>6}: {counts[x]}/{len(roots)} vs "
              f"{counts[y]}/{len(roots)}  discordant {x_only}/{y_only}  "
              f"{100 * rec['effect']:+.1f} pts "
              f"[{100 * rec['ci95'][0]:+.1f}, {100 * rec['ci95'][1]:+.1f}]  "
              f"p={rec['p_exact_mcnemar']:.4f}")

    # ---- the interaction: interval only, explicitly not a test --------------------
    gEp, gF, gC, gA = get("Ep"), get("F"), get("C"), get("A")
    inter = [((1.0 if gEp(r) else 0.0) - (1.0 if gF(r) else 0.0))
             - ((1.0 if gC(r) else 0.0) - (1.0 if gA(r) else 0.0)) for r in roots]
    ilo, ihi = st.bootstrap_ci(inter)
    interaction = {"point": round(sum(inter) / len(roots), 4),
                   "ci95": [round(ilo, 4), round(ihi, 4)],
                   "n": len(roots),
                   "note": ("(E'-F) - (C-A). Reported as an interval only. A difference "
                            "of differences on binary outcomes at n=21 has no useful "
                            "resolution and no p-value is computed for it.")}
    print(f"      interaction (E'-F)-(C-A): {100 * interaction['point']:+.1f} pts "
          f"[{100 * interaction['ci95'][0]:+.1f}, {100 * interaction['ci95'][1]:+.1f}] "
          "-- interval only, not a test")

    states: dict[str, int] = {}
    for r in roots:
        states[f[r]["state"]] = states.get(f[r]["state"], 0) + 1
    toks = [f[r]["tokens"] for r in roots]
    print(f"      F terminal states: {states}")
    print(f"      F completion tokens: median {statistics.median(toks):.0f}")

    results = {"n": len(roots), "cohort": "eval_armf", "tier": "exploratory",
               "registered": False, "spec": "spec/ARM_F_SPEC.md",
               "contrast_choice_saw_eprime": True,
               "verified_counts": counts, "contrasts": contrasts,
               "interaction": interaction, "outcome_states": states,
               "completion_tokens": {"median": statistics.median(toks),
                                     "mean": round(statistics.mean(toks), 1)},
               "roots": roots}

    print("\n[4/4] does the error block alone leak the rejected proof?")
    tok = anch.ServerTokenizer(BASE_URL)
    live, detail = tok.probe()
    if not live:
        print(f"      tokenizer unavailable ({detail}); leak check skipped.")
    else:
        prior = {r: tok.tokens((ROOT / "artifacts/roots" / r
                                / "raw_completion.txt").read_text(encoding="utf-8"))
                 for r in roots}
        s_f = [anch.similarity(tok.tokens(f[r]["completion"]), prior[r]) for r in roots]
        band = json.loads((ROOT / "audit/receipts/s04.json").read_text(
            encoding="utf-8"))["stats"]
        mean_f = statistics.mean(s_f)

        # THE RIGHT BASELINE IS ARM A, NOT THE NULL BAND. The unrelated-root band
        # controls for neither the theorem nor the model -- the reviewer's concern 1 --
        # so almost any arm sits above it merely by proving the same theorem, sharing
        # imports, a signature and common tactics. Arm A is the same theorem with NO
        # attempt shown, which is exactly the counterfactual "no leak" condition.
        # Comparing S(F, own) against the null band would manufacture a leak finding.
        import csv as _csv
        s_a = []
        with (ROOT / "audit/anchoring_results.csv").open(encoding="utf-8") as fh:
            for row in _csv.DictReader(fh):
                if (row["cohort"] == "primary_eval" and row["arm"] == "A"
                        and row["root_id"] in f):
                    s_a.append(float(row["anchoring_S"]))
        mean_a = statistics.mean(s_a) if s_a else None
        results["leak_check"] = {
            "mean_S_F_own": round(mean_f, 4),
            "max_S_F_own": round(max(s_f), 4),
            "mean_S_A_own": round(mean_a, 4) if mean_a is not None else None,
            "excess_over_arm_A": round(mean_f - mean_a, 4) if mean_a is not None else None,
            "n_above_null_p95": sum(1 for v in s_f if v > band["null_band_p95"]),
            "null_band": {k: band[k] for k in
                          ("null_band_p50", "null_band_p95", "null_band_max")},
            "baseline": "arm A on the same roots (same theorem, no attempt shown)",
            "note": ("F never shows the attempt. The comparison that matters is against "
                     "arm A, not the unrelated-root band: the band controls for neither "
                     "theorem nor model, so any arm clears it just by proving the same "
                     "theorem. S(F,own) at or below S(A,own) means the <error> block "
                     "does not let the model reconstruct the rejected proof, so F-A is "
                     "not confounded by leakage."),
        }
        lk = results["leak_check"]
        print(f"      S(F, own prior) mean {mean_f:.4f}, max {lk['max_S_F_own']:.4f}")
        print(f"      S(A, own prior) mean {mean_a:.4f}   <- the right baseline")
        print(f"      excess of F over A: {lk['excess_over_arm_A']:+.4f}")
        print(f"      (unrelated-root band p95 {band['null_band_p95']:.3f}; "
              f"{lk['n_above_null_p95']}/{len(roots)} F roots exceed it, but so does "
              "arm A -- that band is the wrong baseline here)")
        if lk["excess_over_arm_A"] is not None and lk["excess_over_arm_A"] <= 0.02:
            print("      => no meaningful leak: the error block does not reconstruct "
                  "the attempt, so F-A is clean on this dimension")

    OUT.write_text(json.dumps(results, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"\nwrote {OUT.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
