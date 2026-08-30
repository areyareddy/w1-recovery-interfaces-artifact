"""Step s23 -- analyse arm C' (mismatched prior attempt). Run after s12 fills cprime.sqlite.

    python scripts\\s23_cprime_analysis.py

THE DECOMPOSITION. Arm C shows the prior attempt and verification drops. Three accounts
survive the original design; C' separates them because it holds length, wrapper, format,
theorem and seed fixed and changes only WHOSE failed attempt is in the slot.

    C' - A    generic cost of long, irrelevant text in a non-native single-turn wrapper
    C  - C'   cost of the SPECIFIC rejected trajectory for this theorem

Reading the result:

    C-A large, C'-A near zero      -> commitment to the specific trajectory. The paper's
                                      current framing survives.
    C'-A ~ C-A                     -> the effect is generic long-context or off-format
                                      degradation, NOT prior-attempt content. The paper
                                      must be reframed around interface format.
    both intermediate              -> report the split rather than a single mechanism.

THE ANCHORING SIDE ANSWERS THE TAUTOLOGY OBJECTION. Reviewers noted that measuring edit
similarity to text placed in context mostly tests whether the model copies visible tokens.
C' lets us ask a sharper question, because there are now two reference texts:

    S(C', donor)   does the model copy WHATEVER is in the slot?
    S(C', own)     does it reconstruct ITS OWN prior trajectory, which it cannot see?

If S(C', donor) is as high as S(C, own), copying is generic and anchoring is indeed close
to a manipulation check. If S(C', donor) is markedly lower, then what arm C reproduces is
specifically the theorem-relevant prior attempt, which is a behavioural claim rather than a
tautology. S(C', own) is the cleanest control of all: the model never saw that text, so any
similarity above the unrelated-root null band is convergence on the theorem, not copying.

Arm C' is POST-HOC and disclosed as such. It is not part of the registered design.

SEED BLOCKS. --block selects which of the two C' seed blocks is analysed. Block 2 is the
same 40 theorems under the eval_block2 seed, with a byte-identical donor map, wrapper and
payload set; only the seed differs. The two blocks are therefore reported SEPARATELY and
are NOT 80 roots. Each block's C' is contrasted against the A and C arms of its OWN seed
block, so no contrast ever crosses a seed boundary.
"""

from __future__ import annotations

import argparse
import csv
import json
import random
import sqlite3
import statistics
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT / "src"))
sys.path.insert(0, str(HERE))

import anchoring as anch  # noqa: E402
import receipts  # noqa: E402
import stats as st  # noqa: E402
import s17_statistical_tests as pair  # noqa: E402
import s27_interaction_resolution as s27  # noqa: E402

RUNS_DB = ROOT / "data/runs.sqlite"
PAIRING = ROOT / "audit/cprime_pairing.csv"
ANCHOR_CSV = ROOT / "audit/anchoring_results.csv"
BASE_URL = "http://127.0.0.1:8080"

# spec/CPRIME_SPEC.md, frozen while all 40 block-1 branches were pending. Block 2 reuses
# this pairing verbatim, so the value governs both blocks.
FROZEN_DONOR_MAP_SHA = "ea0ea22a3196e841c7cac9df702cd0fc26cbefab73e6e15dcfb89546ce167a4b"

# Only the data sources differ between blocks. base_cohort is the cohort supplying the
# A and C arms this block's C' is paired against -- always the same seed block.
BLOCKS = {
    1: {"db": "data/cprime.sqlite", "prompts": "data/cprime_prompts.jsonl",
        "cohort": "eval_cprime", "base_cohort": "primary_eval",
        "out": "audit/cprime_analysis.json"},
    2: {"db": "data/cprime_b2.sqlite", "prompts": "data/cprime_b2_prompts.jsonl",
        "cohort": "eval_cprime_b2", "base_cohort": "eval_block2",
        "out": "audit/cprime_b2_analysis.json"},
}


def main(block: int = 1, out_override: str | None = None) -> int:
    receipts.force_utf8()
    cfg = BLOCKS[block]
    cprime_db = ROOT / cfg["db"]
    out_path = Path(out_override) if out_override else ROOT / cfg["out"]
    if not cprime_db.exists():
        print(f"{cfg['db']} not found -- build it first")
        return 2

    # spec/CPRIME_SPEC.md: the frozen identity is re-asserted AT ANALYSIS TIME, not only
    # at build time. A mismatch means the arm was rebuilt and the spec no longer
    # describes what ran, so refuse rather than report.
    donor_rows = list(csv.DictReader(PAIRING.open(encoding="utf-8")))
    donor = {r["root_id"]: r["donor_root_id"] for r in donor_rows}
    canon = receipts.sha_text("\n".join(f"{r}->{donor[r]}" for r in sorted(donor)))
    if canon != FROZEN_DONOR_MAP_SHA:
        print(f"donor map sha256 {canon}\n  expected      {FROZEN_DONOR_MAP_SHA}")
        print("the pairing was rebuilt; spec/CPRIME_SPEC.md no longer describes it")
        return 2
    print(f"[0/5] seed block {block}: donor map matches the frozen value {canon[:16]}...")

    cp = sqlite3.connect(f"file:{cprime_db}?mode=ro", uri=True)
    n_done = cp.execute("SELECT count(*) FROM branches WHERE status='done'").fetchone()[0]
    n_all = cp.execute("SELECT count(*) FROM branches").fetchone()[0]
    print(f"[1/5] arm C' block {block}: {n_done}/{n_all} generated")
    if n_done != n_all:
        print("      incomplete -- generate first:")
        print(f"      python scripts\\s12_run.py --db {cfg['db']} "
              f"--prompts {cfg['prompts']} --cohort {cfg['cohort']}")
        return 2

    cprime = {r[0]: {"verified": r[1], "state": r[2], "tokens": r[3],
                     "completion": r[4]}
              for r in cp.execute("SELECT root_id, verified, outcome_state, "
                                  "completion_tokens, completion FROM branches "
                                  "WHERE status='done'")}
    cp.close()

    con = sqlite3.connect(f"file:{RUNS_DB}?mode=ro", uri=True)
    base = {}
    for root_id, arm, v, state, tok in con.execute(
            "SELECT root_id, arm, verified, outcome_state, completion_tokens "
            "FROM branches WHERE cohort=? AND status='done' "
            "AND arm IN ('A','C')", (cfg["base_cohort"],)):
        base.setdefault(root_id, {})[arm] = {"verified": v, "state": state, "tokens": tok}
    con.close()

    results: dict = {"n": len(cprime), "post_hoc": True, "seed_block": block,
                     "cohort": cfg["cohort"], "base_cohort": cfg["base_cohort"],
                     "donor_map_sha256": canon}

    # ------------------------------------------------------------ verification
    print("\n[2/5] verification contrasts (exact McNemar, paired within root)")
    def contrast(xname, xget, yname, yget):
        rows = [(xget(r), yget(r)) for r in cprime if r in base]
        b = sum(1 for x, y in rows if x == 1 and y == 0)
        c = sum(1 for x, y in rows if x == 0 and y == 1)
        both = sum(1 for x, y in rows if x == 1 and y == 1)
        p = pair.mcnemar_exact(b, c)
        eff = (b - c) / len(rows)
        # Interval on the same paired quantity the test addresses: resample roots, the
        # independent unit, and recompute the mean within-root difference.
        lo, hi = st.bootstrap_ci([x - y for x, y in rows])
        print(f"      {xname}-{yname}  n={len(rows):3d}  {xname}-only {b:2d}  "
              f"{yname}-only {c:2d}  both {both:2d}  effect {eff:+.3f} "
              f"[{lo:+.3f}, {hi:+.3f}]  p={p:.4f}{'*' if p < 0.05 else ''}")
        return {"contrast": f"{xname}-{yname}", "n": len(rows), "x_only": b,
                "y_only": c, "both": both, "effect": round(eff, 4),
                "ci95": [round(lo, 4), round(hi, 4)],
                "p_exact_mcnemar": round(p, 6)}

    v_cp = lambda r: cprime[r]["verified"]
    v_a = lambda r: base[r]["A"]["verified"]
    v_c = lambda r: base[r]["C"]["verified"]
    results["verification"] = [
        contrast("Cp", v_cp, "A", v_a),     # generic long-context / format cost
        contrast("C", v_c, "Cp", v_cp),     # the specific rejected trajectory
        contrast("C", v_c, "A", v_a),       # reference: the published contrast
    ]

    # MULTIPLICITY, declared in docs/CPRIME_SPEC.md before any C' branch was generated.
    # The family is the two NEW verification tests that C' exists to answer, C'-A and
    # C-C'. C-A is already reported in the paper under its own within-block family and
    # is reproduced here only as a reference line; folding it in a second time would
    # penalise a result twice for having been looked at once.
    family = ["Cp-A", "C-Cp"]
    fam = [r for r in results["verification"] if r["contrast"] in family]
    adj = st.holm({r["contrast"]: r["p_exact_mcnemar"] for r in fam})
    for r in fam:
        r["p_holm"] = round(adj[r["contrast"]], 6)
        r["holm_family"] = "cprime_verification"
    print(f"      Holm over {family}: " + ", ".join(
        f"{r['contrast']} p={r['p_exact_mcnemar']:.4f} -> {r['p_holm']:.4f}" for r in fam))
    results["holm_family"] = {"members": family, "reference_only": ["C-A"]}
    rates = {"A": sum(v_a(r) for r in cprime if r in base),
             "C": sum(v_c(r) for r in cprime if r in base),
             "Cp": sum(v_cp(r) for r in cprime)}
    print(f"      verified: A {rates['A']}/{len(cprime)}, C {rates['C']}/{len(cprime)}, "
          f"C' {rates['Cp']}/{len(cprime)}")
    results["verified_counts"] = rates

    # ------------------------------------------------------------ tokens / truncation
    print("\n[3/5] generation length and truncation")
    for label, get_t, get_s in (
            ("A", lambda r: base[r]["A"]["tokens"], lambda r: base[r]["A"]["state"]),
            ("C", lambda r: base[r]["C"]["tokens"], lambda r: base[r]["C"]["state"]),
            ("C'", lambda r: cprime[r]["tokens"], lambda r: cprime[r]["state"])):
        ts = [get_t(r) for r in cprime if r in base]
        tr = sum(1 for r in cprime if r in base and get_s(r) == "truncated")
        print(f"      {label:2}  mean {statistics.mean(ts):6.0f} tok   "
              f"truncated {tr}/{len(ts)} ({100 * tr / len(ts):.1f}%)")
        results.setdefault("length", []).append(
            {"arm": label, "mean_tokens": round(statistics.mean(ts), 1),
             "truncated": tr, "n": len(ts)})

    # -------------------------------------------- same-group sensitivity + resolution
    # Both are promised by spec/CPRIME_SPEC.md and were missing from this script.
    # Section 3: "If C - C' is informative, the analysis is repeated on the 28/40
    # same-group pairs and the difference reported; that repetition is descriptive and
    # enters no test family."
    # Section 7: "its own resolution will be computed from the realised discordant counts
    # by the same root-resampling method as scripts/s27_interaction_resolution.py".
    print("\n[4/5] same-coarse-group sensitivity and contrast resolution")

    same = {r["root_id"] for r in donor_rows if r["same_coarse_group"] == "1"}
    shared = [r for r in sorted(cprime) if r in base]

    def restricted(xname, xget, yname, yget, rs):
        b = sum(1 for r in rs if xget(r) == 1 and yget(r) == 0)
        c = sum(1 for r in rs if xget(r) == 0 and yget(r) == 1)
        n = len(rs)
        return {"contrast": f"{xname}-{yname}", "n": n, "x_only": b, "y_only": c,
                "effect": round((b - c) / n, 4) if n else None,
                "p_exact_mcnemar": round(pair.mcnemar_exact(b, c), 6)}

    sens = []
    print("      descriptive only -- enters no test family (spec section 3)")
    for xn, xg, yn, yg in (("C", v_c, "Cp", v_cp), ("Cp", v_cp, "A", v_a)):
        full = restricted(xn, xg, yn, yg, shared)
        sub = restricted(xn, xg, yn, yg, [r for r in shared if r in same])
        sens.append({"all_pairs": full, "same_coarse_group": sub})
        print(f"      {xn}-{yn:2}  all {full['n']} pairs: {full['effect']:+.4f}"
              f"   same-group {sub['n']} pairs: {sub['effect']:+.4f}")
    results["same_group_sensitivity"] = {
        "n_same_coarse_group": len(same & set(shared)),
        "note": ("Donor group crossing is invisible in the C' stimulus -- the wrapper "
                 "carries no error text -- so this is a descriptive check, not an "
                 "estimand. It enters no test family."),
        "contrasts": sens}

    # Resolution, by s27's own root-resampling routine applied to the paired binary
    # contrast w_i = x_i - y_i in {-1, 0, +1}.
    rng = random.Random(s27.SEED)
    res = []
    for xn, xg, yn, yg in (("C", v_c, "Cp", v_cp), ("Cp", v_cp, "A", v_a)):
        w = [xg(r) - yg(r) for r in shared]
        n = len(w)
        b = sum(1 for x in w if x > 0)
        c = sum(1 for x in w if x < 0)
        # exact variance of the paired proportion difference (b-c)/n
        se = ((b + c - (b - c) ** 2 / n) / n ** 2) ** 0.5
        mde_a = (s27.Z_ALPHA + s27.Z_POWER) * se
        sim = None
        for delta in [x / 100 for x in range(1, 61)]:
            if s27.power_at(w, delta, s27.REPS, rng) >= 0.80:
                sim = round(delta, 2)
                break
        obs = abs(sum(w) / n)
        res.append({"contrast": f"{xn}-{yn}", "n": n, "x_only": b, "y_only": c,
                    "se": round(se, 4), "mde_analytic_80": round(mde_a, 4),
                    "mde_simulated_80": sim, "observed_abs_effect": round(obs, 4),
                    "resolved": obs >= mde_a})
        print(f"      {xn}-{yn:2}  SE {se:.4f}   analytic 80% MDE {mde_a:.3f}"
              f"   simulated {sim if sim else '>0.60'}"
              f"   observed {obs:.3f}  -> "
              f"{'resolved' if obs >= mde_a else 'UNDER-RESOLVED'}")
    results["resolution"] = {
        "method": ("paired binary contrast w = x - y over roots; analytic SE from the "
                   "exact variance of (b-c)/n; simulated MDE by the centred root "
                   "resampling of scripts/s27_interaction_resolution.py"),
        "alpha": 0.05, "power": 0.80, "reps": s27.REPS, "seed": s27.SEED,
        "contrasts": res}
    print("      A null C-C' at this n is NOT an equivalence claim (spec section 7).")

    # ------------------------------------------------------------ anchoring
    print(f"\n[5/5] anchoring: does the model copy WHATEVER is in the slot?")
    tok = anch.ServerTokenizer(BASE_URL)
    live, detail = tok.probe()
    if not live:
        print(f"      tokenizer unavailable ({detail}); skipping the anchoring section.")
        print("      Start the server and re-run to complete it.")
    else:
        prior_tokens = {}
        for d in sorted((ROOT / "artifacts/roots").iterdir()):
            if d.is_dir():
                prior_tokens[d.name] = tok.tokens(
                    (d / "raw_completion.txt").read_text(encoding="utf-8"))
        s_own, s_donor = [], []
        for rid, rec in sorted(cprime.items()):
            t = tok.tokens(rec["completion"] or "")
            s_own.append(anch.similarity(t, prior_tokens[rid]))
            s_donor.append(anch.similarity(t, prior_tokens[donor[rid]]))
        anchor_c = {}
        for r in csv.DictReader(ANCHOR_CSV.open(encoding="utf-8")):
            if r["cohort"] == cfg["base_cohort"] and r["arm"] in ("A", "C"):
                anchor_c.setdefault(r["root_id"], {})[r["arm"]] = \
                    float(r["anchoring_S"])
        s_c = [anchor_c[r]["C"] for r in sorted(cprime) if r in anchor_c]
        s_a = [anchor_c[r]["A"] for r in sorted(cprime) if r in anchor_c]

        band = json.loads((ROOT / "audit/receipts/s04.json").read_text(
            encoding="utf-8"))["stats"]
        print(f"      null band (unrelated roots): p50 {band['null_band_p50']:.3f}, "
              f"p95 {band['null_band_p95']:.3f}, max {band['null_band_max']:.3f}")
        print(f"      S(A , own prior)   mean {statistics.mean(s_a):.4f}")
        print(f"      S(C , own prior)   mean {statistics.mean(s_c):.4f}   "
              f"<- copies the text it was shown")
        print(f"      S(C', donor)       mean {statistics.mean(s_donor):.4f}   "
              f"<- copies whatever it was shown?")
        print(f"      S(C', own prior)   mean {statistics.mean(s_own):.4f}   "
              f"<- never saw this text")
        results["anchoring"] = {
            "null_band": {k: band[k] for k in band if k.startswith("null_band")},
            "mean_S_A_own": round(statistics.mean(s_a), 4),
            "mean_S_C_own": round(statistics.mean(s_c), 4),
            "mean_S_Cp_donor": round(statistics.mean(s_donor), 4),
            "mean_S_Cp_own": round(statistics.mean(s_own), 4),
            "n": len(s_own)}
        gap = statistics.mean(s_c) - statistics.mean(s_donor)
        print(f"\n      S(C,own) - S(C',donor) = {gap:+.4f}")
        if abs(gap) < 0.05:
            print("      => copying is GENERIC. Anchoring is close to a manipulation")
            print("         check and should be reported as one.")
        else:
            print("      => the model reproduces its own theorem-relevant attempt more")
            print("         than an arbitrary one. Anchoring is a behavioural claim.")

    out_path.write_text(json.dumps(results, indent=2, sort_keys=True) + "\n",
                        encoding="utf-8")
    print(f"\nwrote {out_path}")
    print("\nArm C' is POST-HOC and must be labelled as such wherever it is reported.")
    return 0


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--block", type=int, choices=sorted(BLOCKS), default=1,
                    help="C' seed block to analyse (default 1)")
    ap.add_argument("--out", default=None,
                    help="override the output path (for verification runs)")
    a = ap.parse_args()
    raise SystemExit(main(a.block, a.out))
