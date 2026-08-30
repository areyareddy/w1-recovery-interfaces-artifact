"""Step s18 -- Analysis 3: does the prior attempt hurt everywhere, or somewhere specific?

The headline is that supplying the prior attempt reduces verification success. The obvious
mechanism question is whether that is uniform, or driven by one kind of root.

The natural suspect was the TRUNCATED group, on the theory that a model shown a
half-finished proof would continue a doomed derivation. THE DATA REJECTS THAT. The deficit
is concentrated instead among roots whose prior attempt was COMPLETE but incorrect.

What can be said, and it is narrow:

  The verification deficit is concentrated DESCRIPTIVELY among roots whose prior attempt
  was complete but incorrect. On those roots, reuse produces markedly shorter and more
  textually anchored completions. This is CONSISTENT WITH commitment to a finished
  erroneous artifact rather than continued exploration, but subgroup sizes are small and
  the mechanism remains hypothesis-generating.

What must NOT be said: that the model "commits instead of exploring". Neither commitment
nor exploration was measured. Completion length and textual anchoring were.

Three qualifications that a summary table can hide, so they are printed below in full:
  - truncation does NOT move one way. On INCOMPLETE roots arm C truncates MORE than A in
    both eval blocks, and diffuse block 2 also has C above A. Only on complete-proof roots
    in block 1 does C truncate less.
  - the subgroup heterogeneity is not significant on a descriptive chi-square, and that
    check itself ignores the repeated-root structure.
  - the 80 pooled eval observations are 40 ROOTS under two seeds, not 80 independent
    roots. The tested results are the separate block-1 and block-2 McNemar contrasts; this
    subgroup table is descriptive and is not a new confirmatory test.

Coarse groups (a W1/W2 definition, not inherited from CoLM -- disclose as ours):

    incomplete          truncated                       -- artifact is a partial proof
    localized_complete  linarith/nlinarith/simp/type/id -- complete proof, local error
    diffuse_complete    unsolved_goals/other/timeout    -- complete proof, diffuse error

Reported per group: the paired verification contrast with an exact McNemar, the anchoring
difference, and the change in truncation rate. Each group is small, so these are
descriptive comparisons that motivate a mechanism -- not confirmatory subgroup tests, and
they are not corrected for multiplicity. Stated that way in the paper.
"""

from __future__ import annotations

import csv
import json
import sqlite3
import statistics
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT / "src"))
sys.path.insert(0, str(HERE))

import receipts  # noqa: E402
import s17_statistical_tests as tests  # noqa: E402

DB = ROOT / "data/runs.sqlite"
ANCHOR = ROOT / "audit/anchoring_results.csv"
OUT = ROOT / "audit/failure_class_analysis.json"

GROUPS = ["incomplete", "localized_complete", "diffuse_complete"]


def main() -> int:
    receipts.force_utf8()
    con = sqlite3.connect(f"file:{DB}?mode=ro", uri=True)

    anchor = {}
    if ANCHOR.exists():
        for r in csv.DictReader(ANCHOR.open(encoding="utf-8")):
            anchor.setdefault((r["cohort"], r["root_id"]), {})[r["arm"]] = \
                float(r["anchoring_S"])

    results = []
    for cohort, label in (("primary_eval", "eval-40 block 1 (PRE-REGISTERED)"),
                          ("eval_block2", "eval-40 block 2 (replication)"),
                          ("full_pool_dev", "dev-43 (descriptive)")):
        print("=" * 78)
        print(label)
        print("=" * 78)
        for x, y in (("C", "A"), ("D", "B")):
            print(f"\n  {x} vs {y}")
            print(f"    {'group':20} {'n':>3}  {'x':>3} {'y':>3} {'both':>4} "
                  f"{'p':>7}   {'dS':>7}  {'trunc ' + x:>8} {'trunc ' + y:>8}")
            for g in GROUPS:
                rows = list(con.execute(
                    "SELECT root_id, "
                    "  max(CASE WHEN arm=? THEN verified END), "
                    "  max(CASE WHEN arm=? THEN verified END), "
                    "  max(CASE WHEN arm=? THEN outcome_state='truncated' END), "
                    "  max(CASE WHEN arm=? THEN outcome_state='truncated' END) "
                    "FROM branches WHERE cohort=? AND status='done' AND arm IN (?,?) "
                    "AND coarse_failure_group=? GROUP BY root_id HAVING count(*)=2",
                    (x, y, x, y, cohort, x, y, g)))
                if not rows:
                    continue
                b = sum(1 for _, a, bb, _, _ in rows if a == 1 and bb == 0)
                c = sum(1 for _, a, bb, _, _ in rows if a == 0 and bb == 1)
                both = sum(1 for _, a, bb, _, _ in rows if a == 1 and bb == 1)
                p = tests.mcnemar_exact(b, c)
                tx = statistics.mean(r[3] for r in rows)
                ty = statistics.mean(r[4] for r in rows)

                diffs = []
                for r in rows:
                    v = anchor.get((cohort, r[0]), {})
                    if x in v and y in v:
                        diffs.append(v[x] - v[y])
                ds = statistics.mean(diffs) if diffs else float("nan")

                star = "*" if p < 0.05 else " "
                print(f"    {g:20} {len(rows):3d}  {b:3d} {c:3d} {both:4d} "
                      f"{p:7.4f}{star} {ds:+7.3f}  {tx:8.2f} {ty:8.2f}")
                results.append({
                    "cohort": cohort, "contrast": f"{x}-{y}", "group": g,
                    "n_pairs": len(rows), "x_only": b, "y_only": c, "both": both,
                    "p_exact_mcnemar": round(p, 6),
                    "mean_anchoring_diff": round(ds, 6) if diffs else None,
                    "truncation_rate_x": round(tx, 4),
                    "truncation_rate_y": round(ty, 4),
                })
    con.close()

    print("\n" + "=" * 78)
    print("Reading")
    print("=" * 78)
    ev = [r for r in results if r["contrast"] == "C-A"
          and r["cohort"] in ("primary_eval", "eval_block2")]
    for g in GROUPS:
        rows = [r for r in ev if r["group"] == g]
        if not rows:
            continue
        a_only = sum(r["y_only"] for r in rows)
        c_only = sum(r["x_only"] for r in rows)
        n = sum(r["n_pairs"] for r in rows)
        print(f"  {g:20} across both eval blocks: A-only {a_only:2d}, C-only {c_only:2d} "
              f"over {n} paired observations")
    print("\n  Small groups; descriptive, uncorrected for multiplicity, and intended to")
    print("  motivate a mechanism rather than to test one.")

    OUT.write_text(json.dumps(results, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"\nwrote {OUT.relative_to(ROOT).as_posix()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
