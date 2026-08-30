"""Step s20 -- the analyses the W1 reviewer asked for. CPU only, existing data.

Five items, none of which need new generation:

  1  DISCORDANT-ROOT OVERLAP between seed blocks. The headline secondary result is
     0-vs-7 and 0-vs-8. If those are largely the same theorems, the result rests on far
     fewer unique roots than 15 events suggests, and the paper must say so.

  2  ANCHORING -> VERIFICATION within arm C. The two endpoints are currently adjacent
     facts. Does root-level similarity predict Lean failure? Do the discordant roots sit
     at high similarity? A null here is itself important: it separates "retention causes
     harm" from "retention and harm co-occur".

  3  ABSOLUTE per-arm similarity, not just differences.

  4  NEAR-VERBATIM fraction: how often is arm C essentially reproducing the failed
     attempt rather than being influenced by it?

  5  TRUNCATION ATTRIBUTION: how much of the C verification loss is explained by C
     branches that never reached the verifier at all?
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
import stats as st  # noqa: E402

DB = ROOT / "data/runs.sqlite"
ANCHOR = ROOT / "audit/anchoring_results.csv"
OUT = ROOT / "audit/reviewer_analyses.json"
NEAR_VERBATIM = 0.90


def main() -> int:
    receipts.force_utf8()
    con = sqlite3.connect(f"file:{DB}?mode=ro", uri=True)
    anchor: dict[tuple[str, str], dict[str, float]] = {}
    for r in csv.DictReader(ANCHOR.open(encoding="utf-8")):
        anchor.setdefault((r["cohort"], r["root_id"]), {})[r["arm"]] = \
            float(r["anchoring_S"])
    out: dict = {}

    # ---------------------------------------------------------------- 1. overlap
    print("=" * 76)
    print("1. DISCORDANT-ROOT OVERLAP between the two seed blocks (C vs A)")
    print("=" * 76)
    disc = {}
    for cohort in ("primary_eval", "eval_block2"):
        rows = list(con.execute(
            "SELECT root_id, max(CASE WHEN arm='C' THEN verified END), "
            "       max(CASE WHEN arm='A' THEN verified END) "
            "FROM branches WHERE cohort=? AND status='done' AND arm IN ('A','C') "
            "GROUP BY root_id HAVING count(*)=2", (cohort,)))
        disc[cohort] = {"a_only": {r for r, cv, av in rows if av == 1 and cv == 0},
                        "c_only": {r for r, cv, av in rows if cv == 1 and av == 0}}
        print(f"  {cohort:14} A-only {len(disc[cohort]['a_only'])}, "
              f"C-only {len(disc[cohort]['c_only'])}")
    b1, b2 = disc["primary_eval"]["a_only"], disc["eval_block2"]["a_only"]
    shared = b1 & b2
    union = b1 | b2
    print(f"\n  block-1 A-only roots : {sorted(b1)}")
    print(f"  block-2 A-only roots : {sorted(b2)}")
    print(f"\n  shared by both blocks: {len(shared)}  {sorted(shared)}")
    print(f"  UNIQUE roots involved: {len(union)}  (from {len(b1) + len(b2)} events)")
    print(f"\n  => the secondary result rests on {len(union)} unique theorems, of which "
          f"{len(shared)} discordant in both blocks.")
    out["discordant_overlap"] = {
        "block1_a_only": sorted(b1), "block2_a_only": sorted(b2),
        "shared": sorted(shared), "n_unique_roots": len(union),
        "n_events": len(b1) + len(b2)}

    # ------------------------------------------------- 2. anchoring -> verification
    print("\n" + "=" * 76)
    print("2. Does anchoring predict verification failure WITHIN arm C?")
    print("=" * 76)
    link = []
    for cohort in ("primary_eval", "eval_block2"):
        rows = list(con.execute(
            "SELECT root_id, verified FROM branches WHERE cohort=? AND arm='C' "
            "AND status='done'", (cohort,)))
        ok = [anchor[(cohort, r)]["C"] for r, v in rows
              if v == 1 and (cohort, r) in anchor]
        bad = [anchor[(cohort, r)]["C"] for r, v in rows
               if v == 0 and (cohort, r) in anchor]
        # is S higher on the roots where A rescued and C did not?
        d = disc[cohort]["a_only"]
        s_disc = [anchor[(cohort, r)]["C"] for r in d if (cohort, r) in anchor]
        s_rest = [anchor[(cohort, r)]["C"] for r, v in rows
                  if r not in d and (cohort, r) in anchor]
        print(f"\n  {cohort}")
        print(f"    S(C) | C verified        n={len(ok):2d}  "
              f"mean {statistics.mean(ok):.3f}" if ok else
              f"    S(C) | C verified        n=0")
        print(f"    S(C) | C failed          n={len(bad):2d}  "
              f"mean {statistics.mean(bad):.3f}")
        print(f"    S(C) | A-only discordant n={len(s_disc):2d}  "
              f"mean {statistics.mean(s_disc):.3f}")
        print(f"    S(C) | all other roots   n={len(s_rest):2d}  "
              f"mean {statistics.mean(s_rest):.3f}")
        diff = statistics.mean(s_disc) - statistics.mean(s_rest)
        print(f"    difference (discordant - rest): {diff:+.3f}")
        link.append({"cohort": cohort, "n_verified": len(ok),
                     "mean_S_verified": round(statistics.mean(ok), 4) if ok else None,
                     "mean_S_failed": round(statistics.mean(bad), 4),
                     "n_discordant": len(s_disc),
                     "mean_S_discordant": round(statistics.mean(s_disc), 4),
                     "mean_S_other": round(statistics.mean(s_rest), 4),
                     "difference": round(diff, 4)})
    out["anchoring_vs_verification"] = link
    print("\n  A near-zero difference means anchoring MAGNITUDE does not select the roots")
    print("  where the prior attempt costs a rescue. That is a real finding, and it")
    print("  argues against 'more copying -> more harm' as the mechanism.")

    # ------------------------------------------------------ 3. absolute similarity
    print("\n" + "=" * 76)
    print("3. ABSOLUTE per-arm similarity to the prior attempt")
    print("=" * 76)
    abs_s = []
    for cohort in ("primary_eval", "eval_block2", "full_pool_dev"):
        vals = {}
        for arm in "ABCDE":
            xs = [v[arm] for (co, _), v in anchor.items() if co == cohort and arm in v]
            if xs:
                vals[arm] = (len(xs), statistics.mean(xs), statistics.median(xs))
        print(f"\n  {cohort}")
        for arm, (n, m, md) in vals.items():
            print(f"    S(x_{arm}, prior)  n={n:3d}  mean {m:.4f}  median {md:.4f}")
        abs_s.append({"cohort": cohort,
                      **{f"mean_S_{a}": round(v[1], 4) for a, v in vals.items()},
                      **{f"median_S_{a}": round(v[2], 4) for a, v in vals.items()}})
    out["absolute_similarity"] = abs_s

    # --------------------------------------------------------- 4. near-verbatim
    print("\n" + "=" * 76)
    print(f"4. NEAR-VERBATIM reproduction (S >= {NEAR_VERBATIM})")
    print("=" * 76)
    nv = []
    for cohort in ("primary_eval", "eval_block2", "full_pool_dev"):
        for arm in ("A", "C"):
            xs = [v[arm] for (co, _), v in anchor.items() if co == cohort and arm in v]
            if not xs:
                continue
            k = sum(1 for x in xs if x >= NEAR_VERBATIM)
            print(f"  {cohort:14} arm {arm}: {k}/{len(xs)} "
                  f"({100 * k / len(xs):.1f}%)  max S {max(xs):.3f}")
            nv.append({"cohort": cohort, "arm": arm, "n": len(xs), "near_verbatim": k,
                       "max_S": round(max(xs), 4)})
    out["near_verbatim"] = {"threshold": NEAR_VERBATIM, "rows": nv}

    # ------------------------------------------------- 5. truncation attribution
    print("\n" + "=" * 76)
    print("5. How much of the C loss is C branches never reaching the verifier?")
    print("=" * 76)
    trunc = []
    for cohort in ("primary_eval", "eval_block2"):
        d = disc[cohort]["a_only"]
        rows = list(con.execute(
            "SELECT root_id, outcome_state FROM branches WHERE cohort=? AND arm='C' "
            "AND status='done'", (cohort,)))
        state = dict(rows)
        t = sum(1 for r in d if state.get(r) == "truncated")
        print(f"  {cohort:14} of {len(d)} roots A rescued and C did not, "
              f"{t} had C truncated before Lean ({100 * t / len(d):.0f}%)")
        trunc.append({"cohort": cohort, "a_only": len(d), "c_truncated": t})
    out["truncation_attribution"] = trunc
    con.close()

    OUT.write_text(json.dumps(out, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"\nwrote {OUT.relative_to(ROOT).as_posix()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
