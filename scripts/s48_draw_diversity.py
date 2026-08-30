"""Step s48 -- does a second draw buy new theorems, and does prior access cost that?

CPU ONLY. NO NEW GENERATION. This is a post-hoc reanalysis of data already registered,
already generated and already reported elsewhere in the paper.

THE QUESTION. Section 6 asserts that "access to a rejected completion can reduce the
diversity benefit of fresh sampling", citing Brown et al. The study never measured it,
and a reviewer correctly flagged that with one draw per arm per root it could not.

But there are two draws per arm per root: the two seed blocks are the same 40 theorems
under different seeds at the same full 12,288-token budget. Their union is therefore
pass@2, and the gain from block 1 to the union is exactly "what a second independent
draw buys", per arm. That quantity has never been computed.

WHAT THIS IS NOT.
  * Not new evidence about theorems. Both blocks are the same 40 roots, so this
    sharpens the sampling axis and does nothing for theorem-level generalization.
  * Not confirmatory. The registered endpoints are fixed in the frozen spec and pass@2
    is not among them. Every quantity here is EXPLORATORY and must be labelled so in
    the paper, under the same registration-tier rule that governs the restart arms.
  * Not a new test family. The A-vs-C contrast below is reported with its exact
    McNemar p-value UNADJUSTED and enters no Holm family, because adding a post-hoc
    estimand to a pre-specified family would change the correction applied to the
    registered tests.

The allocation section is a straight read of audit/allocation_analysis.json, which was
produced under spec/ALLOCATION_SPEC.md, frozen before generation. Those numbers are
confirmatory ON THEIR OWN endpoint (Holm family {Split-2 - Long, Split-3 - Long}); this
script copies them, it does not recompute or reinterpret them.
"""

from __future__ import annotations

import json
import math
import sqlite3
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT / "src"))

import stats as st  # noqa: E402

DB = ROOT / "data/runs.sqlite"
ALLOC = ROOT / "audit/allocation_analysis.json"
OUT = ROOT / "audit/draw_diversity.json"

BLOCKS = ("primary_eval", "eval_block2")
ARMS = ("A", "B", "C", "D")


def mcnemar_exact(b: int, c: int) -> float:
    """Two-sided exact McNemar. Identical to scripts/s17_statistical_tests.py."""
    n = b + c
    if n == 0:
        return 1.0
    k = min(b, c)
    tail = sum(math.comb(n, i) for i in range(k + 1)) / (2 ** n)
    return min(1.0, 2 * tail)


def verified_sets(con):
    """{arm: {block: set of verified root_id}} plus the root universe per block."""
    out: dict = {}
    universe: dict = {}
    for cohort in BLOCKS:
        for arm in ARMS:
            rows = list(con.execute(
                "SELECT root_id, verified, status FROM branches "
                "WHERE cohort=? AND arm=?", (cohort, arm)))
            assert rows, f"no rows for {cohort}/{arm}"
            incomplete = [r[0] for r in rows if r[2] != "done"]
            assert not incomplete, f"{cohort}/{arm} incomplete: {incomplete[:3]}"
            universe.setdefault(cohort, set()).update(r[0] for r in rows)
            out.setdefault(arm, {})[cohort] = {r[0] for r in rows if r[1] == 1}
    return out, universe


def main() -> int:
    try:
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    except (AttributeError, ValueError):
        pass

    con = sqlite3.connect(f"file:{DB}?mode=ro", uri=True)
    ver, universe = verified_sets(con)
    con.close()

    # ---- gate: the two blocks must be the SAME theorems, or "union" means nothing ----
    b1, b2 = universe[BLOCKS[0]], universe[BLOCKS[1]]
    assert b1 == b2, ("seed blocks do not share a root set; pass@2 as a union is "
                      f"undefined. only in block1: {sorted(b1 - b2)[:3]} "
                      f"only in block2: {sorted(b2 - b1)[:3]}")
    roots = sorted(b1)
    n = len(roots)
    assert n == 40, f"expected 40 eval roots, found {n}"
    print(f"[gate] both seed blocks cover the same {n} theorems -- union is well defined")

    res: dict = {
        "n_roots": n,
        "tier": "exploratory",
        "registered": False,
        "new_generation": False,
        "note": ("pass@2 is the union of the two seed blocks: two draws at the same "
                 "full budget on the same 40 theorems. Sampling diversity only; the "
                 "theorem set is unchanged, so this does not widen external validity."),
        "per_arm": {},
    }

    for arm in ARMS:
        s1, s2 = ver[arm][BLOCKS[0]], ver[arm][BLOCKS[1]]
        union = s1 | s2
        res["per_arm"][arm] = {
            "block1": len(s1),
            "block2": len(s2),
            "pass_at_2": len(union),
            "both_blocks": len(s1 & s2),
            "new_from_block2": len(s2 - s1),
            "new_from_block1": len(s1 - s2),
            "gain_over_block1": len(union) - len(s1),
            "gain_over_best_block": len(union) - max(len(s1), len(s2)),
            "union_roots": sorted(union),
        }
        print(f"  arm {arm}: {len(s1)}/{n} and {len(s2)}/{n} -> pass@2 {len(union)}/{n} "
              f"(+{len(union) - len(s1)} over block 1)")

    # ---- the contrast the diversity claim is actually about: A vs C at pass@2 --------
    # Paired within root. Exploratory, unadjusted, in no Holm family.
    contrasts = []
    for x, y in (("A", "C"), ("A", "B"), ("B", "D"), ("C", "D")):
        ux = set(res["per_arm"][x]["union_roots"])
        uy = set(res["per_arm"][y]["union_roots"])
        x_only = len(ux - uy)
        y_only = len(uy - ux)
        diffs = [(1.0 if r in ux else 0.0) - (1.0 if r in uy else 0.0) for r in roots]
        lo, hi = st.bootstrap_ci(diffs)
        contrasts.append({
            "contrast": f"{x}-{y}",
            "basis": "pass@2 (union of the two seed blocks)",
            "n": n,
            "x_verified": len(ux),
            "y_verified": len(uy),
            "x_only": x_only,
            "y_only": y_only,
            "both": len(ux & uy),
            "effect": round(sum(diffs) / n, 4),
            "ci95": [round(lo, 4), round(hi, 4)],
            "p_exact_mcnemar": round(mcnemar_exact(x_only, y_only), 6),
            "holm_family": None,
            "tier": "exploratory",
        })
        c = contrasts[-1]
        print(f"  {c['contrast']} at pass@2: {c['x_verified']}/{n} vs "
              f"{c['y_verified']}/{n}  discordant {x_only}/{y_only}  "
              f"p={c['p_exact_mcnemar']:.4f}")
    res["contrasts"] = contrasts

    # ---- the second-draw yield, stated as the diversity quantity --------------------
    res["second_draw_gain"] = {
        arm: res["per_arm"][arm]["gain_over_block1"] for arm in ARMS
    }

    # ---- allocation policies: copied from the frozen-spec analysis, not recomputed ---
    if ALLOC.exists():
        a = json.loads(ALLOC.read_text(encoding="utf-8"))["eval"]
        cp = a["cross_policy"]
        res["allocation"] = {
            "source": "audit/allocation_analysis.json",
            "spec": "spec/ALLOCATION_SPEC.md",
            "confirmatory": a.get("confirmatory"),
            "budget_tokens": 12288,
            "verified_roots": {
                "long": a["accounting"]["full_budget"]["long"]["verified_roots"],
                "split2": a["accounting"]["full_budget"]["split2"]["verified_roots"],
                "split3": a["accounting"]["full_budget"]["split3"]["verified_roots"],
            },
            "union_any_policy": cp["roots_verified_by_any"],
            "all_three": cp["roots_verified_by_all_three"],
            "unique": cp["roots_verified_by_exactly_one"],
            "contrasts": a["contrasts"],
        }
        v = res["allocation"]["verified_roots"]
        print(f"  allocation (registered): long {v['long']}/{n}  "
              f"split2 {v['split2']}/{n}  split3 {v['split3']}/{n}  "
              f"union {cp['roots_verified_by_any']}/{n}")
    else:
        print("  note: audit/allocation_analysis.json absent -- allocation block omitted")

    OUT.write_text(json.dumps(res, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"\nwrote {OUT.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
