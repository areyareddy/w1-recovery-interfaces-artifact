"""Step s19 -- Co-primary B, as registered: the guidance-by-artifact INTERACTION.

v7 `02` Sec.8 defines the confirmatory verification estimand and it is NOT C-A:

    G0 = mean(Y_B - Y_A)          guidance effect with no prior attempt
    G1 = mean(Y_D - Y_C)          guidance effect with the prior attempt
    I  = G1 - G0                  the registered co-primary

Equivalently, per root, I is the mean of

    d_i = (Y_D - Y_C) - (Y_B - Y_A)

which is why the CI here bootstraps over ROOTS: the four arms of a root are paired
observations of one theorem, and the theorem is the independent unit.

WHY THIS SCRIPT EXISTS. The first pass through these results reported C-A as the
headline. C-A is a real and striking effect, but it is a SECONDARY pairwise contrast, and
letting it stand in for the registered estimand would be exactly the substitution
pre-registration is meant to prevent. The interaction is reported here whatever it says.

The five pairwise verification contrasts are a post-hoc family and are Holm-corrected as
one, reported alongside the uncorrected values.
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

import receipts  # noqa: E402
import stats  # noqa: E402
import s17_statistical_tests as pair  # noqa: E402

DB = ROOT / "data/runs.sqlite"
OUT = ROOT / "audit/coprimary_interaction.json"

COHORTS = [("primary_eval", "eval-40 block 1 (PRE-REGISTERED)"),
           ("eval_block2", "eval-40 block 2 (replication)"),
           ("full_pool_dev", "dev-43 (descriptive)")]
PAIRWISE = [("C", "A"), ("D", "B"), ("B", "A"), ("D", "C"), ("E", "A")]


def per_root(con, cohort: str) -> dict[str, dict[str, int]]:
    rows = con.execute(
        "SELECT root_id, arm, verified FROM branches "
        "WHERE cohort=? AND status='done'", (cohort,))
    out: dict[str, dict[str, int]] = {}
    for root_id, arm, verified in rows:
        out.setdefault(root_id, {})[arm] = int(verified or 0)
    return out


def main() -> int:
    receipts.force_utf8()
    con = sqlite3.connect(f"file:{DB}?mode=ro", uri=True)
    results = {"interaction": [], "pairwise_family": []}

    print("=" * 78)
    print("CO-PRIMARY B (registered):  I = (D - C) - (B - A)")
    print("=" * 78)
    for cohort, label in COHORTS:
        roots = per_root(con, cohort)
        d = [(v["D"] - v["C"]) - (v["B"] - v["A"])
             for v in roots.values() if all(a in v for a in "ABCD")]
        if not d:
            continue
        I = statistics.mean(d)
        lo, hi = stats.bootstrap_ci(d)
        g0 = statistics.mean(v["B"] - v["A"] for v in roots.values()
                             if all(a in v for a in "AB"))
        g1 = statistics.mean(v["D"] - v["C"] for v in roots.values()
                             if all(a in v for a in "CD"))
        resolved = not (lo <= 0.0 <= hi)
        print(f"\n  {label}")
        print(f"    n roots {len(d):3d}   G0 = {g0:+.4f}   G1 = {g1:+.4f}")
        print(f"    I = {I:+.4f}   root-bootstrap 95% CI [{lo:+.4f}, {hi:+.4f}]")
        print(f"    -> {'RESOLVED' if resolved else 'UNRESOLVED (CI contains 0)'}")
        results["interaction"].append(
            {"cohort": cohort, "n_roots": len(d), "G0": round(g0, 6),
             "G1": round(g1, 6), "I": round(I, 6),
             "ci95_lo": round(lo, 6), "ci95_hi": round(hi, 6),
             "resolved": resolved})

    print("\n" + "=" * 78)
    print("SECONDARY pairwise family -- exact McNemar, Holm-corrected as one family")
    print("=" * 78)
    for cohort, label in COHORTS:
        raw: dict[str, float] = {}
        detail: dict[str, tuple] = {}
        for x, y in PAIRWISE:
            rows = list(con.execute(
                "SELECT max(CASE WHEN arm=? THEN verified END), "
                "       max(CASE WHEN arm=? THEN verified END) "
                "FROM branches WHERE cohort=? AND status='done' AND arm IN (?,?) "
                "GROUP BY root_id HAVING count(*)=2", (x, y, cohort, x, y)))
            if not rows:
                continue
            b = sum(1 for a, bb in rows if a == 1 and bb == 0)
            c = sum(1 for a, bb in rows if a == 0 and bb == 1)
            key = f"{x}-{y}"
            raw[key] = pair.mcnemar_exact(b, c)
            detail[key] = (len(rows), b, c)
        adj = stats.holm(raw)
        print(f"\n  {label}")
        for key in sorted(raw, key=lambda k: raw[k]):
            n, b, c = detail[key]
            s_raw = "*" if raw[key] < 0.05 else " "
            s_adj = "*" if adj[key] < 0.05 else " "
            print(f"    {key:5} n={n:3d}  {b:2d} vs {c:2d}   "
                  f"p={raw[key]:.4f}{s_raw}   Holm={adj[key]:.4f}{s_adj}")
            results["pairwise_family"].append(
                {"cohort": cohort, "contrast": key, "n_pairs": n,
                 "x_only": b, "y_only": c,
                 "p_exact": round(raw[key], 6), "p_holm": round(adj[key], 6),
                 "significant_raw": raw[key] < 0.05,
                 "significant_holm": adj[key] < 0.05})
    con.close()

    OUT.write_text(json.dumps(results, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print("\n" + "=" * 78)
    print("How this must be written up")
    print("=" * 78)
    print("  The registered co-primary is the interaction. Report it whatever it says.")
    print("  C-A is secondary, and after Holm correction within its family the two")
    print("  seed blocks do not agree on significance -- say so rather than quoting the")
    print("  uncorrected value alone.")
    print(f"\nwrote {OUT.relative_to(ROOT).as_posix()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
