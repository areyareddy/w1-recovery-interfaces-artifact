"""Step s17 -- the tests behind the W1 headline numbers. CPU only; no GPU, no server.

Two families, because the two co-primaries are different kinds of measurement.

VERIFICATION is a paired BINARY outcome per root, so the test is McNemar's, computed
EXACTLY (binomial on the discordant pairs) rather than with the chi-square approximation.
The approximation is unreliable at these counts -- one cell is zero in both seed blocks --
and an exact test costs nothing here.

  Only the DISCORDANT pairs carry information. If arm C and arm A both verify a root, or
  both fail it, that root says nothing about which arm is better. With b = C-only and
  c = A-only, the null is b ~ Binomial(b + c, 0.5).

ANCHORING is a paired CONTINUOUS difference per root, so: Wilcoxon signed-rank (no
normality assumption) reported alongside the paired t-statistic. Where they agree, the
result is not an artifact of either test's assumptions.

Both seed blocks are reported separately and never pooled. Block 2 is a REPLICATION -- an
independent draw on the same 40 roots -- so the question it answers is "does the sign and
rough magnitude hold", not "can we get a tighter interval by combining".

The dev-43 cohort is descriptive: a different, development-split root set, reported for
generalization rather than confirmation.
"""

from __future__ import annotations

import csv
import json
import math
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
OUT = ROOT / "audit/statistical_tests.json"


# ----------------------------------------------------------------- exact McNemar


def mcnemar_exact(b: int, c: int) -> float:
    """Two-sided exact McNemar p-value. b and c are the discordant counts.

    Under the null each discordant pair is a fair coin, so the p-value is the two-sided
    binomial tail. With b=0 this reduces to 2 * 0.5^c, capped at 1."""
    n = b + c
    if n == 0:
        return 1.0
    k = min(b, c)
    tail = sum(math.comb(n, i) for i in range(k + 1)) / (2 ** n)
    return min(1.0, 2 * tail)


# ------------------------------------------------------- Wilcoxon signed-rank


def wilcoxon(diffs: list[float]) -> tuple[float, float, int]:
    """Returns (W, two-sided p by normal approximation with tie and continuity
    correction, n_nonzero). Zero differences are dropped, which is the standard
    (Wilcoxon) handling and is conservative here."""
    nz = [d for d in diffs if d != 0.0]
    n = len(nz)
    if n == 0:
        return 0.0, 1.0, 0
    order = sorted(range(n), key=lambda i: abs(nz[i]))
    ranks = [0.0] * n
    i = 0
    tie_correction = 0.0
    while i < n:
        j = i
        while j + 1 < n and abs(nz[order[j + 1]]) == abs(nz[order[i]]):
            j += 1
        avg = (i + j + 2) / 2.0          # average of 1-based ranks i+1..j+1
        for k in range(i, j + 1):
            ranks[order[k]] = avg
        t = j - i + 1
        if t > 1:
            tie_correction += t ** 3 - t
        i = j + 1

    w_plus = sum(r for d, r in zip(nz, ranks) if d > 0)
    w_minus = sum(r for d, r in zip(nz, ranks) if d < 0)
    w = min(w_plus, w_minus)
    mean = n * (n + 1) / 4.0
    var = n * (n + 1) * (2 * n + 1) / 24.0 - tie_correction / 48.0
    if var <= 0:
        return w, 1.0, n
    z = (w - mean + 0.5) / math.sqrt(var)      # continuity correction
    p = 2 * 0.5 * math.erfc(abs(z) / math.sqrt(2))
    return w, min(1.0, p), n


def paired_t(diffs: list[float]) -> tuple[float, float]:
    """Paired t with a REAL Student's t tail (df = n - 1).

    An earlier version used a normal tail here. At n = 21..43 that is not the t
    distribution and it under-reports p -- wrong in the anti-conservative direction,
    which is the direction that matters. src/stats.py carries the t CDF via the
    regularized incomplete beta so nothing rests on a large-sample hand-wave."""
    n = len(diffs)
    if n < 2:
        return 0.0, 1.0
    m = statistics.mean(diffs)
    sd = statistics.stdev(diffs)
    if sd == 0:
        return (math.inf if m else 0.0), (0.0 if m else 1.0)
    t = m / (sd / math.sqrt(n))
    return t, st.t_sf_two_sided(t, n - 1)


# ------------------------------------------------------------------------ main


def main() -> int:
    receipts.force_utf8()
    con = sqlite3.connect(f"file:{DB}?mode=ro", uri=True)

    cohorts = [("primary_eval", "eval-40 block 1 (PRE-REGISTERED)"),
               ("eval_block2", "eval-40 block 2 (replication)"),
               ("full_pool_dev", "dev-43 (descriptive)")]
    contrasts = [("C", "A", "artifact, no guidance"),
                 ("D", "B", "artifact, with guidance"),
                 ("B", "A", "guidance, no artifact"),
                 ("D", "C", "guidance, with artifact"),
                 ("E", "A", "native interface (confounded: artifact+feedback+structure)")]

    results = {"verification": [], "anchoring": []}

    print("=" * 78)
    print("VERIFICATION -- exact McNemar on paired binary outcomes")
    print("=" * 78)
    for cohort, label in cohorts:
        print(f"\n{label}")
        for x, y, why in contrasts:
            rows = list(con.execute(
                "SELECT max(CASE WHEN arm=? THEN verified END), "
                "       max(CASE WHEN arm=? THEN verified END) "
                "FROM branches WHERE cohort=? AND status='done' AND arm IN (?,?) "
                "GROUP BY root_id HAVING count(*)=2", (x, y, cohort, x, y)))
            if not rows:
                continue
            b = sum(1 for a, bb in rows if a == 1 and bb == 0)   # x only
            c = sum(1 for a, bb in rows if a == 0 and bb == 1)   # y only
            both = sum(1 for a, bb in rows if a == 1 and bb == 1)
            neither = len(rows) - b - c - both
            p = mcnemar_exact(b, c)
            star = "*" if p < 0.05 else " "
            print(f"  {x}-{y}  n={len(rows):3d}  {x}only={b:2d} {y}only={c:2d} "
                  f"both={both:2d} neither={neither:2d}   p={p:.4f}{star}   {why}")
            results["verification"].append(
                {"cohort": cohort, "contrast": f"{x}-{y}", "n_pairs": len(rows),
                 "x_only": b, "y_only": c, "both": both, "neither": neither,
                 "discordant": b + c, "p_exact_mcnemar": round(p, 6),
                 "direction": f"{y} better" if c > b else (f"{x} better" if b > c else "tie"),
                 "note": why})

    print("\n" + "=" * 78)
    print("ANCHORING -- paired t (Student), asymptotic Wilcoxon signed-rank,")
    print("            and exact sign test on S differences")
    print("=" * 78)
    if not ANCHOR.exists():
        print("  audit/anchoring_results.csv not found; run s14 first")
    else:
        rows = list(csv.DictReader(ANCHOR.open(encoding="utf-8")))
        by: dict[tuple[str, str], dict[str, float]] = {}
        for r in rows:
            by.setdefault((r["cohort"], r["root_id"]), {})[r["arm"]] = float(r["anchoring_S"])
        for cohort, label in cohorts:
            print(f"\n{label}")
            for x, y, why in (("C", "A", "T0"), ("D", "B", "T1"), ("E", "A", "E-A")):
                pairs = [(v[x], v[y]) for (co, _), v in by.items()
                         if co == cohort and x in v and y in v]
                if not pairs:
                    continue
                diffs = [a - b for a, b in pairs]
                w, pw, nz = wilcoxon(diffs)
                t, pt = paired_t(diffs)
                m = statistics.mean(diffs)
                sd = statistics.stdev(diffs) if len(diffs) > 1 else 0.0
                se = sd / math.sqrt(len(diffs)) if diffs else 0.0
                pos, nzz, p_sign = st.sign_test_exact(diffs)
                print(f"  {why:4} {x}-{y}  n={len(diffs):3d}  mean={m:+.4f} "
                      f"(se {se:.4f})  t={t:+.2f} p={pt:.2e}  "
                      f"W={w:.0f} p_asym={pw:.2e}  sign {pos}/{nzz} p={p_sign:.2e}")
                results["anchoring"].append(
                    {"cohort": cohort, "contrast": f"{x}-{y}", "label": why,
                     "n": len(diffs), "mean_diff": round(m, 6), "se": round(se, 6),
                     "t": round(t, 4), "df": len(diffs) - 1, "p_paired_t_student": pt,
                     "wilcoxon_W": w, "p_wilcoxon_asymptotic": pw,
                     "n_positive": pos, "n_nonzero": nzz,
                     "p_sign_test_exact": p_sign})
    con.close()

    OUT.write_text(json.dumps(results, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(chr(10) + "NOTE: these pairwise verification tests are SECONDARY.")
    print("The registered co-primary is the guidance-by-artifact INTERACTION")
    print("  I = (D - C) - (B - A)   --  scripts/s19_coprimary_interaction.py")
    print("Do not let a pairwise contrast stand in for it.")
    print(chr(10) + "Block 2 is a REPLICATION, not extra n: the same 40 roots under a")
    print("second seed. Never pool the blocks to tighten a pre-registered interval.")
    print(f"\nwrote {OUT.relative_to(ROOT).as_posix()}")
    print(chr(10) + "Reminder: block 2 is a replication, not extra n. Never pool it")
    print("with block 1 to tighten an interval on a pre-registered contrast.")
    print(chr(10) + "These pairwise verification tests are SECONDARY. The registered")
    print("co-primary is the interaction (D-C)-(B-A): scripts/s19_coprimary_interaction.py")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
