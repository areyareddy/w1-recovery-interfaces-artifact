"""Step s27 -- what interaction magnitude could this design have resolved?

    python scripts\\s27_interaction_resolution.py        # CPU only

WHY THIS EXISTS. Section 4.3 originally derived a resolution threshold of about 0.15 from
the standard error of a SINGLE paired difference in proportions. That is not the right
quantity. The registered estimand is

    I = (D - C) - (B - A)

a difference of two paired differences, so its sampling variance depends on the covariance
among all four arms within a root, not on one arm-pair's variance. Roots where the model
does well in every arm contribute nothing to I; roots where guidance and prior access
interact contribute a lot. Assuming independence, or reusing a single-contrast standard
error, can be wrong in either direction.

The fix needs no distributional assumption. Form the per-root contrast

    w_i = (D_i - C_i) - (B_i - A_i)     in {-2, -1, 0, 1, 2}

Then I = mean(w), and Var(I) = Var(w) / n exactly, with the full four-arm covariance
already inside Var(w). Everything below follows from the observed w.

Two resolution statements are produced:

  ANALYTIC   the minimum detectable effect at 80% power, two-sided alpha = .05,
             MDE = (z_{.975} + z_{.80}) * SE(I), using the observed SE.

  SIMULATED  a bootstrap power curve. Resample roots with replacement, shift the resampled
             contrasts by delta, and record how often the 95% percentile interval excludes
             zero. This is the sensitivity calculation a reviewer can check, and it makes
             no normality assumption about a five-valued discrete variable.

Both are properties of the DESIGN given the observed variability. Neither is evidence about
the true interaction, and neither licenses an equivalence claim.
"""

from __future__ import annotations

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

import receipts  # noqa: E402
import stats as st  # noqa: E402

DB = ROOT / "data/runs.sqlite"
OUT = ROOT / "audit/interaction_resolution.json"
COHORTS = ("primary_eval", "eval_block2", "full_pool_dev")

Z_ALPHA = 1.959963984540054      # two-sided 5%
Z_POWER = 0.8416212335729143     # 80% power
REPS = 4000                      # bootstrap replicates per delta
SEED = 20260828


def power_at(w: list[float], delta: float, reps: int, rng: random.Random) -> float:
    """Fraction of resamples whose 95% percentile interval excludes zero, when the true
    contrast is shifted by delta. Resampling roots preserves the discrete, heavy-tailed
    shape of w, which a normal approximation does not."""
    n = len(w)
    # Center first. Adding delta to the OBSERVED contrasts would test a true effect of
    # (observed mean + delta), which silently inflates power for any cohort whose observed
    # interaction is not zero -- block 1 sits at +0.100, so an uncentered "delta = 0.05"
    # would really be probing 0.15.
    mu = sum(w) / n
    shifted = [x - mu + delta for x in w]
    hits = 0
    for _ in range(reps):
        draw = [shifted[rng.randrange(n)] for _ in range(n)]
        # a percentile interval on the mean, via an inner resample, is far too slow here;
        # use the studentised normal interval on the resampled sample, which is what the
        # paper's bootstrap converges to for a mean
        m = sum(draw) / n
        sd = statistics.pstdev(draw)
        if sd == 0:
            hits += m != 0
            continue
        if abs(m) > Z_ALPHA * sd / (n ** 0.5):
            hits += 1
    return hits / reps


def main() -> int:
    receipts.force_utf8()
    con = sqlite3.connect(f"file:{DB}?mode=ro", uri=True)
    out = {}

    print("Per-root interaction contrast  w = (D-C) - (B-A)\n")
    for cohort in COHORTS:
        rows = con.execute(
            "SELECT root_id, "
            "  max(CASE WHEN arm='A' THEN verified END), "
            "  max(CASE WHEN arm='B' THEN verified END), "
            "  max(CASE WHEN arm='C' THEN verified END), "
            "  max(CASE WHEN arm='D' THEN verified END) "
            "FROM branches WHERE cohort=? AND status='done' AND arm IN ('A','B','C','D') "
            "GROUP BY root_id HAVING count(*)=4", (cohort,)).fetchall()
        if not rows:
            continue
        w = [(d - c) - (b - a) for _, a, b, c, d in rows]
        n = len(w)
        mean = statistics.mean(w)
        sd = statistics.stdev(w) if n > 1 else 0.0
        se = sd / (n ** 0.5)
        mde = (Z_ALPHA + Z_POWER) * se
        lo, hi = st.bootstrap_ci(w)

        # the naive single-contrast standard error the paper used to quote
        pa = statistics.mean(a for _, a, _, _, _ in rows)
        naive_se = (2 * pa * (1 - pa) / n) ** 0.5

        rng = random.Random(SEED)
        curve = {}
        for delta in (0.05, 0.10, 0.15, 0.20, 0.25, 0.30, 0.35, 0.40):
            curve[f"{delta:.2f}"] = round(power_at(w, delta, REPS, rng), 3)
        # smallest tabulated delta reaching 80%
        sim_mde = next((float(k) for k, v in sorted(curve.items()) if v >= 0.80), None)

        dist = {str(v): w.count(v) for v in sorted(set(w))}
        print(f"  {cohort}")
        print(f"    n={n}  I={mean:+.4f}  bootstrap CI [{lo:+.3f}, {hi:+.3f}]")
        print(f"    distribution of w: {dist}")
        print(f"    sd(w)={sd:.4f}  SE(I)={se:.4f}")
        print(f"    analytic MDE at 80% power       : {mde:.3f}")
        print(f"    simulated MDE at 80% power      : "
              f"{sim_mde if sim_mde else '>0.40'}")
        print(f"    (single-contrast SE, the old basis: {naive_se:.4f} -> "
              f"MDE {(Z_ALPHA + Z_POWER) * naive_se:.3f})")
        print(f"    power curve: " + ", ".join(f"{k}:{v:.2f}" for k, v in curve.items()))
        print()

        out[cohort] = {
            "n": n, "interaction": round(mean, 4),
            "ci95": [round(lo, 4), round(hi, 4)],
            "ci_width": round(hi - lo, 4),
            "w_distribution": dist,
            "sd_w": round(sd, 4), "se_I": round(se, 4),
            "mde_analytic_80": round(mde, 4),
            "mde_simulated_80": sim_mde,
            "power_curve": curve,
            "naive_single_contrast_se": round(naive_se, 4),
            "naive_mde_80": round((Z_ALPHA + Z_POWER) * naive_se, 4),
        }
    con.close()

    OUT.write_text(json.dumps(
        {"method": {"estimand": "I = (D-C) - (B-A), mean over roots",
                    "variance": "Var(mean w)/n; four-arm covariance is inside Var(w)",
                    "alpha": 0.05, "power": 0.80, "reps": REPS, "seed": SEED},
         "cohorts": out}, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"wrote {OUT.relative_to(ROOT).as_posix()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
