"""Distributions and corrections, implemented rather than approximated.

The earlier version of the test script used a NORMAL tail for the paired-t p-value. At
n = 21..43 that is not the t distribution, and it reports p-values that are too small --
wrong in the anti-conservative direction, which is the direction that matters. This
module carries a real Student's t CDF via the regularized incomplete beta function, so
nothing depends on a large-sample hand-wave.

Also here:
  holm            family-wise correction for the pairwise verification tests, which are
                  a post-hoc family and must be labelled as one
  sign_test_exact assumption-free companion to Wilcoxon: Wilcoxon avoids normality but
                  still assumes the paired differences are symmetric, and the sign test
                  assumes neither
  bootstrap_ci    percentile CI resampling ROOTS, the unit of independence
"""

from __future__ import annotations

import math
import random


# ------------------------------------------------------- regularized incomplete beta


def _betacf(a: float, b: float, x: float, itmax: int = 300, eps: float = 3e-16) -> float:
    """Continued fraction for the incomplete beta, modified Lentz method."""
    qab, qap, qam = a + b, a + 1.0, a - 1.0
    c = 1.0
    d = 1.0 - qab * x / qap
    if abs(d) < 1e-300:
        d = 1e-300
    d = 1.0 / d
    h = d
    for m in range(1, itmax + 1):
        m2 = 2 * m
        aa = m * (b - m) * x / ((qam + m2) * (a + m2))
        d = 1.0 + aa * d
        if abs(d) < 1e-300:
            d = 1e-300
        c = 1.0 + aa / c
        if abs(c) < 1e-300:
            c = 1e-300
        d = 1.0 / d
        h *= d * c
        aa = -(a + m) * (qab + m) * x / ((a + m2) * (qap + m2))
        d = 1.0 + aa * d
        if abs(d) < 1e-300:
            d = 1e-300
        c = 1.0 + aa / c
        if abs(c) < 1e-300:
            c = 1e-300
        d = 1.0 / d
        delta = d * c
        h *= delta
        if abs(delta - 1.0) < eps:
            break
    return h


def betainc(a: float, b: float, x: float) -> float:
    """Regularized incomplete beta I_x(a, b)."""
    if x <= 0.0:
        return 0.0
    if x >= 1.0:
        return 1.0
    lbeta = (math.lgamma(a + b) - math.lgamma(a) - math.lgamma(b)
             + a * math.log(x) + b * math.log1p(-x))
    front = math.exp(lbeta)
    if x < (a + 1.0) / (a + b + 2.0):
        return front * _betacf(a, b, x) / a
    return 1.0 - math.exp(
        math.lgamma(a + b) - math.lgamma(a) - math.lgamma(b)
        + b * math.log1p(-x) + a * math.log(x)) * _betacf(b, a, 1.0 - x) / b


def t_sf_two_sided(t: float, df: int) -> float:
    """Two-sided Student's t tail. THE correct tail for a paired t at these n."""
    if df <= 0:
        return 1.0
    if not math.isfinite(t):
        return 0.0
    x = df / (df + t * t)
    return max(0.0, min(1.0, betainc(df / 2.0, 0.5, x)))


# --------------------------------------------------------------------- exact tests


def binom_two_sided(k: int, n: int, p: float = 0.5) -> float:
    """Exact two-sided binomial tail at p=0.5 (symmetric, so double the smaller side)."""
    if n == 0:
        return 1.0
    kk = min(k, n - k)
    tail = sum(math.comb(n, i) for i in range(kk + 1)) / (2 ** n)
    return min(1.0, 2 * tail)


def sign_test_exact(diffs: list[float]) -> tuple[int, int, float]:
    """(n_positive, n_nonzero, exact two-sided p). Assumes only that, under the null,
    a difference is equally likely to be positive or negative -- no symmetry, no
    normality."""
    nz = [d for d in diffs if d != 0.0]
    pos = sum(1 for d in nz if d > 0)
    return pos, len(nz), binom_two_sided(pos, len(nz))


# ------------------------------------------------------------------- corrections


def holm(pvalues: dict[str, float]) -> dict[str, float]:
    """Holm-Bonferroni. Returns adjusted p-values, monotone-enforced."""
    items = sorted(pvalues.items(), key=lambda kv: kv[1])
    m = len(items)
    out: dict[str, float] = {}
    running = 0.0
    for i, (key, p) in enumerate(items):
        adj = min(1.0, (m - i) * p)
        running = max(running, adj)
        out[key] = running
    return out


# -------------------------------------------------------------------- bootstrap


def bootstrap_ci(values: list[float], reps: int = 20000, alpha: float = 0.05,
                 seed: int = 20260828) -> tuple[float, float]:
    """Percentile CI over a resample of the ROOTS. Roots are the independent unit; the
    four arms within a root are paired observations of the same theorem."""
    if not values:
        return float("nan"), float("nan")
    rng = random.Random(seed)
    n = len(values)
    means = []
    for _ in range(reps):
        means.append(sum(values[rng.randrange(n)] for _ in range(n)) / n)
    means.sort()
    lo = means[int((alpha / 2) * reps)]
    hi = means[min(reps - 1, int((1 - alpha / 2) * reps))]
    return lo, hi
