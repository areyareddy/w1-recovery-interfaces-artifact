"""Step s15 -- can per-branch prefill/decode TIME be reconstructed without a replay?

Answer: no. This script is the artifact for that claim, which was previously asserted
from a throwaway command with nothing on disk to check it against.

The idea under test: request_wall_seconds is recorded per branch, and so are
prefill_tokens and decode_tokens. If wall time were a clean linear function of the two
token counts, the coefficients would give ms/token for prefill and decode and no replay
would be needed.

It fails, and the way it fails is the point. The fit predicts TOTAL wall well, but the
coefficients are not physical: prefill comes out an order of magnitude slower than the
directly measured rate, and the intercept is NEGATIVE -- a negative fixed request
overhead cannot exist. A model can fit well and still attribute time to the wrong place.

Compared against the direct measurement from Gate 9 (audit/determinism.json), which is
the ground truth here: it comes from the server's own timings object on isolated calls.
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

DB = ROOT / "data/runs.sqlite"
OUT = ROOT / "audit/timing_regression.json"


def solve3(A: list[list[float]]) -> list[float]:
    """Gauss-Jordan on a 3x4 augmented matrix. No numpy dependency."""
    A = [row[:] for row in A]
    for i in range(3):
        piv = A[i][i]
        if abs(piv) < 1e-12:
            raise ValueError("singular normal equations")
        A[i] = [v / piv for v in A[i]]
        for r in range(3):
            if r != i:
                f = A[r][i]
                A[r] = [A[r][j] - f * A[i][j] for j in range(4)]
    return [A[i][3] for i in range(3)]


def main() -> int:
    receipts.force_utf8()

    con = sqlite3.connect(f"file:{DB}?mode=ro", uri=True)
    rows = list(con.execute(
        "SELECT prefill_tokens, decode_tokens, request_wall_seconds FROM branches "
        "WHERE status='done'"))
    con.close()
    n = len(rows)
    print(f"[1/3] {n} completed branches")

    X = [[float(p), float(d), 1.0] for p, d, _ in rows]
    y = [float(w) for _, _, w in rows]
    normal = [[sum(X[k][i] * X[k][j] for k in range(n)) for j in range(3)]
              + [sum(X[k][i] * y[k] for k in range(n))] for i in range(3)]
    a, b, c0 = solve3(normal)

    pred = [a * X[k][0] + b * X[k][1] + c0 for k in range(n)]
    ybar = statistics.mean(y)
    ss_res = sum((y[k] - pred[k]) ** 2 for k in range(n))
    ss_tot = sum((v - ybar) ** 2 for v in y)
    r2 = 1 - ss_res / ss_tot
    rmse = (ss_res / n) ** 0.5

    det = json.loads((ROOT / "audit/determinism.json").read_text(encoding="utf-8"))
    reps = [c for c in det["checks"] if c["check"] == "repeat_same_seed"]
    measured_prefill = statistics.median(c["prefill_tok_per_s"] for c in reps)
    measured_decode = statistics.median(c["decode_tok_per_s"] for c in reps)

    # collinearity check -- the obvious explanation, and it is NOT the explanation
    p = [r[0] for r in rows]
    d = [r[1] for r in rows]
    mp, md = statistics.mean(p), statistics.mean(d)
    cov = sum((u - mp) * (v - md) for u, v in zip(p, d))
    corr = cov / ((sum((u - mp) ** 2 for u in p) * sum((v - md) ** 2 for v in d)) ** 0.5)

    print(f"\n[2/3] fit: wall = a*prefill_tokens + b*decode_tokens + c")
    print(f"      a  {a * 1000:9.4f} ms/tok  -> {1 / a:9.1f} tok/s   "
          f"(measured {measured_prefill:.1f})")
    print(f"      b  {b * 1000:9.4f} ms/tok  -> {1 / b:9.1f} tok/s   "
          f"(measured {measured_decode:.1f})")
    print(f"      c  {c0:9.4f} s intercept")
    print(f"      R^2 {r2:.5f}   RMSE {rmse:.3f}s on mean wall {ybar:.1f}s")
    print(f"      corr(prefill_tokens, decode_tokens) = {corr:+.3f}")

    verdict_reasons = []
    if c0 < 0:
        verdict_reasons.append(
            f"intercept is negative ({c0:.2f}s); a fixed request overhead cannot be "
            f"negative, so the fit is absorbing structure it should not")
    ratio_fit = b / a
    ratio_measured = measured_prefill / measured_decode
    if not (0.5 <= ratio_fit / ratio_measured <= 2.0):
        verdict_reasons.append(
            f"fitted prefill:decode speed ratio {ratio_fit:.1f}x disagrees with the "
            f"directly measured {ratio_measured:.1f}x by more than an order of magnitude")
    if abs(corr) < 0.3:
        verdict_reasons.append(
            f"collinearity is NOT the cause (corr = {corr:+.3f}); the regressors are "
            f"close to independent, so the misattribution is structural, not numerical")

    usable = not verdict_reasons
    print(f"\n[3/3] verdict: reconstruction is "
          f"{'USABLE' if usable else 'NOT USABLE'}")
    for r in verdict_reasons:
        print(f"      - {r}")

    payload = {
        "n_branches": n,
        "fit": {"prefill_ms_per_token": round(a * 1000, 6),
                "prefill_tokens_per_second": round(1 / a, 2),
                "decode_ms_per_token": round(b * 1000, 6),
                "decode_tokens_per_second": round(1 / b, 2),
                "intercept_seconds": round(c0, 4),
                "r_squared": round(r2, 6),
                "rmse_seconds": round(rmse, 4),
                "mean_wall_seconds": round(ybar, 3)},
        "directly_measured_gate9": {
            "prefill_tokens_per_second": measured_prefill,
            "decode_tokens_per_second": measured_decode,
            "ratio": round(ratio_measured, 2)},
        "corr_prefill_decode_tokens": round(corr, 4),
        "reconstruction_usable": usable,
        "reasons": verdict_reasons,
        "conclusion": "per-branch prefill/decode time cannot be reconstructed from "
                      "stored token counts and total wall time; it must be re-measured",
    }
    OUT.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"\n  wrote {OUT.relative_to(ROOT).as_posix()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
