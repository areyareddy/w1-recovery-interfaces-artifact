"""Step s04 / Gate 6 -- freeze the textual-anchoring proxy and prove it behaves.

Two parts, and both must pass.

PART 1, synthetic unit gate. Runs on explicit token-ID lists, so it tests the formula
itself with no tokenizer in the way. If the arithmetic is wrong, this catches it in
milliseconds instead of after 181 generations.

PART 2, real model tokens. Needs the llama.cpp server up, because model_tokens means the
model's own tokenizer and nothing else. It establishes two things the analysis will lean
on later:

  self-similarity   S(prior, prior) == 1.0 exactly, on all 83 roots
  null band         the distribution of S between prior attempts of DIFFERENT roots

That null band is the reference the paper needs. T0 and T1 are differences of S values;
without knowing what S looks like for unrelated text from the same model on the same
task distribution, a T0 of 0.04 is uninterpretable. Pre-registering the band before any
branch is generated is the only way it stays a reference and not a post-hoc rationale.

If the server is down this exits 2 and writes NO receipt -- the step stays pending, and
status.py keeps saying so.
"""

from __future__ import annotations

import csv
import json
import random
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT / "src"))
sys.path.insert(0, str(HERE))

import anchoring  # noqa: E402
import pipeline  # noqa: E402
import receipts  # noqa: E402

STEP = pipeline.BY_ID["s04"]
BASE_URL = "http://127.0.0.1:8080"
NULL_BAND_PAIRS = 400
NULL_BAND_SEED = 20260828


def read_jsonl(path: Path) -> list[dict]:
    with path.open(encoding="utf-8") as fh:
        return [json.loads(line) for line in fh if line.strip()]


def unit_gate() -> tuple[list[dict], int]:
    """Token-ID level cases with hand-computed expected values."""
    S = anchoring.similarity
    N = anchoring.normalize
    ten = list(range(10))

    cases: list[tuple[str, float, float, str]] = []

    def chk(name, got, want, why):
        cases.append((name, got, want, why))

    chk("identical_10", S(ten, ten), 1.0, "a completion vs itself is perfect retention")
    chk("both_empty", S([], []), 1.0, "degenerate, must not divide by zero")
    chk("empty_vs_5", S([], [1, 2, 3, 4, 5]), 0.0, "nothing retained")
    chk("one_substitution", S(ten, [99] + ten[1:]), 0.9, "1 edit over max len 10")
    chk("one_deletion", S(ten, ten[1:]), 0.9, "1 edit over max len 10")
    chk("prefix_3_of_10", S(ten, ten[:3]), 0.3, "7 deletions over max len 10")
    chk("disjoint_equal_len", S(ten, list(range(100, 110))), 0.0, "10 edits over 10")
    chk("symmetry", S(ten[:4], ten), S(ten, ten[:4]), "S must be symmetric")
    chk("longer_dilutes", S(ten, ten + list(range(50, 90))), 0.2,
        "40 insertions over max len 50")

    # normalization
    chk("norm_crlf", 1.0 if N("a \r\nb\r\n") == "a\nb" else 0.0, 1.0,
        "CRLF collapses and trailing space goes")
    chk("norm_lone_cr", 1.0 if N("a\rb") == "a\nb" else 0.0, 1.0, "bare CR is a newline")
    chk("norm_idempotent", 1.0 if N(N("  x \t\r\n y  ")) == N("  x \t\r\n y  ") else 0.0,
        1.0, "normalizing twice must change nothing")
    chk("norm_keeps_indent",
        1.0 if N("theorem f :=\n  by\n    ring") == "theorem f :=\n  by\n    ring" else 0.0,
        1.0, "Lean indentation is load-bearing and must survive")
    chk("norm_keeps_unicode",
        1.0 if N("∀ x : ℝ, x = x") == "∀ x : ℝ, x = x" else 0.0,
        1.0, "Lean identifiers are unicode")
    chk("norm_keeps_blank_lines",
        1.0 if N("a\n\n\nb") == "a\n\n\nb" else 0.0, 1.0,
        "blank-line structure is not collapsed")

    # bounds on random pairs
    rng = random.Random(7)
    in_bounds = True
    for _ in range(300):
        a = [rng.randrange(50) for _ in range(rng.randrange(0, 40))]
        b = [rng.randrange(50) for _ in range(rng.randrange(0, 40))]
        s = S(a, b)
        if not (0.0 - 1e-12 <= s <= 1.0 + 1e-12) or abs(s - S(b, a)) > 1e-12:
            in_bounds = False
            break
    chk("random_bounds_and_symmetry", 1.0 if in_bounds else 0.0, 1.0,
        "300 random pairs stay in [0,1] and are symmetric")

    rows, failed = [], 0
    for name, got, want, why in cases:
        ok = abs(got - want) < 1e-12
        failed += 0 if ok else 1
        rows.append({"part": "unit", "case": name, "got": round(got, 12),
                     "expected": round(want, 12), "pass": ok, "why": why})
    return rows, failed


def main() -> int:
    receipts.force_utf8()

    print("[1/3] synthetic unit gate")
    rows, failed = unit_gate()
    for r in rows:
        flag = "ok  " if r["pass"] else "FAIL"
        print(f"      {flag} {r['case']:28} {r['got']}")
    if failed:
        print(f"\n  GATE 6 FAILED -- {failed} unit case(s). The formula is wrong.")
        return 1
    print(f"      {len(rows)} cases pass")

    print(f"\n[2/3] model tokenizer at {BASE_URL}")
    tok = anchoring.ServerTokenizer(BASE_URL)
    live, detail = tok.probe()
    if not live:
        print(f"      unavailable: {detail}")
        print("\n  s04 part 2 needs the frozen serving process, because model_tokens")
        print("  means the model's own tokenizer. There is deliberately no fallback:")
        print("  a substitute tokenizer would change every S in the paper silently.")
        print("\n  Start it, then re-run this step:")
        print("     powershell -NoProfile -File scripts\\start_server.ps1")
        print("     python scripts\\s04_anchoring_metric.py")
        print("\n  No receipt written -- s04 stays pending.")
        return 2
    print(f"      {detail}")

    roots = read_jsonl(ROOT / "data/roots.jsonl")
    print(f"\n[3/3] tokenizing {len(roots)} prior attempts")
    toks: dict[str, list[int]] = {}
    t0 = time.time()
    for i, rec in enumerate(sorted(roots, key=lambda r: r["root_id"]), 1):
        rid = rec["root_id"]
        raw = (ROOT / "artifacts/roots" / rid / "raw_completion.txt").read_text(
            encoding="utf-8")
        toks[rid] = tok.tokens(raw)
        if i % 20 == 0 or i == len(roots):
            print(f"      {i:3d}/{len(roots)} ({100 * i // len(roots):3d}%)")
    print(f"      {time.time() - t0:.1f}s, "
          f"{sum(len(v) for v in toks.values())} tokens total")

    self_fail = 0
    for rid, t in toks.items():
        s = anchoring.similarity(t, t)
        if abs(s - 1.0) > 1e-12:
            self_fail += 1
            rows.append({"part": "self", "case": rid, "got": s, "expected": 1.0,
                         "pass": False, "why": "S(prior, prior) must be exactly 1.0"})
    if not self_fail:
        rows.append({"part": "self", "case": "all_83_self_similarity", "got": 1.0,
                     "expected": 1.0, "pass": True,
                     "why": "S(prior, prior) == 1.0 on every root"})
    print(f"      self-similarity: {len(toks) - self_fail}/{len(toks)} exactly 1.0")

    ids = sorted(toks)
    rng = random.Random(NULL_BAND_SEED)
    pairs = set()
    while len(pairs) < min(NULL_BAND_PAIRS, len(ids) * (len(ids) - 1) // 2):
        a, b = rng.sample(ids, 2)
        pairs.add(tuple(sorted((a, b))))
    band = sorted(anchoring.similarity(toks[a], toks[b]) for a, b in pairs)
    n = len(band)
    q = lambda p: band[min(n - 1, int(p * n))]  # noqa: E731
    print(f"      null band over {n} cross-root pairs: "
          f"min {band[0]:.4f}  p50 {q(0.50):.4f}  p95 {q(0.95):.4f}  max {band[-1]:.4f}")
    rows.append({"part": "null_band", "case": f"{n}_cross_root_pairs",
                 "got": round(q(0.50), 6), "expected": "", "pass": True,
                 "why": "median S between prior attempts of unrelated roots"})

    with (ROOT / "audit/anchoring_unit_gate.csv").open("w", encoding="utf-8",
                                                       newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=["part", "case", "got", "expected", "pass", "why"])
        w.writeheader()
        w.writerows(rows)

    if self_fail:
        print(f"\n  GATE 6 FAILED -- {self_fail} root(s) not self-similar.")
        return 1

    stats = {
        "metric_id": anchoring.METRIC_ID,
        "normalization_id": anchoring.NORMALIZE_ID,
        "unit_cases": len([r for r in rows if r["part"] == "unit"]),
        "roots_tokenized": len(toks),
        "median_prior_tokens": sorted(len(v) for v in toks.values())[len(toks) // 2],
        "max_prior_tokens": max(len(v) for v in toks.values()),
        "null_band_pairs": n,
        "null_band_seed": NULL_BAND_SEED,
        "null_band_min": round(band[0], 6),
        "null_band_p50": round(q(0.50), 6),
        "null_band_p95": round(q(0.95), 6),
        "null_band_max": round(band[-1], 6),
        "result": "PASS",
    }
    receipts.write(STEP["id"], STEP["title"], STEP["inputs"], STEP["outputs"], stats)
    print()
    for k, v in stats.items():
        print(f"      {k:24} {v}")
    print("\n  GATE 6 PASS. s04 done.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
