"""Step s06 / Gate 9 -- determinism under the frozen serving policy.

The CoLM run passed a 9/9 determinism audit. That result does NOT carry over: this
harness serves at --parallel 1 / ctx 32768 / --no-cont-batching, CoLM served at
--parallel 4 / ctx 65536. Different slot geometry, different batching, and both change
the arithmetic. The audit has to be re-run here or the paired design has no foundation:
if the same seed and the same prompt do not reproduce the same completion, then a C-A
difference cannot be attributed to the prior attempt.

Three things are checked, and all three matter.

  REPEAT     same messages, same seed, twice -> byte-identical completion.
             Run across all five arms, because the arms differ in prompt length and in
             conversation structure, and a cache or batching bug can be length-dependent.

  SEED       same messages, different seed -> a DIFFERENT completion.
             Without this, "deterministic" could just mean the seed is being ignored,
             which would silently collapse seed block 2 onto seed block 1.

  NO CACHE   every response reports cache_n == 0.
             Cached and fresh prefill are not bit-identical. The client raises on any
             cache hit, so this is enforced rather than merely observed.

Full frozen budget (max_tokens 12288) and the frozen sampler are used, because
determinism at 256 tokens says nothing about determinism at 12288.
"""

from __future__ import annotations

import json
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT / "src"))
sys.path.insert(0, str(HERE))

import anchoring  # noqa: E402
import generate  # noqa: E402
import pipeline  # noqa: E402
import receipts  # noqa: E402

STEP = pipeline.BY_ID["s06"]
BASE_URL = "http://127.0.0.1:8080"
SEED = 424242
SEED_ALT = 424243


def read_jsonl(path: Path) -> list[dict]:
    with path.open(encoding="utf-8") as fh:
        return [json.loads(line) for line in fh if line.strip()]


def pick(branches: list[dict]) -> list[dict]:
    """One eval branch per arm: the median-prompt-length branch of that arm, chosen by a
    stable rule so the audit is reproducible rather than cherry-picked."""
    chosen = []
    for arm in "ABCDE":
        pool = sorted((b for b in branches
                       if b["arm"] == arm and b["split"] == "held_out"),
                      key=lambda b: (b["payload_chars"], b["root_id"]))
        if pool:
            chosen.append(pool[len(pool) // 2])
    return chosen


def main() -> int:
    receipts.force_utf8()

    print(f"[1/3] server at {BASE_URL}")
    live, detail = anchoring.ServerTokenizer(BASE_URL).probe()
    if not live:
        print(f"      unavailable: {detail}")
        print("     powershell -NoProfile -File scripts\\start_server.ps1")
        print("\n  No receipt written -- s06 stays pending.")
        return 2
    print(f"      {detail}")

    branches = read_jsonl(ROOT / "data/prompts.jsonl")
    targets = pick(branches)
    client = generate.Client(BASE_URL)
    print(f"      sampler {generate.SAMPLER}, max_tokens {generate.MAX_TOKENS}")
    print(f"      {len(targets)} branches, 2 repeats each + 1 alternate-seed call")

    print("\n[2/3] generating")
    results = []
    t_start = time.time()
    calls = 0
    for i, b in enumerate(targets, 1):
        pair = []
        for rep in (1, 2):
            r = client.chat(b["messages"], seed=SEED)
            calls += 1
            pair.append(r)
            print(f"      {b['branch_key']:52} rep{rep}  "
                  f"{r.completion_tokens:5d} tok  {r.request_wall_seconds:6.1f}s  "
                  f"{r.decode_tokens_per_second:5.1f} tok/s  {r.finish_reason}")
        identical = pair[0].completion == pair[1].completion
        results.append({
            "branch_key": b["branch_key"],
            "arm": b["arm"],
            "check": "repeat_same_seed",
            "seed": SEED,
            "identical": identical,
            "pass": identical,
            "completion_tokens_1": pair[0].completion_tokens,
            "completion_tokens_2": pair[1].completion_tokens,
            "sha_1": receipts.sha_text(pair[0].completion),
            "sha_2": receipts.sha_text(pair[1].completion),
            "prefill_tokens": pair[0].prefill_tokens,
            "prefill_tok_per_s": round(pair[0].prefill_tokens_per_second, 1),
            "decode_tok_per_s": round(pair[0].decode_tokens_per_second, 1),
            "request_wall_seconds": round(pair[0].request_wall_seconds, 2),
            "finish_reason": pair[0].finish_reason,
            "cached_tokens": pair[0].cached_tokens,
        })
        print(f"      {'':52} -> {'IDENTICAL' if identical else 'DIVERGED'}")

        if i == 1:  # seed sensitivity, once
            alt = client.chat(b["messages"], seed=SEED_ALT)
            calls += 1
            differs = alt.completion != pair[0].completion
            results.append({
                "branch_key": b["branch_key"],
                "arm": b["arm"],
                "check": "alternate_seed",
                "seed": SEED_ALT,
                "identical": not differs,
                "pass": differs,
                "completion_tokens_1": pair[0].completion_tokens,
                "completion_tokens_2": alt.completion_tokens,
                "sha_1": receipts.sha_text(pair[0].completion),
                "sha_2": receipts.sha_text(alt.completion),
                "prefill_tokens": alt.prefill_tokens,
                "prefill_tok_per_s": round(alt.prefill_tokens_per_second, 1),
                "decode_tok_per_s": round(alt.decode_tokens_per_second, 1),
                "request_wall_seconds": round(alt.request_wall_seconds, 2),
                "finish_reason": alt.finish_reason,
                "cached_tokens": alt.cached_tokens,
            })
            print(f"      {'':52} -> alternate seed "
                  f"{'DIFFERS (good)' if differs else 'IDENTICAL (seed ignored!)'}")

    elapsed = time.time() - t_start

    print("\n[3/3] verdict")
    fails = [r for r in results if not r["pass"]]
    payload = {
        "seed": SEED,
        "seed_alt": SEED_ALT,
        "sampler": generate.SAMPLER,
        "max_tokens": generate.MAX_TOKENS,
        "serving": {"parallel": 1, "n_ctx": 32768, "cont_batching": False,
                    "cache_prompt": False},
        "model_calls": calls,
        "elapsed_seconds": round(elapsed, 1),
        "checks": results,
        "result": "PASS" if not fails else "FAIL",
    }
    (ROOT / "audit/determinism.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    for r in results:
        flag = "ok  " if r["pass"] else "FAIL"
        print(f"      {flag} {r['check']:18} {r['branch_key']}")

    if fails:
        print(f"\n  GATE 9 FAILED -- {len(fails)} check(s).")
        print("  Without determinism the paired within-root contrasts have no foundation.")
        return 1

    rep = [r for r in results if r["check"] == "repeat_same_seed"]
    stats = {
        "branches_checked": len(rep),
        "arms_checked": sorted({r["arm"] for r in rep}),
        "model_calls": calls,
        "elapsed_seconds": round(elapsed, 1),
        "seed": SEED,
        "median_decode_tok_per_s": sorted(r["decode_tok_per_s"] for r in rep)[len(rep) // 2],
        "median_prefill_tok_per_s": sorted(r["prefill_tok_per_s"] for r in rep)[len(rep) // 2],
        "all_cache_n_zero": all(r["cached_tokens"] == 0 for r in results),
        "result": "PASS",
    }
    receipts.write(STEP["id"], STEP["title"], STEP["inputs"], STEP["outputs"], stats)
    print()
    for k, v in stats.items():
        print(f"      {k:26} {v}")
    print("\n  GATE 9 PASS. s06 done.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
