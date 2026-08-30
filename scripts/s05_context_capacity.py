"""Step s05 / Gate 8 -- every branch must fit the context window, with no elision rule.

The claim being tested:

    max(prompt_tokens) + max_tokens(12288) <= n_ctx(32768)

for all 376 branches, where prompt_tokens is measured the way the server measures it:
the chat template applied to the messages, then tokenized with special tokens parsed.
Arm D is the worst case (guidance + wrapper + full prior attempt + base) and arm E is
the worst multi-turn case.

This matters because the alternative is an elision rule -- truncating long prior
attempts to fit -- and an elision rule would apply unevenly across failure classes.
Truncated roots carry the longest artifacts by construction, so eliding would weaken the
prior-attempt treatment exactly where it is most interesting, and Analysis 3 would be
measuring the elision rule instead of the failure class.

FREE CALIBRATION, and the real reason this step is worth more than a capacity number.
Our arm B payload is supposed to be byte-identical to the stage-two prompt CoLM actually
sent under arm R2 -- same theorem, same frozen tactic list, same renderer, one user turn,
no system message. CoLM recorded the server's own prompt_tokens for each of those calls.
So comparing our measured B token count against that recorded number is an end-to-end
check of the whole path -- root extraction, guidance freeze, renderer port, chat template
-- against ground truth from a different run, at zero GPU cost. If those numbers agree on
all 83 roots, the reconstruction is right. If they disagree, something upstream is wrong
and no amount of internal consistency would have revealed it.
"""

from __future__ import annotations

import csv
import json
import sys
import time
import urllib.request
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT / "src"))
sys.path.insert(0, str(HERE))

import anchoring  # noqa: E402
import pipeline  # noqa: E402
import receipts  # noqa: E402

STEP = pipeline.BY_ID["s05"]
BASE_URL = "http://127.0.0.1:8080"

N_CTX = 32768
MAX_TOKENS = 12288          # frozen generation budget for the primary run
SAFETY_MARGIN = 64          # BOS/EOS bookkeeping slack; never consumed deliberately


def post(path: str, body: dict, timeout: int = 120) -> dict:
    req = urllib.request.Request(
        BASE_URL + path, data=json.dumps(body).encode("utf-8"),
        headers={"Content-Type": "application/json"})
    with urllib.request.urlopen(req, timeout=timeout) as resp:
        return json.loads(resp.read().decode("utf-8"))


def get(path: str, timeout: int = 30) -> dict:
    with urllib.request.urlopen(BASE_URL + path, timeout=timeout) as resp:
        return json.loads(resp.read().decode("utf-8"))


def read_jsonl(path: Path) -> list[dict]:
    with path.open(encoding="utf-8") as fh:
        return [json.loads(line) for line in fh if line.strip()]


def main() -> int:
    receipts.force_utf8()

    print(f"[1/4] server at {BASE_URL}")
    live, detail = anchoring.ServerTokenizer(BASE_URL).probe()
    if not live:
        print(f"      unavailable: {detail}")
        print("\n  Start it, then re-run:")
        print("     powershell -NoProfile -File scripts\\start_server.ps1")
        print("\n  No receipt written -- s05 stays pending.")
        return 2
    props = get("/props")
    served_ctx = props.get("default_generation_settings", {}).get("n_ctx")
    print(f"      {detail}")
    print(f"      served n_ctx={served_ctx}  slots={props.get('total_slots')}")
    assert served_ctx == N_CTX, (
        f"server is running at n_ctx={served_ctx}, this gate assumes {N_CTX}. "
        f"Restart with scripts/start_server.ps1 before trusting any capacity number."
    )

    branches = read_jsonl(ROOT / "data/prompts.jsonl")
    render = {r["root_id"]: r for r in read_jsonl(ROOT / "data/guidance_render.jsonl")}
    print(f"\n[2/4] measuring {len(branches)} branch payloads")

    rows: list[dict] = []
    t0 = time.time()
    for i, b in enumerate(branches, 1):
        rendered = post("/apply-template", {"messages": b["messages"]})["prompt"]
        toks = post("/tokenize", {"content": rendered})["tokens"]
        n = len(toks)
        rows.append({
            "branch_key": b["branch_key"],
            "root_id": b["root_id"],
            "split": b["split"],
            "arm": b["arm"],
            "conversation_turns": b["conversation_turns"],
            "payload_chars": b["payload_chars"],
            "templated_chars": len(rendered),
            "prompt_tokens": n,
            "max_tokens": MAX_TOKENS,
            "total_required": n + MAX_TOKENS,
            "n_ctx": N_CTX,
            "headroom": N_CTX - (n + MAX_TOKENS),
            "fits": n + MAX_TOKENS + SAFETY_MARGIN <= N_CTX,
            "fine_failure_class": b["fine_failure_class"],
        })
        if i % 50 == 0 or i == len(branches):
            print(f"      {i:3d}/{len(branches)} ({100 * i // len(branches):3d}%)")
    print(f"      {time.time() - t0:.1f}s")

    print("\n[3/4] cross-check vs CoLM's recorded R2 prompt_tokens")
    by_key = {r["branch_key"]: r for r in rows}
    agree = disagree = missing = 0
    deltas = Counter()
    examples: list[str] = []
    for rid, g in render.items():
        recorded = g.get("colm_r2_prompt_tokens")
        if recorded is None:
            missing += 1
            continue
        ours = by_key[f"{rid}|B"]["prompt_tokens"]
        d = ours - recorded
        deltas[d] += 1
        if d == 0:
            agree += 1
        else:
            disagree += 1
            if len(examples) < 5:
                examples.append(f"{rid}: ours {ours} vs CoLM {recorded} (delta {d:+d})")
    print(f"      exact match {agree}/{agree + disagree}   "
          f"(no recorded value: {missing})")
    if disagree:
        print(f"      delta histogram: {dict(sorted(deltas.items()))}")
        for e in examples:
            print(f"        {e}")

    print("\n[4/4] capacity")
    worst = max(rows, key=lambda r: r["total_required"])
    fails = [r for r in rows if not r["fits"]]
    per_arm = {}
    for arm in "ABCDE":
        a = [r["prompt_tokens"] for r in rows if r["arm"] == arm]
        if a:
            per_arm[arm] = {"n": len(a), "median": sorted(a)[len(a) // 2], "max": max(a)}
            print(f"      arm {arm}  n={len(a):3d}  median {sorted(a)[len(a)//2]:6d}  "
                  f"max {max(a):6d} tokens")
    print(f"\n      worst case: {worst['branch_key']}  "
          f"{worst['prompt_tokens']} + {MAX_TOKENS} = {worst['total_required']} "
          f"of {N_CTX}  (headroom {worst['headroom']})")

    with (ROOT / "audit/context_capacity.csv").open("w", encoding="utf-8", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)

    if fails:
        print(f"\n  GATE 8 FAILED -- {len(fails)} branch(es) do not fit:")
        for r in fails[:10]:
            print(f"    {r['branch_key']}  needs {r['total_required']} of {N_CTX}")
        print("\n  An elision rule would be required, and it would bias by failure class.")
        return 1

    stats = {
        "branches_measured": len(rows),
        "n_ctx": N_CTX,
        "max_tokens": MAX_TOKENS,
        "safety_margin": SAFETY_MARGIN,
        "worst_branch": worst["branch_key"],
        "worst_prompt_tokens": worst["prompt_tokens"],
        "worst_total_required": worst["total_required"],
        "worst_headroom": worst["headroom"],
        "per_arm": per_arm,
        "colm_r2_prompt_token_exact_match": f"{agree}/{agree + disagree}",
        "colm_r2_delta_histogram": dict(sorted(deltas.items())),
        "elision_rule_needed": False,
        "result": "PASS",
    }
    receipts.write(STEP["id"], STEP["title"], STEP["inputs"], STEP["outputs"], stats)
    print(f"\n  GATE 8 PASS -- all {len(rows)} branches fit with "
          f"{worst['headroom']} tokens to spare. No elision rule.")
    print("  s05 done.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
