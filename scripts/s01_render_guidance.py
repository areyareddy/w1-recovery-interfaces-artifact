"""Step s01 / Gate 2 -- render the frozen R2 guidance through CoLM's own template.

Preconditions (both enforced here, so this one command IS the gate):
  1. every frozen symbol in src/policy.py is byte-identical to mospe_navi.py
     (scripts/sync_policy.py, run inline below)
  2. data/roots.jsonl exists and its 83 records carry non-empty R2 tactic lists

What it produces, per root:
  prompt_A        = official_prompt(theorem)                      -- no guidance
  prompt_B        = concrete_guidance_prompt(theorem, R2 tactics) -- guidance outermost
  guidance_block  = the exact prefix such that block + prompt_A == prompt_B

That last identity is the whole point. concrete_guidance_prompt PREPENDS: the theorem is
embedded inside the base template, so theorem-and-base are one inseparable unit and the
guidance block can only sit outside it (MASTER_CORRECTION.md Sec.3). Establishing the
block as an exact string prefix here is what lets Gate 5 later assert A->B differs by
guidance ALONE, as a string containment rather than a judgement call.

Also carried forward for later cross-checks: the prompt_tokens the CoLM server actually
billed for each R2 stage-two call. s05 re-tokenizes our rendered prompt_B against the
live server; if our render is right those two numbers must agree.
"""

from __future__ import annotations

import csv
import json
import sys
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT / "src"))
sys.path.insert(0, str(HERE))

import pipeline  # noqa: E402
import policy  # noqa: E402
import receipts  # noqa: E402
import sync_policy  # noqa: E402

STEP = pipeline.BY_ID["s01"]
COLM = ROOT.parent / "CoLM_Jul2026_MoSpe_Navi"
CASCADE = COLM / "runs/epp_confirmatory_202/evaluation/cascade_attempts.jsonl"

SEPARATOR = "\n\nThese are optional suggestions; use only when applicable, and select " \
            "exact tactics and arguments from the current theorem.\n\n"
HEADER = "Similar Lean-verified proofs commonly used:\n"


def read_jsonl(path: Path) -> list[dict]:
    with path.open(encoding="utf-8") as fh:
        return [json.loads(line) for line in fh if line.strip()]


def main() -> int:
    receipts.force_utf8()

    print("[1/4] Gate 2a -- frozen policy symbols vs CoLM upstream")
    if sync_policy.main([]) != 0:
        print("ABORT: policy surface drifted; the 83 roots no longer describe this prompt.")
        return 1

    print("\n[2/4] loading roots")
    roots = read_jsonl(ROOT / "data/roots.jsonl")
    assert len(roots) == 83, f"expected 83 roots, got {len(roots)}"
    print(f"      {len(roots)} roots")

    # prompt_tokens the CoLM server billed for each real R2 stage-two call
    r2_tokens: dict[str, int] = {}
    for row in read_jsonl(CASCADE):
        if row.get("arm") == "R2":
            usage = (row.get("response") or {}).get("usage") or {}
            if "prompt_tokens" in usage:
                r2_tokens[row["problem_id"]] = usage["prompt_tokens"]

    print("\n[3/4] rendering and checking")
    assert policy.GUIDANCE_TEMPLATE == HEADER + "{listed}" + SEPARATOR
    template_sha = receipts.sha_text(policy.GUIDANCE_TEMPLATE)
    out: list[dict] = []
    rows: list[dict] = []
    n_tac = Counter()

    for i, rec in enumerate(roots, 1):
        rid = rec["root_id"]
        theorem = rec["theorem_text"]
        tactics = rec["r2_guidance_tactics"]

        assert isinstance(tactics, list) and tactics, f"{rid}: R2 guidance empty"
        assert all(isinstance(t, str) and t.strip() for t in tactics), \
            f"{rid}: non-string or blank tactic"
        frozen_block = policy.guidance_block(tactics)
        assert frozen_block == rec["r2_guidance_text"], \
            f"{rid}: rendered block differs from roots.jsonl"
        assert receipts.sha_text(frozen_block) == rec["r2_guidance_sha256"], \
            f"{rid}: guidance block sha mismatch vs roots.jsonl"
        assert template_sha == rec["guidance_template_sha256"], \
            f"{rid}: guidance template sha mismatch vs roots.jsonl"

        prompt_a = policy.official_prompt(theorem)
        prompt_b = policy.concrete_guidance_prompt(theorem, tactics)

        # the composition identity Gate 5 will rely on
        assert prompt_b.endswith(prompt_a), \
            f"{rid}: prompt_A is not a suffix of prompt_B -- composition is not guidance-outermost"
        block = prompt_b[: len(prompt_b) - len(prompt_a)]
        assert block + prompt_a == prompt_b, f"{rid}: block reconstruction failed"
        assert block == frozen_block, f"{rid}: guidance_block() differs from CoLM renderer"
        assert block, f"{rid}: empty guidance block despite non-empty tactics"
        assert block.startswith(HEADER), f"{rid}: unexpected guidance header"
        assert block.endswith(SEPARATOR), f"{rid}: unexpected guidance separator"
        assert theorem in prompt_a, f"{rid}: theorem not present in prompt_A"

        # tactics appear once each, in order, one per line, nothing else in the list
        listed = block[len(HEADER): len(block) - len(SEPARATOR)]
        assert listed.split("\n") == [f"- {t}" for t in tactics], \
            f"{rid}: rendered tactic list does not match the frozen R2 list"

        n_tac[len(tactics)] += 1
        out.append({
            "root_id": rid,
            "split": rec["split"],
            "fine_failure_class": rec["fine_failure_class"],
            "n_tactics": len(tactics),
            "guidance_block": block,
            "prompt_A": prompt_a,
            "prompt_B": prompt_b,
            "guidance_block_sha256": receipts.sha_text(block),
            "prompt_A_sha256": receipts.sha_text(prompt_a),
            "prompt_B_sha256": receipts.sha_text(prompt_b),
            "guidance_template_sha256": template_sha,
            "guidance_policy_id": rec["guidance_policy_id"],
            "guidance_renderer_source": rec["guidance_renderer_source"],
            "guidance_renderer_git_commit": rec["guidance_renderer_git_commit"],
            "colm_r2_prompt_tokens": r2_tokens.get(rid),
        })
        rows.append({k: v for k, v in out[-1].items()
                     if k not in ("guidance_block", "prompt_A", "prompt_B")})
        if i % 20 == 0 or i == len(roots):
            print(f"      {i:3d}/{len(roots)} ({100 * i // len(roots):3d}%)")

    print("\n[4/4] writing")
    with (ROOT / "data/guidance_render.jsonl").open("w", encoding="utf-8", newline="\n") as fh:
        for r in out:
            fh.write(json.dumps(r, ensure_ascii=False, sort_keys=True) + "\n")
    with (ROOT / "audit/guidance_render.csv").open("w", encoding="utf-8", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)

    blocks = {r["guidance_block_sha256"] for r in out}
    ev = [r for r in out if r["split"] == "held_out"]
    stats = {
        "roots": len(out),
        "eval_roots": len(ev),
        "distinct_guidance_blocks": len(blocks),
        "tactics_per_root": dict(sorted(n_tac.items())),
        "guidance_template_sha256": template_sha,
        "median_guidance_chars": sorted(len(r["guidance_block"]) for r in out)[len(out) // 2],
        "max_prompt_B_chars": max(len(r["prompt_B"]) for r in out),
        "roots_with_colm_r2_prompt_tokens": sum(1 for r in out
                                                if r["colm_r2_prompt_tokens"] is not None),
    }
    receipts.write(STEP["id"], STEP["title"], STEP["inputs"], STEP["outputs"], stats)

    print()
    for k, v in stats.items():
        print(f"      {k:34} {v}")
    print("\n  s01 done. Next: python scripts/status.py")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
