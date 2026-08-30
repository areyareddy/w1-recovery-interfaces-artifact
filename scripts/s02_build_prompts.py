"""Step s02 / Gate 4 -- build every branch payload, for all 83 roots and all arms.

Output: data/prompts.jsonl, one record per (root, arm) branch.

    83 roots x A/B/C/D = 332
    +  44 E-eligible   =  44        (23 dev + 21 eval -- MASTER_CORRECTION Sec.1)
    ------------------------------
                         376 branches built

Building all 376 costs nothing and is not a commitment to generate them. The primary
run selects eval-40 x A/B/C/D + eval E = 160 + 21 = 181; the full-pool run selects
332 + 21 = 353. Both are subsets of what this step emits, so neither needs a rebuild.

Every payload is assembled through src/prompts.py and nowhere else. That is the whole
reason Gate 5 (s03) means anything: it audits the same code path generation uses.

Integrity checks performed here, per root:
  - artifacts/roots/<id>/raw_completion.txt still hashes to the sha frozen in roots.jsonl
  - the rendered R2 block still hashes to r2_guidance_sha256
  - the native <error> block is REBUILT from the stored REPL stdout and must match both
    the stored native_error.txt and native_feedback_sha256
  - arm E is refused unless feedback_kind == "native_error" (no synthesized placeholders)
"""

from __future__ import annotations

import json
import sys
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT / "src"))
sys.path.insert(0, str(HERE))

import goedel_native  # noqa: E402
import pipeline  # noqa: E402
import policy  # noqa: E402
import prompts  # noqa: E402
import receipts  # noqa: E402

STEP = pipeline.BY_ID["s02"]

# The prior attempt is stage one, so the native correction turn refers to Round 1.
# Frozen here rather than computed, because it is part of the arm-E prompt text.
PREV_ROUND = 1


def read_jsonl(path: Path) -> list[dict]:
    with path.open(encoding="utf-8") as fh:
        return [json.loads(line) for line in fh if line.strip()]


def main() -> int:
    receipts.force_utf8()

    print("[1/4] loading")
    roots = read_jsonl(ROOT / "data/roots.jsonl")
    render = {r["root_id"]: r for r in read_jsonl(ROOT / "data/guidance_render.jsonl")}
    assert len(roots) == 83, f"expected 83 roots, got {len(roots)}"
    assert len(render) == 83, f"expected 83 rendered roots, got {len(render)}"
    print(f"      83 roots, 83 rendered guidance blocks")

    print("\n[2/4] building branches")
    out: list[dict] = []
    arms_built = Counter()
    n_e = 0

    for i, rec in enumerate(sorted(roots, key=lambda r: r["root_id"]), 1):
        rid = rec["root_id"]
        adir = ROOT / "artifacts/roots" / rid
        theorem = rec["theorem_text"]
        tactics = rec["r2_guidance_tactics"]

        raw = (adir / "raw_completion.txt").read_text(encoding="utf-8")
        assert receipts.sha_text(raw) == rec["raw_prior_assistant_completion_sha256"], \
            f"{rid}: raw_completion.txt does not match the sha frozen in roots.jsonl"

        block = prompts.guidance_block(theorem, tactics)
        assert receipts.sha_text(block) == rec["r2_guidance_sha256"], \
            f"{rid}: rendered R2 block does not match r2_guidance_sha256"
        assert block == render[rid]["guidance_block"], \
            f"{rid}: R2 block disagrees with s01's guidance_render.jsonl"

        # --- arm E feedback, rebuilt from the stored REPL response ------------------
        feedback = None
        error_block = None
        if rec["native_feedback_available"]:
            stdout = (adir / "lean_stdout.json").read_text(encoding="utf-8")
            errors = goedel_native.repl_errors(stdout)
            extracted = (adir / "extracted_prior.lean").read_text(encoding="utf-8")
            code = goedel_native.submitted_code(extracted)
            feedback, error_block, kind = goedel_native.build_feedback(
                rec["outcome_state"], code, errors, prev_round=PREV_ROUND)
            assert kind == "native_error", f"{rid}: E built from non-native kind {kind!r}"
            assert error_block.count("<error>") >= 1, \
                f"{rid}: native feedback carries no <error> marker"
            assert receipts.sha_text(error_block) == rec["native_feedback_sha256"], \
                f"{rid}: rebuilt <error> block differs from native_feedback_sha256"
            assert error_block == (adir / "native_error.txt").read_text(encoding="utf-8"), \
                f"{rid}: rebuilt <error> block differs from stored native_error.txt"

        # --- payloads ---------------------------------------------------------------
        for arm in prompts.ARMS:
            if arm == "E":
                if not rec["native_feedback_available"]:
                    continue
                messages = prompts.arm_messages(
                    "E", theorem, raw_prior_attempt=raw, native_feedback=feedback)
                guidance_present, prior_present = False, True
                n_e += 1
            else:
                guidance_present, prior_present = prompts.ARM_FACTORS[arm]
                messages = prompts.arm_messages(
                    arm, theorem,
                    tactics=tactics if guidance_present else None,
                    raw_prior_attempt=raw if prior_present else None)

            payload_sha = receipts.sha_text(
                json.dumps(messages, ensure_ascii=False, sort_keys=True))
            out.append({
                "branch_key": f"{rid}|{arm}",
                "root_id": rid,
                "split": rec["split"],
                "arm": arm,
                "arm_title": prompts.ARM_TITLE[arm],
                "guidance_present": guidance_present,
                "prior_attempt_present": prior_present,
                "native_feedback_present": arm == "E",
                "conversation_turns": len(messages),
                "messages": messages,
                "payload_chars": sum(len(m["content"]) for m in messages),
                "payload_sha256": payload_sha,
                "base_prompt_sha256": receipts.sha_text(policy.official_prompt(theorem)),
                "guidance_block_sha256": rec["r2_guidance_sha256"] if guidance_present else None,
                "prior_attempt_sha256": rec["raw_prior_assistant_completion_sha256"]
                                        if prior_present else None,
                "native_feedback_sha256": rec["native_feedback_sha256"] if arm == "E" else None,
                "wrapper_sha256": receipts.sha_text(prompts.NEUTRAL_PRIOR_ATTEMPT_WRAPPER)
                                  if prior_present and arm != "E" else None,
                "fine_failure_class": rec["fine_failure_class"],
                "coarse_failure_group": rec["coarse_failure_group"],
                "raw_prior_completion_tokens": rec["raw_prior_completion_tokens"],
                "stage1_prompt_tokens": rec["stage1_prompt_tokens"],
            })
            arms_built[arm] += 1

        if i % 20 == 0 or i == len(roots):
            print(f"      {i:3d}/{len(roots)} roots ({100 * i // len(roots):3d}%)  "
                  f"{len(out)} branches")

    print("\n[3/4] cross-arm invariants")
    by_root: dict[str, dict[str, dict]] = {}
    for r in out:
        by_root.setdefault(r["root_id"], {})[r["arm"]] = r
    for rid, arms in by_root.items():
        # v7 04 Sec.7: the guidance in B and D, and the prior attempt in C and D, must be
        # the exact same bytes -- otherwise the 2x2 has two things moving per cell.
        assert arms["B"]["guidance_block_sha256"] == arms["D"]["guidance_block_sha256"], \
            f"{rid}: B and D carry different R2 guidance"
        assert arms["C"]["prior_attempt_sha256"] == arms["D"]["prior_attempt_sha256"], \
            f"{rid}: C and D carry different prior attempts"
        assert len({arms[a]["base_prompt_sha256"] for a in "ABCD"}) == 1, \
            f"{rid}: A/B/C/D do not share one base prompt"
        assert all(arms[a]["conversation_turns"] == 1 for a in "ABCD"), \
            f"{rid}: A/B/C/D must be a single user turn -- conversation structure is held fixed"
        if "E" in arms:
            assert arms["E"]["conversation_turns"] == 3, f"{rid}: E must be 3 turns"
            assert arms["E"]["messages"][0]["content"] == arms["A"]["messages"][0]["content"], \
                f"{rid}: E's opening turn must be identical to arm A"
            assert arms["E"]["messages"][1]["content"] == \
                (ROOT / "artifacts/roots" / rid / "raw_completion.txt").read_text(encoding="utf-8"), \
                f"{rid}: E's assistant turn is not the exact prior completion"
    print(f"      ok on {len(by_root)} roots")

    print("\n[4/4] writing")
    with (ROOT / "data/prompts.jsonl").open("w", encoding="utf-8", newline="\n") as fh:
        for r in out:
            fh.write(json.dumps(r, ensure_ascii=False, sort_keys=True) + "\n")

    ev = [r for r in out if r["split"] == "held_out"]
    stats = {
        "branches_total": len(out),
        "per_arm": dict(sorted(arms_built.items())),
        "e_branches": n_e,
        "primary_run_eval_181": sum(1 for r in ev if r["arm"] in "ABCD") + \
                                sum(1 for r in ev if r["arm"] == "E"),
        "full_pool_353": len([r for r in out if r["arm"] in "ABCD"]) + \
                         sum(1 for r in ev if r["arm"] == "E"),
        "wrapper_sha256": receipts.sha_text(prompts.NEUTRAL_PRIOR_ATTEMPT_WRAPPER),
        "max_payload_chars": max(r["payload_chars"] for r in out),
        "max_payload_branch": max(out, key=lambda r: r["payload_chars"])["branch_key"],
        "median_payload_chars_D": sorted(
            r["payload_chars"] for r in out if r["arm"] == "D")[41],
        "distinct_payloads": len({r["payload_sha256"] for r in out}),
    }
    receipts.write(STEP["id"], STEP["title"], STEP["inputs"], STEP["outputs"], stats)

    print()
    for k, v in stats.items():
        print(f"      {k:26} {v}")
    print("\n  s02 done. Next: python scripts/s03_prompt_diff_audit.py")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
