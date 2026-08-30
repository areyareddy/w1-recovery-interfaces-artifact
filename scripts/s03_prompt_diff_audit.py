"""Step s03 / Gate 5 -- the prompt-diff audit. HARD GATE.

v7 `04` Sec.7 states the requirement:

    A -> B = R2 guidance only
    A -> C = prior attempt + neutral wrapper only
    B -> D = prior attempt + neutral wrapper only
    C -> D = R2 guidance only
    sha256(R2 in B) == sha256(R2 in D)
    sha256(prior in C) == sha256(prior in D)

This script asserts all of that as EXACT STRING RECONSTRUCTION rather than as a diff.
"Differs by guidance only" is checked by rebuilding B from A and the guidance block and
requiring byte equality -- a diff can look clean while whitespace or ordering shifted
somewhere else in the string.

It also checks the negative direction, which the plan does not ask for but which is what
actually establishes the 2x2. A factor being present in the right cells is only half the
claim; it must be ABSENT in the others:

    guidance block does not occur anywhere in A or C
    prior attempt does not occur anywhere in A or B

Every check runs on all 83 roots (not just eval-40), and every check must pass. A single
failure means the factorial is confounded and generation must not start.
"""

from __future__ import annotations

import csv
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT / "src"))
sys.path.insert(0, str(HERE))

import pipeline  # noqa: E402
import prompts  # noqa: E402
import receipts  # noqa: E402

STEP = pipeline.BY_ID["s03"]

CHECKS = [
    "a_to_b_guidance_only",
    "a_to_c_prior_only",
    "b_to_d_prior_only",
    "c_to_d_guidance_only",
    "guidance_sha_b_eq_d",
    "prior_sha_c_eq_d",
    "base_prompt_shared_abcd",
    "guidance_absent_in_a",
    "guidance_absent_in_c",
    "prior_absent_in_a",
    "prior_absent_in_b",
    "wrapper_skeleton_uniform",
    "e_opening_turn_equals_a",
]


def read_jsonl(path: Path) -> list[dict]:
    with path.open(encoding="utf-8") as fh:
        return [json.loads(line) for line in fh if line.strip()]


def main() -> int:
    receipts.force_utf8()

    print("[1/3] loading branch payloads")
    branches = read_jsonl(ROOT / "data/prompts.jsonl")
    by_root: dict[str, dict[str, dict]] = {}
    for b in branches:
        by_root.setdefault(b["root_id"], {})[b["arm"]] = b
    print(f"      {len(branches)} branches over {len(by_root)} roots")

    wrapper_skeleton_sha = receipts.sha_text(prompts.NEUTRAL_PRIOR_ATTEMPT_WRAPPER)

    print("\n[2/3] auditing")
    rows: list[dict] = []
    failures: list[str] = []

    for i, (rid, arms) in enumerate(sorted(by_root.items()), 1):
        text = {a: arms[a]["messages"][0]["content"] for a in "ABCD"}
        # the two manipulated components, as the exact bytes that went into the payload
        prior = (ROOT / "artifacts/roots" / rid / "raw_completion.txt").read_text(
            encoding="utf-8")
        guidance = (ROOT / "artifacts/roots" / rid / "r2_guidance.txt").read_text(
            encoding="utf-8")
        wrapper = prompts.wrapper_block(prior)

        r = {"root_id": rid, "split": arms["A"]["split"]}

        # --- positive direction: exact reconstruction -------------------------------
        r["a_to_b_guidance_only"] = text["B"] == guidance + text["A"]
        r["a_to_c_prior_only"] = text["C"] == wrapper + text["A"]
        r["b_to_d_prior_only"] = text["D"] == guidance + wrapper + text["A"]
        r["c_to_d_guidance_only"] = text["D"] == guidance + text["C"]

        # --- component identity across cells ---------------------------------------
        r["guidance_sha_b_eq_d"] = (arms["B"]["guidance_block_sha256"]
                                    == arms["D"]["guidance_block_sha256"]
                                    == receipts.sha_text(guidance))
        r["prior_sha_c_eq_d"] = (arms["C"]["prior_attempt_sha256"]
                                 == arms["D"]["prior_attempt_sha256"]
                                 == receipts.sha_text(prior))
        r["base_prompt_shared_abcd"] = len({arms[a]["base_prompt_sha256"]
                                            for a in "ABCD"}) == 1

        # --- negative direction: the factor is absent where it must be --------------
        r["guidance_absent_in_a"] = guidance not in text["A"]
        r["guidance_absent_in_c"] = guidance not in text["C"]
        r["prior_absent_in_a"] = prior not in text["A"]
        r["prior_absent_in_b"] = prior not in text["B"]

        # --- wrapper is uniform: no per-root or per-failure-class wording ------------
        r["wrapper_skeleton_uniform"] = (
            arms["C"]["wrapper_sha256"] == arms["D"]["wrapper_sha256"]
            == wrapper_skeleton_sha)

        # --- arm E shares arm A's opening turn ---------------------------------------
        if "E" in arms:
            r["e_opening_turn_equals_a"] = (
                arms["E"]["messages"][0]["content"] == text["A"])
        else:
            r["e_opening_turn_equals_a"] = ""  # not applicable

        r["len_A"] = len(text["A"])
        r["len_B"] = len(text["B"])
        r["len_C"] = len(text["C"])
        r["len_D"] = len(text["D"])
        r["delta_guidance_chars"] = len(guidance)
        r["delta_prior_chars"] = len(wrapper)

        for c in CHECKS:
            if r[c] is False:
                failures.append(f"{rid}: {c}")
        rows.append(r)

        if i % 20 == 0 or i == len(by_root):
            print(f"      {i:3d}/{len(by_root)} ({100 * i // len(by_root):3d}%)")

    print("\n[3/3] writing")
    fields = ["root_id", "split"] + CHECKS + [
        "len_A", "len_B", "len_C", "len_D", "delta_guidance_chars", "delta_prior_chars"]
    with (ROOT / "audit/prompt_diff_audit.csv").open("w", encoding="utf-8", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=fields)
        w.writeheader()
        w.writerows(rows)

    print()
    for c in CHECKS:
        vals = [r[c] for r in rows if r[c] != ""]
        n_ok = sum(1 for v in vals if v is True)
        flag = "ok  " if n_ok == len(vals) else "FAIL"
        print(f"      {flag} {c:26} {n_ok}/{len(vals)}")

    if failures:
        print(f"\n  GATE 5 FAILED -- {len(failures)} check(s) did not pass:")
        for f in failures[:20]:
            print(f"    {f}")
        print("\n  The factorial is confounded. Do NOT start generation.")
        return 1

    stats = {
        "roots_audited": len(rows),
        "checks_per_root": len(CHECKS),
        "total_assertions": sum(1 for r in rows for c in CHECKS if r[c] != ""),
        "e_roots_checked": sum(1 for r in rows if r["e_opening_turn_equals_a"] != ""),
        "wrapper_skeleton_sha256": wrapper_skeleton_sha,
        "max_delta_prior_chars": max(r["delta_prior_chars"] for r in rows),
        "max_delta_guidance_chars": max(r["delta_guidance_chars"] for r in rows),
        "result": "PASS",
    }
    receipts.write(STEP["id"], STEP["title"], STEP["inputs"], STEP["outputs"], stats)

    print(f"\n  GATE 5 PASS -- {stats['total_assertions']} assertions over "
          f"{len(rows)} roots.")
    print("  s03 done. Next: python scripts/s04_anchoring_metric.py")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
