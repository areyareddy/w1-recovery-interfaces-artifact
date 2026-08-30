"""Step s11 / Gate 11 -- freeze the spec. This is the point of no return.

After this runs, spec/frozen_spec.yaml and its sha256 are the contract the primary run
executes against, and every generated branch records that sha. Changing a frozen value
afterwards and re-running would produce branches whose spec hash disagrees with their
neighbours, which is exactly the situation the hash exists to make visible.

Two jobs.

FIRST, assign seeds. Until now every branch's seed has been NULL and the runner refuses
to generate without one. The rule (src/seeds.py) is one seed per (root, block), SHARED
BY EVERY ARM of that root -- that sharing is what makes C - A a paired within-root
contrast rather than two independent draws.

SECOND, write down everything a replication would need and nothing it would not: the
hashes of the frozen policy surface, the prompt components, the sampler, the serving
configuration, the metric definition, the cohort sizes, and the results of every gate.

It REFUSES to freeze if any upstream gate is missing or stale. A spec that certifies a
Gate 5 result computed against a since-changed prompt file is worse than no spec.

The two decisions v7 left open are resolved here, in writing:

  seed block 2      block-2 seeds live at their own base rather than at an offset from
                    block 1, so non-collision is verifiable by inspection
  plain-draw band   pre-registered as a DESCRIPTIVE reference for arm A, sourced from 8
                    historical R0 runs on this exact eval-40, and explicitly labelled as
                    coming from a different batching configuration
"""

from __future__ import annotations

import json
import sqlite3
import sys
from pathlib import Path

import yaml

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT / "src"))
sys.path.insert(0, str(HERE))

import anchoring  # noqa: E402
import generate  # noqa: E402
import pipeline  # noqa: E402
import policy  # noqa: E402
import prompts  # noqa: E402
import receipts  # noqa: E402
import seeds as seeds_mod  # noqa: E402

STEP = pipeline.BY_ID["s11"]
DB = ROOT / "data/runs.sqlite"
SPEC = ROOT / "spec/frozen_spec.yaml"
SPEC_SHA = ROOT / "spec/frozen_spec.sha256"

REQUIRED_GATES = ["s00", "s01", "s02", "s03", "s04", "s05", "s06", "s07", "s08",
                  "s09", "s10"]

# Historical R0 = arm A under a different batching configuration: same prompt, same
# max_tokens 12288, same temperature 0.7; --parallel 4 / ctx 65536 rather than
# --parallel 1 / ctx 32768. Arm A prompts are 190-371 tokens, so the context difference
# is not binding. Pre-registered as a descriptive reference, never as a null distribution.
PLAIN_DRAW_BAND = {
    "status": "pre_registered_descriptive_reference",
    "source": "CoLM R0 (baseline retry, no guidance) on this exact eval-40 root set",
    "primary_8_matched_runs": {
        "runs": ["epp_replication40_d0", "epp_replication40_d1", "epp_replication40_d2",
                 "epp_replication40_d3", "epp_prospective40_seed56",
                 "epp_prospective40_seed57", "epp_prospective40_seed58",
                 "epp_prospective40_seed59"],
        "rescues_of_40": [8, 9, 7, 7, 9, 9, 8, 9],
        "band": "7-9 of 40",
        "pooled": "66/320 = 20.6%",
    },
    "wider_envelope_12_runs": {
        "adds": ["epp_confirmatory_202", "epp_confirmatory_202_matched_seeds",
                 "epp_confirmatory_202_router_seed540",
                 "epp_confirmatory_202_seed550_confirm"],
        "band": "6-11 of 40",
        "pooled": "97/480 = 20.2%",
    },
    "comparability_caveat":
        "different batching configuration (--parallel 4 / ctx 65536 vs --parallel 1 / "
        "ctx 32768). Prompt, sampler and max_tokens are identical. Report as a "
        "descriptive expectation, not as a test distribution.",
    "use": "if arm A lands outside 6-11 of 40, treat it as a signal that something in "
           "serving changed, and investigate before interpreting any contrast.",
}


def main() -> int:
    receipts.force_utf8()

    print("[1/4] upstream gates")
    blocked = []
    for step in REQUIRED_GATES:
        status, detail = receipts.verify(step)
        print(f"      {status:8} {step}  {detail}")
        if status != "done":
            blocked.append(f"{step} is {status} ({detail})")
    if blocked:
        print("\n  REFUSING to freeze:")
        for b in blocked:
            print(f"    {b}")
        print("\n  A spec that certifies a stale gate is worse than no spec.")
        return 1

    print("\n[2/4] assigning seeds")
    con = sqlite3.connect(DB)
    con.execute("PRAGMA busy_timeout=60000")
    root_ids = [r[0] for r in con.execute(
        "SELECT DISTINCT root_id FROM branches").fetchall()]
    assert len(root_ids) == 83, f"expected 83 roots in the store, got {len(root_ids)}"
    already = con.execute(
        "SELECT count(*) FROM branches WHERE seed IS NOT NULL AND status='done'"
    ).fetchone()[0]
    if already:
        print(f"      {already} completed branch(es) already carry seeds; leaving them")
    mapping = seeds_mod.all_seeds(root_ids, block=1)
    con.execute("BEGIN IMMEDIATE")
    for rid, seed in mapping.items():
        con.execute("UPDATE branches SET seed=? WHERE root_id=? AND seed_block=1 "
                    "AND status!='done'", (seed, rid))
    con.execute("COMMIT")
    lo, hi = con.execute("SELECT min(seed), max(seed) FROM branches "
                         "WHERE seed_block=1").fetchone()
    nulls = con.execute("SELECT count(*) FROM branches WHERE seed IS NULL").fetchone()[0]
    per_root = con.execute(
        "SELECT count(*) FROM (SELECT root_id, count(DISTINCT seed) c FROM branches "
        "WHERE seed_block=1 GROUP BY root_id) WHERE c != 1").fetchone()[0]
    con.close()
    print(f"      block 1 seeds {lo}..{hi}, {nulls} NULL remaining")
    assert nulls == 0, "every branch must carry a seed before the run"
    assert per_root == 0, "all arms of a root must share one seed (paired contrast)"
    print(f"      all arms of each root share one seed: ok")

    print("\n[3/4] building the spec")
    gates = {s: receipts.load(s)["stats"] for s in REQUIRED_GATES}
    roots = [json.loads(l) for l in (ROOT / "data/roots.jsonl").open(encoding="utf-8")]
    e_eligible = [r["root_id"] for r in roots
                  if r["native_feedback_available"] and r["split"] == "held_out"]

    spec = {
        "spec_version": 1,
        "frozen_utc": receipts.time.strftime("%Y-%m-%dT%H:%M:%SZ", receipts.time.gmtime()),
        "authoritative_correction": "MASTER_CORRECTION.md",
        "note": "This file wins over Updated_Proposal_V_7 wherever they disagree.",

        "cohorts": {
            "primary_eval": {"n": 181, "definition":
                             "eval-40 x arms A/B/C/D (160) + arm E on the 21 "
                             "native-feedback-eligible eval roots"},
            "full_pool_dev": {"n": 195, "definition":
                              "dev-43 x arms A/B/C/D (172) + arm E on 23 eligible dev roots"},
            "all_branches_built": 376,
            "e_eligible_eval_roots": sorted(e_eligible),
        },

        "seeds": {
            "rule_id": seeds_mod.SEED_RULE_ID,
            "block_base": seeds_mod.BLOCK_BASE,
            "formula": "seed = block_base[block] + index of root_id in sorted(root_ids)",
            "shared_across_arms": True,
            "why_shared": "C-A and D-B are paired within-root contrasts; different "
                          "seeds per arm would make them independent draws",
            "block_1_range": [lo, hi],
            "collision_note": "CoLM's entire seed history lies in 100030..1079030",
        },

        "serving": {
            "model": "Goedel-Prover-V2-8B.Q4_K_M.gguf",
            "backend": "llama.cpp server",
            "n_ctx": 32768,
            "parallel": 1,
            "cont_batching": False,
            "cache_prompt": False,
            "gpu_layers": 999,
            "determinism_reverified_here": True,
            "colm_determinism_does_not_carry_over":
                "CoLM served --parallel 4 at ctx 65536; slot geometry changes the "
                "arithmetic, so Gate 9 was re-run under this configuration",
        },

        "sampler": dict(generate.SAMPLER),
        "generation": {"max_tokens": generate.MAX_TOKENS},

        "policy_surface": {
            "source": "CoLM_Jul2026_MoSpe_Navi/src/mospe_navi.py",
            "verified_byte_identical": True,
            "verify_with": "python scripts/sync_policy.py",
            "official_prompt_sha256": receipts.sha_text(policy.OFFICIAL_PROMPT),
            "prompt_addendum": policy.PROMPT_ADDENDUM,
            "guidance_template_sha256": receipts.sha_text(policy.GUIDANCE_TEMPLATE),
        },

        "prompt_composition": {
            "order": "guidance outermost",
            "A": "OFFICIAL(theorem)",
            "B": "GUIDANCE_BLOCK + OFFICIAL(theorem)",
            "C": "WRAPPER_BLOCK + OFFICIAL(theorem)",
            "D": "GUIDANCE_BLOCK + WRAPPER_BLOCK + OFFICIAL(theorem)",
            "E": "3-turn native format: OFFICIAL(theorem) / prior completion / "
                 "native <error> correction turn",
            "abcd_are_one_user_turn": True,
            "why": "conversation structure is held constant across the 2x2; only E "
                   "changes it, which is why E-A is a positive control and not an "
                   "isolated artifact effect",
            "v7_ordering_is_unbuildable":
                "04 Sec.6 writes theorem + R2 + prior + wrapper + base; the theorem is "
                "embedded inside the base template, so that ordering cannot be built",
        },

        "neutral_prior_attempt_wrapper": {
            "origin": "W1 design decision; v7 names the function but not its wording",
            "sha256": receipts.sha_text(prompts.NEUTRAL_PRIOR_ATTEMPT_WRAPPER),
            "text": prompts.NEUTRAL_PRIOR_ATTEMPT_WRAPPER,
            "constraints": [
                "states the attempt was not accepted, and nothing about why",
                "uniform across all roots -- no per-failure-class wording",
                "does not instruct repair",
            ],
        },

        "guidance": {
            "policy_id": "R2_error_conditioned",
            "source": "cascade_guidance(failure_class, ...) -- mospe_navi.py:2826",
            "r1_is_not_failure_conditioned": "mospe_navi.py:2823",
            "error_class_keyed_roots": 51,
            "truncation_top3_roots": 32,
            "caveat": "on truncated roots cascade_guidance returns nav2_selection[:3], "
                      "which is prompt shrinking rather than error-class keying",
        },

        "anchoring_metric": {
            "metric_id": anchoring.METRIC_ID,
            "normalization_id": anchoring.NORMALIZE_ID,
            "formula": "S = 1 - lev(model_tokens(a), model_tokens(b)) / max(len_a, len_b)",
            "tokenizer": "the serving model's own /tokenize endpoint; no fallback",
            "computed_over": "the entire completion -- comments, prose and malformed "
                             "Lean are NOT stripped",
            "contrasts": {"T0": "mean[S(C,root) - S(A,root)]",
                          "T1": "mean[S(D,root) - S(B,root)]"},
            "interpretation": "proxy for textual anchoring. High S evidences anchoring; "
                              "low S does NOT prove the prior attempt was ignored.",
            "null_band": {k: v for k, v in gates["s04"].items()
                          if k.startswith("null_band")},
        },

        "plain_draw_variance_band": PLAIN_DRAW_BAND,

        "outcome_states": {
            "derivation": "policy.generation_prefilter, verbatim from CoLM",
            "truncated": "finish_reason == length; Lean never runs",
            "format_error": "no usable Lean, or a sorry/admit placeholder",
            "verified": "Lean accepted",
            "lean_failed": "Lean rejected",
            "verifier_wall_zero_not_null":
                "skipped states record 0.0, so 'not spent' never looks like 'not measured'",
        },

        "resource_accounting": {
            "columns": ["model_calls", "completion_tokens", "total_tokens",
                        "prefill_tokens", "decode_tokens", "request_wall_seconds",
                        "verifier_wall_seconds"],
            "prefill_and_decode_kept_separate": True,
            "measured_prefill_tokens_per_second": gates["s07"]["prefill_tokens_per_second"],
            "measured_decode_tokens_per_second": gates["s07"]["decode_tokens_per_second"],
            "measured_ratio": gates["s07"]["prefill_to_decode_ratio"],
        },

        "verification": {
            "backend": "Lean 4 REPL in WSL2 with pinned Mathlib",
            "timeout_seconds": 180,
            "workers": 1,
        },

        "gates": {
            "s03_prompt_diff": gates["s03"],
            "s04_anchoring": {k: v for k, v in gates["s04"].items()
                              if not k.startswith("null_band")},
            "s05_context_capacity": gates["s05"],
            "s06_determinism": gates["s06"],
            "s09_kill_restart": gates["s09"],
            "s10_pilot": gates["s10"],
        },
    }

    print("\n[4/4] writing")
    SPEC.parent.mkdir(parents=True, exist_ok=True)
    text = yaml.safe_dump(spec, sort_keys=True, allow_unicode=True, width=100)
    SPEC.write_text(text, encoding="utf-8", newline="\n")
    sha = receipts.sha_text(text)
    SPEC_SHA.write_text(f"{sha}  frozen_spec.yaml\n", encoding="utf-8", newline="\n")
    print(f"      {SPEC.relative_to(ROOT).as_posix()}  ({len(text)} bytes)")
    print(f"      sha256 {sha}")

    receipts.write(STEP["id"], STEP["title"], STEP["inputs"], STEP["outputs"], {
        "spec_sha256": sha,
        "spec_bytes": len(text),
        "seed_rule": seeds_mod.SEED_RULE_ID,
        "seed_block_1_range": [lo, hi],
        "gates_certified": REQUIRED_GATES,
        "open_decisions_resolved": ["seed_block_2_derivation",
                                    "plain_draw_descriptive_variance_band"],
    })
    print("\n  SPEC FROZEN. The primary run may start:")
    print("     python scripts\\s12_run.py")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
