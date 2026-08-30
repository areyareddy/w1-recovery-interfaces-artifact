"""The pipeline manifest -- single source of truth for what the steps are, in order.

Nothing here executes. `scripts/status.py` reads it to render progress; each step
script imports STEPS only to look up its own declared inputs/outputs so the receipt it
writes cannot drift from what status.py checks.

Gate numbers refer to Updated_Proposal_V_7 `05` unless MASTER_CORRECTION.md overrides
them. Where the two disagree, MASTER_CORRECTION.md wins.
"""

from __future__ import annotations

STEPS: list[dict] = [
    {
        "id": "s00",
        "title": "Freeze the 83-root set",
        "gate": "G1",
        "script": "scripts/build_roots.py",
        "inputs": [],  # reads the CoLM tree, which is read-only and outside this repo
        "outputs": ["data/roots.jsonl", "artifacts/roots", "audit/e_eligibility.csv",
                    "audit/r2_guidance_audit.csv", "audit/step1_freeze.json"],
        "blurb": "extract stage-one failures, freeze R2 guidance, classify E-eligibility",
    },
    {
        "id": "s01",
        "title": "Port + render R2 guidance",
        "gate": "G2",
        "script": "scripts/s01_render_guidance.py",
        "inputs": ["data/roots.jsonl", "audit/step1_freeze.json", "src/policy.py"],
        "outputs": ["data/guidance_render.jsonl", "audit/guidance_render.csv"],
        "blurb": "concrete_guidance_prompt ported verbatim; render + hash per root",
    },
    {
        "id": "s02",
        "title": "Prompt builder, arms A-E",
        "gate": "G4",
        "script": "scripts/s02_build_prompts.py",
        "inputs": ["data/roots.jsonl", "data/guidance_render.jsonl", "src/policy.py",
                   "src/prompts.py", "src/goedel_native.py"],
        "outputs": ["data/prompts.jsonl"],
        "blurb": "guidance-outermost composition; rename goedel_native arms to A-E",
    },
    {
        "id": "s03",
        "title": "Prompt-diff audit",
        "gate": "G5",
        "script": "scripts/s03_prompt_diff_audit.py",
        "inputs": ["data/prompts.jsonl", "artifacts/roots", "src/prompts.py"],
        "outputs": ["audit/prompt_diff_audit.csv"],
        "blurb": "A->B guidance only, A->C artifact only, B->D artifact only, C->D guidance only",
    },
    {
        "id": "s04",
        "title": "Freeze anchoring metric",
        "gate": "G6",
        "script": "scripts/s04_anchoring_metric.py",
        "inputs": ["data/roots.jsonl", "artifacts/roots", "src/anchoring.py"],
        "outputs": ["audit/anchoring_unit_gate.csv"],
        "blurb": "server /tokenize + rapidfuzz edit ratio; synthetic unit gate",
    },
    {
        "id": "s05",
        "title": "Context capacity check",
        "gate": "G8",
        "script": "scripts/s05_context_capacity.py",
        "inputs": ["data/prompts.jsonl", "data/guidance_render.jsonl"],
        "outputs": ["audit/context_capacity.csv"],
        "blurb": "every arm-D prompt + 12288 max_tokens must fit 32768; no elision rule",
    },
    {
        "id": "s06",
        "title": "Determinism check",
        "gate": "G9",
        "script": "scripts/s06_determinism.py",
        "inputs": ["data/prompts.jsonl", "src/generate.py"],
        "outputs": ["audit/determinism.json"],
        "blurb": "same seed + same prompt -> same completion under the frozen serving policy",
    },
    {
        "id": "s07",
        "title": "Runtime projection",
        "gate": "-",
        "script": "scripts/s07_runtime_projection.py",
        "inputs": ["audit/determinism.json", "audit/context_capacity.csv"],
        "outputs": ["audit/runtime_projection.csv"],
        "blurb": "measured tok/s -> wall-clock estimate for 181 and 353 branches",
    },
    {
        "id": "s08",
        "title": "SQLite job store + runner",
        "gate": "-",
        "script": "scripts/s08_init_db.py",
        "inputs": ["data/prompts.jsonl"],
        "outputs": ["data/runs.sqlite"],
        "blurb": "one row per branch, resumable, records all seven W2 resource columns",
    },
    {
        "id": "s09",
        "title": "Kill/restart resume test",
        "gate": "G10",
        "script": "scripts/s09_kill_restart.py",
        "inputs": ["src/runner.py", "scripts/s12_run.py"],
        "outputs": ["audit/kill_restart.json"],
        "blurb": "SIGKILL mid-run, restart, no duplicate and no lost branch",
    },
    {
        "id": "s10",
        "title": "Pilot on the 13 excluded roots",
        "gate": "-",
        "script": "scripts/s10_pilot.py",
        "inputs": ["src/runner.py", "scripts/pilot_common.py"],
        "outputs": ["audit/pilot_summary.json", "data/pilot_prompts.jsonl"],
        "blurb": "end-to-end rehearsal on roots outside dev-43 and eval-40",
    },
    {
        "id": "s11",
        "title": "Freeze the spec",
        "gate": "G11",
        "script": "scripts/s11_freeze_spec.py",
        "inputs": ["data/prompts.jsonl", "audit/prompt_diff_audit.csv"],
        "outputs": ["spec/frozen_spec.yaml", "spec/frozen_spec.sha256"],
        "blurb": "seed-block-2 rule + plain-draw band must be decided BEFORE this runs",
    },
    {
        "id": "s12",
        "title": "Primary run: 160 A-D + 21 E",
        "gate": "-",
        "script": "scripts/s12_run.py",
        "inputs": ["spec/frozen_spec.sha256"],
        "outputs": ["data/runs.sqlite"],
        "blurb": "eval-40 x A/B/C/D = 160, then E on the 21 native-feedback roots = 181",
        "total": 181,
    },
]

BY_ID = {s["id"]: s for s in STEPS}
