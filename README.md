# Recovery interfaces and prior-attempt anchoring in Lean proof generation

Artifact for **Failed Proofs Are Sticky: Rejected-Proof Perseveration in Lean
Recovery** by Arya Srikar Reddy, Workshop on Who Verifies the Agents? Toward
Reliable Agent Development, NeurIPS 2026.

The study tests what happens when a verifier-guided recovery call receives the
model's rejected proof, a matched proof from another theorem, native Lean
feedback, or permission to restart. It extends the predecessor paper *Proof
Yahtzee: From Prompting to Scheduling -- Failure Signals for Token-Efficient
Retries in Frozen Lean Provers*, accepted at COLM 2026 and currently unpublished;
its manuscript is included under `prior_work/`.

## What is included

| component | records | role in the paper |
|---|---:|---|
| `data/runs.sqlite` | 536 | core A--E factorial, two seed blocks and development cohort |
| `data/cprime.sqlite` | 40 | mismatched-attempt control, block 1 |
| `data/cprime_b2.sqlite` | 40 | mismatched-attempt control, block 2 |
| `data/restart.sqlite` | 120 | restart-permissive A/C/C-prime arms |
| `data/eprime.sqlite` | 21 | one-turn native-feedback arm E-prime |
| `data/armf.sqlite` | 21 | feedback-without-attempt arm F |
| held-out rows in the allocation databases | 200 | 80 Split-2 and 120 Split-3 completions |

These components sum to the paper's 978 analyzed completions. The allocation
databases also retain 215 development rows (86 Split-2 and 129 Split-3); they are
descriptive and are not counted in 978.

The repository additionally contains all rendered prompts, the 83 frozen root
artifacts, raw completions and Lean receipts in SQLite, frozen specifications,
analysis outputs, paper-facing computed results, and the scripts that generated
or analyzed each later control.

## Start here

1. Read `ARTIFACT_MANIFEST.md` for the claim-to-file map.
2. Read `REPRODUCE.md` for CPU-only verification commands.
3. Run `python scripts/verify_artifact.py` for the read-only integrity gate.
4. Verify individual bytes against `FILE_MANIFEST_SHA256.csv`.

## Release-export adjustments

The scientific records, prompts, frozen specifications, and database payloads are
unchanged. Three non-scientific path adjustments make the code self-contained:

- `s58_mediation_and_ceiling.py` reads the included predecessor ledger instead of
  an adjacent local checkout;
- `wsl_lean_repl.py` resolves `lake` from the WSL login environment instead of a
  user-specific absolute path; and
- `configs/primary.json` uses neutral example paths while preserving every frozen
  sampler, context, budget, and timeout setting.

The original frozen-spec digest remains byte-valid:
`cd8317bef3e3523a0842674219b2b0e5760b685f43686cc9d21381322885281d`.

## Scope

The repository supports audit and analysis without a GPU. Repeating generation
requires the separately obtained Goedel-Prover-V2-8B Q4_K_M model, a compatible
llama.cpp server, and the pinned Lean/mathlib environment described in
`ENVIRONMENT.md`. Model weights are not redistributed.
