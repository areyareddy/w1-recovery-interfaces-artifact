# Frozen execution environment

## Model serving

- GPU: NVIDIA GeForce RTX 4090, 24 GB
- Model: `Goedel-Prover-V2-8B.Q4_K_M.gguf`
- Model SHA-256: `919203ed088d6260fbbe124688ca04cb3e213cf63a9ed35346c69e4bec914c02`
- Backend: llama.cpp commit `2969d6d15d67a08e7b83f26164b15350c79c5248`
  (reported build `b1-2969d6d`)
- Context: 32,768 tokens, one slot
- Prompt cache: disabled
- Continuous batching: disabled
- Sampler: temperature 0.7, top-p 0.95, top-k 40, min-p 0.05
- Main completion cap: 12,288 tokens

## Verification

- WSL distribution: Ubuntu
- Lean: 4.9.0-rc1, commit `be6c4894e0a6`
- Lake: 5.0.0-be6c489
- mathlib checkout: `2f65ba7f1a9144b20c8e7358513548e317d26de1`
- Verifier timeout: 180 seconds
- Verification workers: 1 (serial)

Machine-specific source paths in `configs/primary.json` have been normalized for
portable artifact release. This changes no prompt, seed, sampler, context, budget,
completion, or verifier result.
