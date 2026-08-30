# Artifact manifest

This document maps the paper's result families to immutable inputs and analysis
commands. Every command is run from the repository root.

| result family | input database(s) | specification | analysis |
|---|---|---|---|
| core factorial and textual anchoring | `runs.sqlite` | `frozen_spec.yaml` | `s14`, `s17`, `s19` |
| failure-class and reviewer analyses | `runs.sqlite` | frozen core specification | `s18`, `s20` |
| first-error and proof-body reuse | `runs.sqlite` | frozen core specification | `s24`, `s25`, `build_assets` |
| terminal-state decomposition | `runs.sqlite` | frozen core specification | `s26` |
| registered-interaction resolution | `runs.sqlite` | frozen core specification | `s27` |
| mismatched attempt C-prime | `runs.sqlite`, `cprime.sqlite`, `cprime_b2.sqlite` | `CPRIME_SPEC.md` | `s23 --block 1/2` |
| restart permission | `runs.sqlite`, `cprime.sqlite`, `restart.sqlite` | `RESTART_SPEC.md` | `s37`, `s38`, `s39` |
| two-seed draw diversity | `runs.sqlite`, both C-prime databases | frozen/core and C-prime specifications | `s48` |
| native feedback E-prime | `runs.sqlite`, `eprime.sqlite` | `EPRIME_SPEC.md` | `s50` |
| feedback without attempt F | `runs.sqlite`, `eprime.sqlite`, `armf.sqlite` | `ARM_F_SPEC.md` | `s52` |
| fixed-budget allocation | `runs.sqlite`, both allocation databases | `ALLOCATION_SPEC.md` | `s34`, `s35` |
| completion-length mediation and corpus ceiling | `runs.sqlite`, predecessor attempt ledger | descriptive analysis | `s58` |

## Generated-record builders

The builders are included for prompt and schema audit; rerunning them is not needed
to reproduce reported statistics and requires the model server and Lean verifier.

- Core: `s11_freeze_spec.py`, `s12_run.py`, `s13_seed_block2.py`
- C-prime: `s21_build_cprime.py`, `s30_build_cprime_block2.py`
- Allocation: `s31_build_allocation.py`
- Restart: `s32_build_restart.py`
- E-prime: `s49_build_eprime.py`
- F: `s51_build_armf.py`

## Denominator ledger

`536 + 40 + 40 + 120 + 21 + 21 + 80 + 120 = 978` paper completions.
The two allocation databases contain 215 additional development rows that are
retained for transparency but excluded from that total.
