# Reproducing the W1 analyses

## CPU-only integrity gate

Use Python 3.10 or later. From the repository root:

```powershell
python -m pip install -r requirements.txt
python scripts\verify_artifact.py
python scripts\check_databases.py
```

`verify_artifact.py` opens every SQLite database read-only, runs `quick_check`,
checks cohort sizes and completion status, reconstructs the 978-completion paper
denominator, verifies the frozen-spec digest, checks that no SQLite sidecar is in
the file manifest, and scans text files for the private path or identity strings configured in
the script. Do not regenerate the manifest before this check: the shipped manifest
is the digest record being verified. `build_file_manifest.py` is a maintainer tool
used only when intentionally freezing a new artifact revision.

## Main analysis sequence

```powershell
python scripts\s17_statistical_tests.py
python scripts\s18_failure_class_analysis.py
python scripts\s19_coprimary_interaction.py
python scripts\s20_reviewer_analyses.py
python scripts\s23_cprime_analysis.py --block 1
python scripts\s23_cprime_analysis.py --block 2
python scripts\s24_line_level_similarity.py
python scripts\s26_outcome_decomposition.py
python scripts\s27_interaction_resolution.py
python scripts\s37_restart_verify.py
python scripts\s38_restart_analysis.py
python scripts\s48_draw_diversity.py
python scripts\s50_eprime_analysis.py
python scripts\s52_armf_analysis.py
python scripts\s34_agent_loop_replay.py
python scripts\s35_allocation_analysis.py
python scripts\s58_mediation_and_ceiling.py
python scripts\build_assets.py
```

`s14_anchoring_analysis.py`, `s25_proof_body_similarity.py`, and
`s39_restart_anchoring.py` additionally need the model tokenizer endpoint on
`http://127.0.0.1:8080`. Their frozen outputs are supplied under `audit/`; they
should not be rerun without that endpoint because the tokenizer-dependent fields
would otherwise be unavailable.

Analysis scripts write their named outputs under `audit/`. Their integrity
assertions fail closed on missing roots, mixed cohorts, incomplete branches, or
an invalid pairing.

## Generation

Generation is not necessary for result reproduction. To regenerate completions,
edit only the machine-specific paths in `configs/primary.json`, start a compatible
llama.cpp server, and provide the WSL Lean workspace described in
`ENVIRONMENT.md`. The builders and runner are resumable; do not overwrite the
shipped databases when testing regeneration.
