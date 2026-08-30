# Arm C′ — seed block 2 result

Run 2026-08-29 after the system restart. Analysis is `spec/CPRIME_SPEC.md`, unchanged;
`scripts/s23_cprime_analysis.py --block 2`; output `audit/cprime_b2_analysis.json`.

**Block 2 was the pre-registered §9 trigger firing, not a new experiment.** Block 1 left
`C − C′` at −0.125, p = .125, Holm .250, interval touching zero and below its own MDE:
directionally important and inconclusive, which is the condition §9 fixed in advance.

Payloads are byte-identical across the two blocks — same donor map, same wrapper, same
base prompt. **Only the seed differs.** Both blocks are the **same 40 theorems**. They are
reported separately and are **not 80 roots**.

## Verification

Verified counts, out of 40: **A 9, C 1, C′ 11** (block 1 was A 9, C 2, C′ 7). Arm A
reproduces 9/40 in both blocks.

| contrast | block 1 | block 2 | family |
|---|---|---|---|
| **C′ − A** | −0.050 [−0.175, +0.075], p = .688, Holm .688 | **+0.050 [−0.075, +0.175], p = .688, Holm .688** | Holm, size 2 |
| **C − C′** | −0.125 [−0.250, 0.000], p = .125, Holm .250 | **−0.250 [−0.400, −0.125], p = .0020, Holm .0039** | Holm, size 2 |
| C − A | −0.175 [−0.300, −0.075], p = .0156 | −0.200 [−0.325, −0.075], p = .0078 | reference only |

Discordant pairs, block 2: C′−A is 4 vs 2; C−C′ is **0 vs 10** — one-directional, no root
verified under C that failed under C′.

## Reading, against the interpretation table frozen in §7

Spec §7 row: *"C − A large, C′ − A ≈ 0 → the deficit is specific to the rejected
trajectory; the paper's mechanism survives."*

Both blocks land in that row. C′ − A is null in both and **changes sign** between them
(−0.050, +0.050), which is what a true zero looks like at this n; it is not a
small-consistent effect. C − C′ is negative in both and is now **resolved** in block 2:
observed 0.250 against an analytic 80% MDE of 0.192 and a simulated 0.200, with a Holm
p of .0039 and an interval excluding zero.

So the deficit is **not** generic long-context or off-format cost. C′ carries the same
wrapper, the same format, the same length distribution and an equally irrelevant prior
attempt, and it verifies as often as plain A — slightly more often here. What costs
verification is the model's **own rejected trajectory for that specific theorem**.

Per `HANDOFF.md` §3.2 this is the "C′≈A and C<C′" branch: **the current title survives**;
no reframe around interface format is required.

## Resolution and limits

| contrast | block | SE | MDE analytic / simulated | observed | verdict |
|---|---|---|---|---|---|
| C − C′ | 1 | 0.063 | 0.177 / 0.19 | 0.125 | under-resolved |
| C − C′ | 2 | 0.069 | 0.192 / 0.20 | 0.250 | **resolved** |
| C′ − A | 1 | 0.061 | 0.170 / 0.18 | 0.050 | under-resolved |
| C′ − A | 2 | 0.061 | 0.170 / 0.18 | 0.050 | under-resolved |

**C′ − A is a null that is not an equivalence claim**, in either block. At n = 40 the arm
cannot resolve anything below ≈0.17, so the honest statement is that no C′−A difference is
detectable at this resolution, with the interval given. Spec §7 says this explicitly and
the paper must not upgrade it.

Same-coarse-group sensitivity (descriptive, no test family): C − C′ is −0.250 over all 40
pairs and −0.179 over the 28 same-group pairs — direction preserved, magnitude attenuated.
C′ − A is +0.050 and +0.036.

## What is missing

**The anchoring side-analysis (§8) did not run for block 2.** It needs the tokenizer at
`127.0.0.1:8080`, and the llama-server did not survive the restart. The section is
secondary and descriptive and carries no confirmatory claim, so the primary result above
does not depend on it; block 1's anchoring numbers are intact in
`audit/cprime_analysis.json`. To complete it: start the server, then
`python scripts\s23_cprime_analysis.py --block 2`.

## Provenance defect, disclosed

§9 requires the block-2 decision to be recorded in `spec/CPRIME_SPEC.md` before generation.
It was not. It was recorded pre-generation in the docstring of
`scripts/s30_build_cprime_block2.py` (written 07:35:32Z; first block-2 branch 07:41:59Z),
which also wrongly asserts the spec already carried it. The record's **location** was
wrong, not its timing — the trigger numbers are block-1 quantities already published in
`audit/cprime_analysis.json`, and no block-2 outcome existed when `s30` was written. Now
disclosed in `spec/CPRIME_SPEC.md` §9 and its change log, dated 2026-08-29, not backdated.

## Changes made

- `scripts/s23_cprime_analysis.py` — added `--block` / `--out`; added the analysis-time
  re-assertion of the frozen donor-map digest that the spec header already required and
  the script never performed. Run with no arguments it reproduces
  `audit/cprime_analysis.json` exactly (verified by diff; only the four new provenance
  keys differ).
- `Paper_Working/W1_NeurIPS_Draft_v1/scripts/build_macros.py` — emits the C′ macro set for
  both blocks; block 2 under a `CpBlockTwo` prefix. Block-1 macro names and values are
  unchanged. Anchoring emit is now guarded, so a missing section drops macros and fails
  the LaTeX build loudly instead of printing a stale number. 498 → 540 macros, 0 changed,
  0 removed.
- `s22` number audit: 32/32 matched, 0 unmatched.

Backups: `Backup/s23_cprime_analysis.py.pre_block2`, `Backup/CPRIME_SPEC.md.pre_block2`,
`Backup/build_macros.py.pre_block2`, `Backup/computed_macros.tex.pre_block2`.
