# Restart-permissive arms — analysis specification

## 0. Registration status — read this first

**This is an EXPLORATORY ROBUSTNESS analysis. It is not confirmatory and must never be
described as pre-registered.** The paper must say so wherever these numbers appear.

Two halves, and both must be stated:

- **The design was recorded before generation.** `scripts/s32_build_restart.py` was written
  2026-08-29 00:40 local; the first restart branch was generated 12:20:44Z. Its docstring
  fixes the three arms, names `C-R vs C'-R` as the contrast the experiment exists for, and
  names the comparison against the original `C vs C'` as the question of whether the commit
  instruction was amplifying the effect. That file's mtime is checkable.
- **The statistical plan — this file — was written after generation**, on 2026-08-29, while
  no restart outcome had been read. `scripts/s37_restart_verify.py` was run first and
  deliberately reads no verification result, so the arms could be validated structurally
  without opening an outcome. That is weaker than pre-registration and is disclosed as such.
  What it does buy: the contrasts, the tests, the multiplicity and the interpretation table
  below were all fixed before anyone saw a restart number, so no contrast was selected for
  looking good.

No equivalence claim is available anywhere in this document.

## 1. What the arms are

W1 limitation (7): every arm's base prompt carries

> Commit to your first derivation — do not restart the analysis or re-derive earlier steps
> if you notice a possible error; fix it in place and proceed directly to the Lean 4 code.

In arms C and C′ the "earlier derivation" in context is a *rejected proof*, so the
instruction plausibly amplifies retention there specifically, and the commitment reading is
then partly a restatement of an instruction rather than a finding.

|  | commit (original) | restart permitted |
|---|---|---|
| fresh | A | **A-R** |
| mismatched attempt | C′ | **C′-R** |
| own rejected attempt | C | **C-R** |

One audited substitution of that sentence, nothing else. Verified in
`audit/restart_verify.json`: 120/120 restart payloads differ from their original by exactly
that sentence, and reversing the substitution restores the original payload digest
byte-for-byte. Arms are root- and seed-matched to their own originals over the same 40
block-1 evaluation roots, at the same 12,288-token cap.

## 2. Contrasts

Paired within root, on the binary verification outcome, over the 40 block-1 roots.

| contrast | question |
|---|---|
| **C-R − C′-R** | does trajectory-specific harm survive when restart is explicitly permitted? |
| **C′-R − A-R** | the generic long-context / off-format cost under restart permission |
| **(C-R − C′-R) − (C − C′)** | did the commit instruction amplify the effect? |

`A-R − A` is a rate anchor and is reported as a reference line only.

## 3. Tests, estimates, intervals

- **Test:** exact McNemar (binomial on the discordant pairs, two-sided).
- **Estimate:** mean within-root difference, `(b − c) / n`.
- **Interval:** 95% percentile bootstrap over 20,000 resamples of the **roots**, seed
  20260828 — the same as every other interval in both papers.
- **The interaction** in row 3 is a difference of two paired differences. Its interval comes
  from the per-root contrast `w_i = (C-R_i − C′-R_i) − (C_i − C′_i)`, whose variance carries
  the full four-arm covariance exactly, by the root-resampling method of
  `scripts/s27_interaction_resolution.py`. Its resolution — analytic and simulated 80% MDE —
  is reported alongside it, because an underpowered interaction is the expected outcome at
  n = 40 and must not be read as evidence of no amplification.

## 4. Multiplicity

Holm family = **{C′-R − A-R, C-R − C′-R}**, size 2. This deliberately mirrors
`spec/CPRIME_SPEC.md` §6 so the restart triple and the original triple are directly
comparable.

The interaction is **not** in the family. It is the robustness statement the arms exist for
and is reported with its interval and its resolution, descriptively. Folding it in would
penalise the two contrasts for a question asked of their difference. This is a judgement
call and is stated as one.

## 5. Interpretation, fixed in advance

| observed | reading |
|---|---|
| C-R − C′-R negative and resolved, interaction ≈ 0 | trajectory-specific harm survives restart permission; the commit instruction was **not** the mechanism, and limitation (7) is answered |
| C-R − C′-R ≈ 0, interaction negative | the original effect depended on the commit instruction; the paper's mechanism claim must be narrowed to the committed-interface setting |
| C-R − C′-R negative and resolved, **interaction under-resolved** | trajectory-specific harm survives restart permission, so limitation (7)'s confound does not account for the effect. The interaction is under-resolved, so **how much** the instruction contributed is not estimable and must not be reported as zero |
| both under-resolved | report as under-resolved with intervals; **name no mechanism**, and leave limitation (7) standing |
| C-R − C′-R negative, interaction also negative | harm survives but is attenuated; report both, and say the instruction contributes without being necessary |

At n = 40 the interaction is very likely under-resolved. That is the expected outcome, it is
reported as such, and it is **not** evidence that the instruction had no effect.

## 6. Cohort separation

The restart arms are a **third** set of observations on the same 40 theorems, alongside C′
block 1 and C′ block 2. They are never pooled with either, and never counted as additional
independent roots. Every contrast in §2 is within the restart triple except the interaction,
which pairs restart against original within the same root by construction.

## 7. Change log

| when | what |
|---|---|
| 2026-08-29, after the first analysis run | Added the "harm resolved, interaction under-resolved" row to section 5. The original table had four rows and none of them covered that combination, so the analyser fell through to a row asserting the interaction was ~0 -- which section 3 of this same document explicitly forbids reading from an under-resolved interaction. The gap was in the table, not in the data; no contrast, test or family changed, and the added row states a weaker conclusion than the one it replaced. |
| 2026-08-29, after generation, before any outcome was read | First version. Design provenance is `scripts/s32_build_restart.py` (pre-generation); this statistical plan is post-generation and the analysis is labelled exploratory throughout. |
