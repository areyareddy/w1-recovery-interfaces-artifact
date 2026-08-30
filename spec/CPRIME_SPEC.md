# Arm C′ — analysis specification, frozen before generation

**Status when this file was written:** `data/cprime.sqlite` holds 40 branches, all
`pending`. No C′ completion exists. Nothing below was chosen after seeing a C′ outcome.

| | |
|---|---|
| **canonical donor-map sha256** | `ea0ea22a3196e841c7cac9df702cd0fc26cbefab73e6e15dcfb89546ce167a4b` |
| prompts sha256 (`data/cprime_prompts.jsonl`) | `5b009fe19829558f11a0e2ce6fec438edac96a2bf218c379ff7758ea7a421f8b` |
| builder | `scripts/s21_build_cprime.py` |
| analyser | `scripts/s23_cprime_analysis.py` |
| pairing audit (descriptive) | `audit/cprime_pairing.csv` — sha256 `7ff1017635a55dc1f28aea6ee2f3b9d94ad11be15d9382fbd74b75b393adcdc2` |

Both hashes are printed by the builder. If either differs at analysis time, the arm was
rebuilt and this specification no longer describes what ran.

**What the donor-map hash covers.** It is `sha256` over the sorted `root->donor` lines —
the pairing itself — and **not** over the bytes of `audit/cprime_pairing.csv`. The CSV is a
descriptive audit file carrying formatting-sensitive columns; digesting it would make the
frozen identity brittle to a column rename. Running `sha256sum` on the CSV therefore yields
a different value (given above), which is expected and is not a rebuild. The builder prints
both, each labelled.

## 1. Registration status

Arm C′ is **post hoc with respect to the original experiment**. It is not part of the
pre-registered 2×2 and must never be described as registered. It is **pre-specified with
respect to its own outcomes**: this file, the builder, and the analyser were all written and
frozen while all 40 branches were still `pending`.

The paper must state both halves of that sentence.

## 2. What C′ is

    A  = BASE(theorem)
    C  = WRAPPER(own failed attempt)       + BASE(theorem)
    C′ = WRAPPER(another root's attempt)   + BASE(theorem)

Held constant between C and C′ for a given root: the theorem, the wrapper text, the
conversation structure (one user turn), the seed, the sampler, the token budget, and the
serving configuration. The only thing that varies is **whose** failed attempt occupies the
slot.

## 3. Donor assignment

Partition the 40 evaluation roots into **incomplete** (truncated fragment) and **complete**
(finished but rejected proof), sort each stratum by the token length of its own prior
attempt, and swap adjacent pairs within the stratum. Odd strata rotate one triple, placed at
the position minimising (max delta, sum delta).

The stratum is binary rather than the full three-way `coarse_failure_group` because exactly
two donor properties reach the model through the prompt:

1. whether the donor is a finished proof or a truncated fragment;
2. how much context it adds.

Both are matched by this rule. The localized/diffuse distinction is a property of the
original compiler diagnosis, and the C′ wrapper carries no error text, so it is invisible in
the stimulus. Adding it as a third stratum would buy nothing the model can see and would
force a 4520-token (46%) mismatch on one pair, because `localized_complete` holds only 10
roots spanning 1852–9899 and its longest root would have no acceptable partner inside the
group. That trade weakens C′ as a long-context control, which is the arm's purpose.

Realised quality (from `audit/cprime_pairing.csv`):

| | |
|---|---|
| donors crossing incomplete / complete | **0 / 40**, asserted at build time |
| donors crossing localized / diffuse | 12 / 40 — descriptive sensitivity, not part of the estimand |
| donors crossing a fine failure class | 16 / 40 — descriptive; no error text is shown in C′ |
| \|donor − own\| token delta | median 61, p90 791, **max 2001** |
| relative delta | median 1.3%, max 20.2%; none above the 25% tolerance |

(The median was first recorded as 87. That was the upper of the two central values, 35 and
87; the conventional median of the 40 gaps is 61. A printed descriptive only — the pairing
and both hashes above are unchanged, and were re-verified after the fix.)

The two worst-case numbers are both forced by the length distribution rather than by the
pairing rule. All 15 incomplete attempts are exactly 12288 tokens, so that stratum matches
perfectly. Among the 25 complete attempts, 2001 tokens is the smallest achievable worst-case
gap over any one-to-one derangement of those lengths.

Localized/diffuse balance is reported as a **descriptive sensitivity analysis**. If C − C′
is informative, the analysis is repeated on the 28/40 same-group pairs and the difference
reported; that repetition is descriptive and enters no test family.

## 4. Primary contrasts

Two, both paired within root, both on the binary verification outcome, both against
block 1 of `primary_eval`:

| contrast | question |
|---|---|
| **C′ − A** | the cost of long, irrelevant text in a non-native single-turn wrapper — generic long-context and off-format degradation |
| **C − C′** | the cost of the **specific** rejected trajectory for this theorem |

`C − A` is reported alongside as a reference line only. It is already published under its
own within-block family and is not re-tested here.

## 5. Tests, estimates, intervals

- **Test:** exact McNemar (binomial on the discordant pairs, two-sided). Discordant counts
  `b` and `c`, and the concordant-positive count, are reported for every contrast.
- **Estimate:** the mean within-root difference, `(b − c) / n`.
- **Interval:** 95% percentile bootstrap over 20,000 resamples of the **roots**, the
  independent unit, seeded at 20260828, matching every other interval in the paper.

## 6. Multiplicity

The Holm family is **`{C′ − A, C − C′}`** — the two new tests C′ exists to answer. Size 2.

`C − A` is excluded from the family. It belongs to the previously reported within-block
family and folding it in here would penalise a result twice for having been looked at once.
This is a judgement call and is stated as one.

## 7. Interpretation, fixed in advance

| observed | reading |
|---|---|
| C − A large, C′ − A ≈ 0 | the deficit is specific to the rejected trajectory; the paper's mechanism survives |
| C′ − A ≈ C − A | the deficit is generic long-context or off-format cost, **not** prior-attempt content; the paper must be reframed around interface format |
| both intermediate | report the split; do not name a single mechanism |

A null C − C′ at n = 40 is **not** evidence of equivalence. C − C′ is a single paired
difference, not an interaction, so §4.3's interaction resolution does not transfer to it;
its own resolution will be computed from the realised discordant counts by the same
root-resampling method as `scripts/s27_interaction_resolution.py`, and reported alongside
the estimate. Any null is reported as unresolved, with its interval.

## 8. Anchoring side-analysis (secondary, descriptive)

C′ supplies two reference texts where C had one:

- `S(C′, donor)` — does the model copy whatever text occupies the slot?
- `S(C′, own)` — the model never saw its own prior attempt in this arm, so similarity above
  the unrelated-root null band is convergence on the theorem, not copying.

These are descriptive. They are not in the Holm family and carry no confirmatory claim.

## 9. Stopping rule

One block of 40. A second seed block is run **only** if the first is directionally
important but inconclusive, and if it is run, that decision and its date are recorded here
before it starts.

**Block 2 was run.** Trigger, evaluated on block 1 only: `C - C'` = -0.125, exact McNemar
p = .125, Holm-adjusted p = .250, 95% interval [-0.250, 0.000] touching zero, and an
observed effect below its own 80% MDE of 0.177 -- directionally important and inconclusive,
which is the condition above. Generation ran 2026-08-29 07:37Z-08:23Z.

The block-2 payloads are byte-identical to block 1: `scripts/s30_build_cprime_block2.py`
re-asserts the canonical donor-map digest and the frozen prompts digest, and asserts that
the set of `payload_sha256` values is unchanged, before staging anything. **Only the seed
differs** -- each root takes its own `eval_block2` seed, read from `runs.sqlite` rather
than recomputed, so A, C and C' stay seed-matched within root in both blocks.

The two blocks are **the same 40 theorems** and are reported separately. They are not 80
roots, and no contrast crosses a seed boundary: each block's C' is paired against the A
and C arms of its own block.

**Provenance defect, disclosed.** This subsection was written on 2026-08-29 *after*
generation, not before it as the paragraph above requires. The decision itself was
recorded before generation, but in the wrong file: the docstring of
`scripts/s30_build_cprime_block2.py`, written 07:35:32Z, six minutes before the first
block-2 branch at 07:41:59Z, states the trigger, the block-1 numbers above, and the
seed derivation. That docstring also asserts that the decision "is recorded in
spec/CPRIME_SPEC.md before this script runs", which was **not true** -- this file was last
written at 07:14Z and did not carry it. What is affected is the location of the record,
not its timing: the trigger numbers are block-1 quantities that were already published in
`audit/cprime_analysis.json`, and no block-2 outcome existed when `s30` was written.
Readers who require a pre-generation artefact should read the `s30` docstring, whose
mtime is checkable, rather than this file.

## 10. Change log

| when | what |
|---|---|
| 2026-08-29, after block-2 generation | Recorded the block-2 decision and its trigger in
section 9, and disclosed there that section 9's "recorded here before it starts"
requirement was met in the wrong file (`s30`'s docstring, pre-generation) rather than in
this one. Nothing about the analysis changed: the contrasts, the tests, the Holm family
and the interpretation table are as frozen. `scripts/s23_cprime_analysis.py` gained a
`--block` selector and now re-asserts the frozen donor-map digest at analysis time as the
header of this document already required; run with no arguments it reproduces
`audit/cprime_analysis.json` exactly, verified by diff. |
| 2026-08-29, after generation | Relabelled the `pairing sha256` row to
**canonical donor-map sha256** and recorded the CSV's own digest beside it. The frozen
value is unchanged and was re-verified as `ea0ea22a…`; the pairing, the prompts, and all 40
generated branches are untouched. This is a naming correction only: the old label sat two
rows above a row naming `audit/cprime_pairing.csv`, so an auditor could reasonably have
hashed that file and concluded the arm had been rebuilt. Also added, in the same pass, the
two analyses this document promised but `s23` did not emit: the same-coarse-group
sensitivity (section 3) and the contrast resolution (section 7). Neither adds a test to any
family. |
| 2026-08-28, before generation | First frozen version used three-group stratification. Superseded the same evening, still before generation, by the binary incomplete/complete rule: the three-group version forced a 4520-token mismatch on one pair to match a label the model cannot see. Both versions were written while all 40 branches were `pending`; no C′ outcome existed under either. Superseded hashes: pairing `fee733ae…`, prompts `6afaa0ef…`. |
