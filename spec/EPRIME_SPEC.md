# Arm E′ — native correction content in one turn. Analysis specification, frozen before generation.

**Status when this file was written:** `data/eprime.sqlite` does not exist. No E′ prompt has
been staged and no E′ completion exists. Nothing below was chosen after seeing an E′ outcome.

| | |
|---|---|
| builder | `scripts/s49_build_eprime.py` |
| runner | `scripts/s12_run.py --blind` |
| cohort | `eval_eprime` |
| database | `data/eprime.sqlite` (separate from `runs.sqlite`, on purpose — see §7) |
| server config | `configs/primary.json` (single slot, `--no-cache-prompt`, ctx 32768) |

---

## 1. The objection this arm exists to answer

A reviewer of the W1 draft raised, and the paper now states in its own voice (§6 and
limitation 1):

> Goedel-Prover-V2 is trained for verifier-guided self-correction, so arm C withholds
> precisely the signal this checkpoint was tuned to consume. The C−A deficit is therefore
> consistent both with anchoring on the rejected trajectory and with the model being
> off-distribution when shown an attempt stripped of its diagnosis.

Arm C shows the failed proof and says nothing about why it failed — deliberately, because
that is what makes C an artifact-presence manipulation. The objection is that this makes C
an unfair interface for *this* model rather than a clean isolation of prior-attempt access.

**E′ supplies the missing diagnosis and changes nothing else that can be held fixed.**

## 2. Construction

E′ is a **single user turn**, in the same family as A/B/C/D:

```
E' = EPRIME_WRAPPER(prior attempt) + CORRECTION_TURN(native errors) + OFFICIAL(theorem)
```

- `OFFICIAL(theorem)` is byte-identical to arm A's whole prompt.
- The `<previous_attempt>` segment is byte-identical to arm C's.
- `CORRECTION_TURN(...)` is **byte-identical to arm E's third user turn** — Goedel's own
  `generate_correction_prompt` text, unmodified.
- `EPRIME_WRAPPER` is arm C's frozen wrapper with exactly one clause changed: C's
  "with no information about why it was not accepted" becomes "together with the compiler
  output it produced", because in E′ the first wording would be false.

That one clause is an unavoidable difference. It is disclosed here rather than hidden: you
cannot add the diagnosis while still announcing that no diagnosis is present.

**Arm E's existing three-turn path is not touched.** `prompts.arm_messages("E", ...)` and
`prompts.ARMS` are unchanged, so no A/B/C/D/E prompt changes by one byte. E′ is staged by a
separate builder into a separate database, as C′ and the restart arms were.

## 3. Eligibility — fixed, and not a sampling choice

E′ requires a real compiler error, so it is built **only** where
`feedback_kind == "native_error"`, the same refusal `s02_build_prompts.py` applies to arm E.
Synthesised placeholder feedback is forbidden (`src/goedel_native.py:159`); a
placeholder-fed E′ would be arm C with extra words and would control for nothing.

On the 40 held-out evaluation roots this yields **21 eligible roots**. The other 19 are
15 truncated first attempts, three verifier timeouts and one clipped stdout record — no
compilable proof, therefore no compiler error. This is a hard ceiling of the corpus, not a
budget decision.

**Every E′ contrast is computed on the matched 21-root subset**, which is the same subset
the paper already uses for arm E (`tab:native`, Appendix C). Marginal comparisons against
the full 40 are not reported.

## 4. Seeds

Each E′ branch uses that root's frozen arm-A seed, identical to A/B/C/D/E in block 1. As
§3 of the paper already states, shared seeds buy bookkeeping determinism and exact replay,
not variance reduction, because the prompts differ and trajectories diverge at the first
token.

## 5. Endpoints and tests

**Primary (descriptive — see §8).** Lean verification, paired within root on the 21
eligible roots.

| contrast | what it isolates |
|---|---|
| `E' − C` | adding the native diagnosis to the same prior attempt, one turn held fixed |
| `E' − A` | the deployed configuration against fresh generation |
| `E' − E` | conversation structure alone: identical correction content, one turn vs three |

Exact McNemar for each, two-sided, with discordant counts reported. 95% percentile root
bootstrap, 20,000 replicates, seed 20260828, matching every other interval in the paper.

**Secondary, descriptive:** terminal-state counts (verified / lean\_failed / truncated);
completion tokens; and textual anchoring `S(E′, own prior attempt)` against the existing
`S(C, own)` and the unrelated-root null band, to record whether supplying the diagnosis
changes how much of the attempt is reproduced.

**Multiplicity.** E′ forms **no Holm family** and joins none. Its *p*-values are reported
unadjusted. Adding a post-hoc arm to a pre-specified family would change the correction
applied to the registered tests, and the registered family is fixed.

## 6. Power, stated before the run

With 21 roots and arm A verifying 5/21 while C verifies 0/21 on this subset, exact McNemar
can resolve a near-complete recovery and cannot resolve a partial one. This arm is not
expected to resolve a small effect and is not run in the hope that it will.

Both outcomes are informative, which is why it is worth 21 branches:

| observed | reading |
|---|---|
| E′ recovers toward A | a material part of the C−A deficit is the withheld diagnosis, and the paper must say so and qualify its claim |
| E′ stays near C | the prior attempt harms even when the model receives exactly the signal it was trained to consume; the off-distribution objection is answered |
| in between | reported as unresolved at this n, with the interval, and no equivalence claim |

A null is reported as a null. No outcome licenses a design recommendation from a 21-root cell.

## 7. Separation and blinding

E′ is post-hoc with respect to the registered 2×2 and must be visibly separate from it.
`runs.sqlite` holds pre-registered cohorts under a frozen spec hash and is not written to.

The cohort name contains `eval`, so `overnight_queue.py` refuses to start it unblinded.
It is run with `s12_run.py --blind`, which withholds outcomes, token counts and wall times
from stdout — a branch that stops exactly at the cap is a truncation tell.

## 8. Registration tier

**Exploratory.** This specification is written before generation, so the design, eligibility
rule, contrasts and interpretation table above are pre-specified rather than chosen after
the fact. But E′ is not part of the registered design, its estimands were not registered,
and it is reported as descriptive throughout — the same tier as the restart-permissive arms,
governed by the same rule.

## 9. Gates — the builder aborts if any fails

1. exactly 21 eligible roots, all with `feedback_kind == "native_error"`
2. every E′ prompt ends with `OFFICIAL(theorem)`, byte-identical to arm A's prompt
3. the `<previous_attempt>` segment is byte-identical to that root's arm-C segment
4. the correction-turn text is byte-identical to that root's arm-E third turn
5. exact reconstruction: `prompt == EPRIME_WRAPPER + correction_turn + "\n\n" + base`
6. the rebuilt `<error>` block matches the stored `native_feedback_sha256`
7. each branch's seed equals that root's frozen arm-A seed
8. `data/eprime.sqlite` contains no `done` branch before the run starts

## 10. What this arm does not establish

It does not evaluate a repair-trained model other than this checkpoint, does not vary the
error format, does not separate the error block from the analysis instruction that Goedel's
own correction turn bundles with it, and does not extend to the 19 roots with no compiler
error. `E' − E` is a one-versus-three-turn comparison on 21 roots and is descriptive.

## 11. Change log

| when | what |
|---|---|
| 2026-08-30, before generation | First frozen version. Written after the objection was added to the paper (§6, limitation 1) and before `scripts/s49_build_eprime.py` staged any branch. |
