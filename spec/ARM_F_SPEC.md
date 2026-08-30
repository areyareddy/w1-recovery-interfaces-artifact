# Arm F — native feedback without the prior attempt. Analysis specification, frozen before generation.

**Status when this file was written:** `data/armf.sqlite` does not exist. No F prompt has
been staged and no F completion exists. The contrasts, eligibility and interpretation below
were fixed before any F outcome could be seen.

| | |
|---|---|
| builder | `scripts/s51_build_armf.py` |
| runner | `scripts/s12_run.py --blind` |
| cohort | `eval_armf` |
| database | `data/armf.sqlite` |
| server config | `configs/primary.json` (single slot, `--no-cache-prompt`, ctx 32768) |
| companion spec | `spec/EPRIME_SPEC.md` (arm E′, already generated and analysed) |

---

## 1. Why this arm, given E′ already ran

E′ answered the narrower question — does supplying the native diagnosis restore
fresh-sampling yield — and the answer was *it reduces retention but does not restore yield,
and the contrast is unresolved at n=21*. But `E′ − A` still varies **two** things at once:
the prior attempt **and** the feedback. It therefore cannot isolate prior-attempt access in
the presence of genuine feedback, which is the configuration deployed systems actually ship.

Arm F supplies the native compiler error **without** the prior attempt, in the same
one-turn structure, completing the factorial:

| | no attempt | attempt |
|---|---|---|
| **no feedback** | `A` (frozen) | `C` (frozen) |
| **feedback** | **`F` (this spec)** | `E′` (generated) |

## 2. Construction

```
F = FEEDBACK_ONLY_WRAPPER(native errors) + OFFICIAL(theorem)
```

- One user turn, same family as A/B/C/D/E′.
- `OFFICIAL(theorem)` byte-identical to arm A's whole prompt.
- The correction content is byte-identical to what E′ inlines and to arm E's third turn:
  Goedel's own `CORRECTION_TURN`, unmodified.
- `FEEDBACK_ONLY_WRAPPER` is E′'s wrapper **with the `<previous_attempt>` block removed**
  and its announcing sentence adjusted, because E′'s sentence refers to an attempt that F
  does not show. No placeholder stands in for the removed attempt: `src/prompts.py`
  forbids synthesised placeholders, and a placeholder would reintroduce the artifact whose
  absence defines this arm.

**A necessary asymmetry, disclosed.** Goedel's correction turn refers to "the proof
(Round 1)" and asks for an analysis of the error message, so in F the model is told about a
proof it cannot see. That is unavoidable for this cell — feedback-without-attempt is
intrinsically a partial view — and it is the reason `F − A` is read as *feedback alone in
this interface* rather than as a clean feedback factor. `E′ − F` does not inherit this
problem: both arms carry the identical correction turn, so the referent asymmetry is held
constant and only attempt-presence varies.

## 3. Eligibility and seeds

Identical to E′: the **21 held-out roots** with `feedback_kind == "native_error"`, the same
roots arm E uses. Each F branch takes that root's frozen arm-A seed, as every other arm on
these roots does. No new roots, no re-seeding, no top-ups.

## 4. Contrasts — frozen here, before any F outcome exists

| contrast | what it isolates | status |
|---|---|---|
| `E′ − F` | **prior-attempt access with genuine feedback present** — the paper's central factor, in the deployed configuration | primary interest |
| `F − A` | feedback alone, no attempt (subject to §2's referent asymmetry) | secondary |
| `F − B` | grounded compiler error vs static failure-class guidance, both attempt-free | secondary |
| `F − C` | swapping the attempt for its diagnosis | descriptive |

Exact McNemar, two-sided, discordant counts reported. 95% percentile root bootstrap,
20,000 replicates, seed 20260828, matching every interval in the paper.

The 2×2 interaction `(E′ − F) − (C − A)` is computed and reported **with its interval
only**. At n=21 a difference of differences on binary outcomes has no useful resolution;
it is recorded so the factorial is complete, never as a test.

## 5. Multiplicity and tier

**Exploratory, and more weakly placed than E′.** E′'s specification was written when no
outcome in its family was known. This one is not: **E′'s results were already known when
these contrasts were chosen**, so even though nothing about F itself has been observed, the
choice of contrasts was made by someone who had seen a neighbouring result. That is
disclosed here rather than glossed, and it is why every F contrast is exploratory
regardless of what it shows.

F forms **no Holm family** and joins none. All *p*-values unadjusted. Adding a post-hoc arm
to a pre-specified family would change the correction applied to the registered tests.

## 6. Power, stated before the run

n = 21, with A at 5/21, C at 0/21 and E′ at 2/21 on this subset. Exact McNemar over
single-digit discordant counts resolves only a near-complete swing. `E′ − F` in particular
compares two arms that are each expected to verify a handful of roots, so it will almost
certainly be unresolved.

**This arm is run to complete the factorial and to remove a confound from `E′ − A`, not to
resolve an effect.** No outcome licenses a design recommendation from a 21-root cell.

| observed | reading |
|---|---|
| F above E′ | consistent with the attempt harming even when feedback is present; report with interval, unresolved unless the discordance is one-directional and large |
| F at or below E′ | the attempt is not the active harm once feedback is present; the paper must say so and qualify the `C − A` reading for feedback-bearing interfaces |
| F near A | feedback alone recovers what the attempt costs |
| all within noise | reported as unresolved, which at this n is the expected outcome |

A null is reported as a null.

## 7. Blinding and separation

Cohort name contains `eval`, so it is run with `s12_run.py --blind`; outcomes, token counts
and wall times are withheld from stdout. `runs.sqlite` is not written to. F lives in its own
database, as C′, the restart arms and E′ do.

## 8. Gates — the builder aborts if any fails

1. exactly 21 eligible roots, all `feedback_kind == "native_error"`, identical to E′'s set
2. every F prompt ends with `OFFICIAL(theorem)`, byte-identical to arm A's prompt
3. the correction turn in F is byte-identical to that root's E′ correction turn
4. **the root's prior attempt appears nowhere in its F prompt** — the defining property
5. exact reconstruction: `prompt == wrapper_head + correction_turn + wrapper_tail + base`
6. the rebuilt `<error>` block matches the stored `native_feedback_sha256`
7. each branch's seed equals that root's frozen arm-A seed
8. re-derived frozen A/C prompts still match `data/prompts.jsonl` byte-for-byte
9. `data/armf.sqlite` holds no `done` branch before the run starts

## 9. What this arm does not establish

It does not clean up the referent asymmetry of §2, does not vary the error format, does not
extend to the 19 roots without a compiler error, and does not make any contrast in this
family confirmatory. The completed 2×2 is a descriptive factorial on 21 theorems.

## 10. Change log

| when | what |
|---|---|
| 2026-08-30, before generation | First frozen version. Written after E′ was generated and analysed, which is disclosed in §5 as the reason this arm is exploratory. |
