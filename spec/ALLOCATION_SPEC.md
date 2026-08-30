# Fixed-budget retry allocation — analysis specification, frozen before generation

**Status when this file was written:** `data/alloc_split2.sqlite` and
`data/alloc_split3.sqlite` hold 415 branches, all `pending`. No allocation completion
exists. Nothing below was chosen after seeing an allocation outcome.

| | |
|---|---|
| allocation design sha256 | `ca5f1cbd074a58108becfed86ec3743f40c23553d8050d520916790b8026fc97` |
| builder | `scripts/s31_build_allocation.py` |
| queue driver | `scripts/overnight_queue.py` |
| commit-instruction sha256 (unchanged arms) | `db5d19c5cac39e6c2156af58ec2485d9f22b3a3101e5f66b8e13347f561220c3` |

The design digest is `sha256` over the sorted `cohort:branches:cap` triples. If it differs
at analysis time the experiment was restaged and this specification no longer describes
what ran.

## 1. Question

W2 established descriptively that 51.6% of all serving time is consumed by branches that
hit the 12,288-token cap and never reach the Lean kernel. This experiment asks whether that
compute can be reallocated:

> At the same per-root completion-token budget, does splitting the budget across several
> shorter draws verify more theorems than spending it on one long draw?

This is a causal comparison of allocation policies, not a measurement. It is the first
thing in either paper that manipulates a decision rather than observing one.

## 2. Policies

Budget is **12,288 completion tokens per root**, identical for all three.

| policy | draws | cap per draw | status |
|---|---:|---:|---|
| Long | 1 | 12,288 | already generated — arm A of the frozen study |
| Split-2 | 2 | 6,144 | staged here, 80 eval + 86 dev |
| Split-3 | 3 | 4,096 | staged here, 120 eval + 129 dev |

**Why these caps.** From the already-published ledger, completions that verify are short:
median 3,263 decode tokens, p90 7,068. A 6,144 cap retains 82% of every completion that
ever verified while buying two draws; 4,096 retains 61% while buying three. Below 4,096 the
retained fraction falls faster than the draw count rises. The caps were read off that
distribution before any allocation branch was generated. The distribution is a property of
published data, not of this experiment's outcomes.

## 3. Seeds

Draw `j` of a root uses `base_seed + (j - 1)`, where `base_seed` is that root's frozen
arm-A seed. Draw 1 of Split-2, draw 1 of Split-3 and the existing Long baseline therefore
share a seed.

If the server is prefix-deterministic under a fixed seed — same prompt, same sampler, only
`n_predict` differing — those three draws are prefixes of a single trajectory and the
policies are compared on a shared first draw. **No analysis below assumes this.** Every
draw is generated for real. It is recorded because if it holds the comparison is tighter,
and because assuming it silently is exactly the class of unchecked premise this project has
had to correct before.

## 4. Endpoints

**Primary.** Fraction of roots with at least one Lean-verified proof within the 12,288-token
budget. Paired within root across policies; exact McNemar for each pairwise contrast;
95% percentile root bootstrap, 20,000 replicates, seed 20260828, matching every other
interval in both papers.

**Secondary**, all descriptive unless stated:

- verified roots per 1,000 end-to-end wall-seconds
- seconds and total tokens per verified root
- time to first success
- terminal-state counts (verified, Lean failed, truncated) by policy and by draw index
- prefill, decode and verifier time — **recorded at generation time**, so no replay is
  required (`scripts/s29_migrate_timings.py`)
- cost–quality frontier over consumed budget

**Two cost accountings are reported for every policy**, both pre-specified:

1. **Full budget** — every draw is generated and paid for, even after one verifies.
2. **Stop after first success** — a simulated policy that halts a root at its first
   verified draw. Draws are executed in index order, so this is computed by truncating each
   root's draw sequence at its first verified draw and summing only the draws up to and
   including it. This rule is fixed here, before any outcome is seen; it is a
   re-accounting of executed draws, not a re-run.

## 5. Multiplicity

Holm family = {Split-2 − Long, Split-3 − Long}, size 2. Split-3 − Split-2 is reported as a
descriptive line and is not in the family; it is a comparison between two new policies
rather than a test of the paper's claim, and folding it in would penalise the two primary
tests for a question that is not being asked confirmatorily.

## 6. Router baselines -- WITHDRAWN 2026-08-29, not reported

**This section is withdrawn. The router baseline is not reported in any form**, neither as
a result nor as an exploratory appendix. The reason is recorded in section 7: the
dev-derived thresholds this section requires were never written or hashed, and the eval
cohorts' outcomes reached a plaintext log at generation time, so the guarantee that made
these thresholds credible cannot be reconstructed after the fact.

The thresholds could still be derived mechanically from the 43 dev roots, and that
derivation would be a deterministic function of dev data that any reader could re-run.
It is withdrawn anyway. The rule family leaves sixteen threshold pairs and the objective
that selects among them was never frozen, so a reader is asked to trust that the objective
was not chosen by someone who had seen the eval outcomes. That is exactly the trust this
document exists to make unnecessary. A secondary baseline is not worth spending the
credibility of the primary design to defend.

**Nothing else in this specification depends on it.** Section 8 already says so: "If the
dev cohorts are incomplete, section 6 is not reported at all. The primary endpoint does
not depend on it." The primary endpoint of section 4 is unaffected -- see section 7.

The proper form of this analysis is a pre-registered causal experiment on the patched
harness, not a rescue of this one.

The original text follows, unchanged, as the record of what was planned.

---

Using the executed draws as a candidate bank, four allocation rules are compared:

1. fixed-step / fixed-cap policies (the three above)
2. an **output-token or SFLOP proxy** policy — chooses the policy minimising generated
   tokens, ignoring verification cost
3. a **censoring-aware** policy — after a capped draw, spend the remaining budget on
   further short draws; after a complete but Lean-rejected draw, continue or stop by a
   threshold
4. a **retrospective oracle** allocation, as an upper bound

**Thresholds for rule 3 are read off the 43 dev roots only, written down, and hashed before
any eval cohort is opened.** The rule family is fixed here: a single threshold on the count
of prior capped draws, and a single threshold on prior complete-but-rejected draws, each an
integer in 0–3. No trained model, no continuous tuning — at 43 roots a transparent frozen
rule is more credible than a fitted router, and a fitted one would not survive review.

## 7. Inspection rule

Generation order does not threaten validity; inspection order does. Eval cohorts are
generated first only so that a truncated window costs the router analysis rather than the
primary endpoint.

**No eval cohort may be opened — not counts, not rates, not plots — before the dev-derived
thresholds of section 6 are written and hashed.** `scripts/overnight_status.py` deliberately
reports only `done`/`pending`/`failed` counts and never outcomes, so the queue can be
monitored without breaking this.

### 7.1 This rule was broken. What happened, and what it costs

**The breach.** `scripts/overnight_status.py` did honour the rule. But
`scripts/overnight_queue.py` redirected `scripts/s12_run.py`'s stdout into
`audit/overnight/<job>.log`, and `s12_run.py` was not blinded: it printed an `OK` marker
and `outcome_state` per branch, then an outcomes dict, a per-arm outcome table, and
`arm X: verified v/n`. So both eval cohorts' outcomes — including per-arm verified counts —
were written to a plaintext log **at generation time**, on 2026-08-29 between 08:23Z and
10:18Z. The guard was on the front door and the queue drove around the back. No threshold
artifact was ever written, so the ordering the rule protects never happened at all.

**Affected files**, quarantined by name in `scripts/s33_blinding_regression.py`:
`audit/overnight/alloc_split2_eval.log` (85 leaking lines) and
`audit/overnight/alloc_split3_eval.log` (125). They are kept, not deleted: they are the
evidence. The dev logs leak outcomes too, which is harmless — section 11 makes dev
descriptive throughout.

**What it costs: section 6 only.** The router baseline is withdrawn. The guarantee at
stake is temporal — thresholds hashed *before* the eval could be opened — and it cannot be
re-established by asserting that nobody happened to read the file. That negative is not
certifiable, and a reviewer should not be asked to take it on trust.

**What it does not cost: the primary endpoint of section 4.** Long / Split-2 / Split-3 is a
comparison of three fixed policies at a fixed budget, frozen in this document before
generation and identified by the allocation design digest, which is unchanged. Its
endpoint, its pairing, its tests and its Holm family were all fixed here in advance, and
none of them depends on inspection order. Section 8's partial-completion rules are
outcome-independent and every cohort finished at 100%. **The primary comparison stands
exactly as specified**, and this subsection changes nothing above it.

**The fix, so it cannot recur.** `s12_run.py` gained a `--blind` mode that withholds every
outcome — and also the token and wall-time figures, since a branch that stops exactly at
the cap is a truncation tell. `overnight_queue.py` gained `BLIND_COHORTS`, passes `--blind`
for those cohorts, and now **refuses to start** if any cohort whose name contains `eval` is
not explicitly either blinded or excused in `UNBLINDED_OK` with a stated reason — because
what failed here was not a wrong decision but a forgotten one.
`scripts/s33_blinding_regression.py` tests the detector against a known-bad sample, checks
that both halves of the contract still hold, and fails on any new leak.

## 8. Partial completion

An unattended window on a machine that has already restarted its server once will probably
not finish everything. Fixed in advance:

- A cohort is analysed **only if all of its branches are `done`.** A cohort with any
  incomplete branch is reported as *not run*, never as a subset. Selecting the finished
  subset of a partly-generated cohort is outcome-dependent selection, which is the failure
  mode this document exists to prevent.
- The primary endpoint requires **both** eval cohorts complete. If only one policy
  finished, its Long contrast is reported and the other is reported as not run.
- If the dev cohorts are incomplete, section 6 is not reported at all. The primary endpoint
  does not depend on it.
- No cohort is extended, re-seeded or topped up to replace failed branches.

## 9. Prefill is not a handicap, and here is the number in advance

A reviewer will ask whether the split policies are penalised by paying prefill once per
draw. Arm-A prompts prefill at 194 tokens, so three draws cost 582 prefill tokens against a
12,288-token decode budget — about 0.06 s at the measured 8,762 tok/s, against per-draw
decode times of 30–100 s. Stated here so it is a prediction rather than a rebuttal.

## 10. Interpretation, fixed in advance

| observed | reading |
|---|---|
| Split-2 and/or Split-3 beat Long on the primary endpoint | budget allocation, not budget size, limits recovery yield on this stack; the capped-decode compute identified in W2 is recoverable |
| all three within noise | cap choice does not matter at this budget; W2's censoring finding stands as accounting only, and the paper says the reallocation was tried and did not pay |
| Long beats the splits | short caps truncate proofs that would have verified; the retained-fraction estimate in section 2 was optimistic, and the cost of censoring is not recoverable by splitting alone |

A null result is reported as a null result. This experiment is worth running because its
negative outcome is publishable in the same paragraph as its positive one.

## 11. What this experiment does not establish

It compares fixed allocation policies on one model, one GPU, one serving configuration and
one failure-conditioned root set. It does not evaluate a learned controller, does not vary
the total budget, and does not claim a policy that transfers to another stack. The dev
cohort informed development and is descriptive throughout.

## 12. Change log

| when | what |
|---|---|
| 2026-08-29, after generation | Withdrew section 6 (router baselines) and recorded the
section 7 breach in new subsection 7.1. Sections 1-5 and 8-11 — the policies, seeds,
endpoints, multiplicity and partial-completion rules that constitute the primary design —
are **unchanged**, as is the allocation design digest. Nothing was re-specified after
seeing an outcome; one secondary analysis was removed and the reason recorded. |
| 2026-08-29, before generation | First frozen version. Written after `s31_build_allocation.py` staged all 415 branches as `pending` and before `scripts/overnight_queue.py` was started. |
