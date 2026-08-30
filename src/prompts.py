"""The single prompt-construction surface for arms A/B/C/D/E.

Nothing else in the harness may assemble a prompt. One surface means the prompt-diff
audit (Gate 5) is auditing the thing that actually runs.

COMPOSITION -- guidance outermost, always
=========================================

    A =                              OFFICIAL(theorem)
    B = GUIDANCE_BLOCK +             OFFICIAL(theorem)
    C =                  WRAPPER_BLOCK + OFFICIAL(theorem)
    D = GUIDANCE_BLOCK + WRAPPER_BLOCK + OFFICIAL(theorem)

v7 `04` Sec.6 writes these as `theorem + R2 + prior + wrapper + base`, which cannot be
built: official_prompt() embeds the theorem INSIDE the base template, so theorem-and-base
are one inseparable unit, and CoLM's concrete_guidance_prompt PREPENDS the guidance ahead
of the whole thing. The ordering above is the only one under which all four Gate 5
assertions hold as exact string operations (MASTER_CORRECTION.md Sec.3):

    A -> B   prepend GUIDANCE_BLOCK
    A -> C   prepend WRAPPER_BLOCK
    B -> D   insert WRAPPER_BLOCK at offset len(GUIDANCE_BLOCK)
    C -> D   prepend GUIDANCE_BLOCK

A/B/C/D are all ONE user turn. That is deliberate and it is what makes the 2x2 clean:
conversation structure is held constant, so the only things that vary are guidance
presence and prior-attempt presence. Arm E is the one arm that changes conversation
structure, which is exactly why E-A is reported as a native-interface positive control
and never as an isolated artifact effect.

THE WRAPPER IS OURS, NOT CoLM's
===============================

v7 names `neutral_prior_attempt_wrapper()` but never specifies its wording. The string
below is therefore a W1 design decision that must be disclosed in the paper, and it is
frozen by hash into spec/frozen_spec.yaml at s11. Three constraints shaped it:

  1. It says the attempt was not accepted and says NOTHING about why. Any hint of the
     failure mode would leak error information into arm C, and C would stop being an
     artifact-presence manipulation.
  2. It is uniform across all 83 roots -- no per-failure-class wording. Analysis 3
     measures effects BY failure class, so treatment must not vary with the grouping.
  3. It does not instruct repair. The base instruction already asks for a complete
     proof. Telling the model to "fix" the attempt would convert C from "prior attempt
     present" into "repair instruction present" and change what the factor means.
"""

from __future__ import annotations

import policy

ARMS = ("A", "B", "C", "D", "E")
ARMS_FACTORIAL = ("A", "B", "C", "D")

ARM_TITLE = {
    "A": "Plain Fresh",
    "B": "R2 Guided Fresh",
    "C": "Prior Attempt",
    "D": "R2 Guided Prior Attempt",
    "E": "Native-Feedback Self-Correction (positive control)",
}

# guidance present? / prior attempt present?
ARM_FACTORS = {
    "A": (False, False),
    "B": (True, False),
    "C": (False, True),
    "D": (True, True),
}

# FROZEN 2026-08-28. Changing one character invalidates every C and D branch.
NEUTRAL_PRIOR_ATTEMPT_WRAPPER = """A previous attempt at this problem was not accepted by the Lean 4 compiler. It is reproduced below exactly as it was produced, with no information about why it was not accepted.

<previous_attempt>
{prior_attempt}
</previous_attempt>

"""


# FROZEN 2026-08-30 by spec/EPRIME_SPEC.md. Arm E' only. This is the arm-C wrapper with
# exactly one clause changed: C says the attempt comes "with no information about why it
# was not accepted", which would be FALSE in E' because the compiler output follows. You
# cannot add the diagnosis while still announcing that no diagnosis is present, so the
# clause is changed and the change is disclosed in the spec rather than hidden.
# Everything else -- the first sentence, the <previous_attempt> tags, the trailing blank
# line -- is byte-identical to NEUTRAL_PRIOR_ATTEMPT_WRAPPER, and Gate 3 checks it.
EPRIME_PRIOR_ATTEMPT_WRAPPER = """A previous attempt at this problem was not accepted by the Lean 4 compiler. It is reproduced below exactly as it was produced, together with the compiler output it produced.

<previous_attempt>
{prior_attempt}
</previous_attempt>

"""


def eprime_prompt(theorem: str, raw_prior_attempt: str, native_feedback: str) -> str:
    """The single user turn for arm E'. NOT part of ARMS: A/B/C/D/E are frozen and E' is
    staged by scripts/s49_build_eprime.py into its own database, exactly as C' and the
    restart arms were.

    `native_feedback` must be the SAME string arm E puts in its third user turn -- Goedel's
    own CORRECTION_TURN, unmodified -- so that E' minus E is a pure conversation-structure
    contrast and carries no content difference. Passing the bare <error> block instead
    would silently make E' a different treatment from E; the builder asserts equality
    against the arm-E payload rather than trusting the caller.
    """
    if not raw_prior_attempt:
        raise ValueError("arm E' requires a prior attempt")
    if not native_feedback:
        raise ValueError("arm E' requires native feedback")
    return (EPRIME_PRIOR_ATTEMPT_WRAPPER.format(prior_attempt=raw_prior_attempt)
            + native_feedback
            + "\n\n"
            + policy.official_prompt(theorem))


# FROZEN 2026-08-30 by spec/ARM_F_SPEC.md. Arm F only: native feedback, NO prior attempt.
# This is EPRIME_PRIOR_ATTEMPT_WRAPPER with the <previous_attempt> block deleted and the
# announcing sentence adjusted, because E's sentence refers to an attempt F does not show.
# Nothing stands in for the removed attempt: a placeholder would reintroduce the artifact
# whose absence defines this arm, and src/prompts.py forbids synthesised placeholders.
#
# The correction turn that follows still says "the proof (Round 1)", so F tells the model
# about a proof it cannot see. That asymmetry is intrinsic to feedback-without-attempt and
# is disclosed in ARM_F_SPEC.md section 2; it is held CONSTANT in E'-F, which is why that
# contrast, not F-A, is the clean test of prior-attempt access under feedback.
FEEDBACK_ONLY_WRAPPER = """A previous attempt at this problem was not accepted by the Lean 4 compiler. The attempt itself is not shown. The compiler output it produced is reproduced below exactly.

"""


def armf_prompt(theorem: str, native_feedback: str) -> str:
    """The single user turn for arm F. NOT part of ARMS; staged by
    scripts/s51_build_armf.py into its own database, as C', the restart arms and E' were.

    `native_feedback` must be the SAME string E' inlines and arm E sends as its third
    turn, so that E'-F varies attempt-presence and nothing else. The builder asserts that
    equality against the arm-E payload rather than trusting the caller.
    """
    if not native_feedback:
        raise ValueError("arm F requires native feedback")
    return (FEEDBACK_ONLY_WRAPPER
            + native_feedback
            + "\n\n"
            + policy.official_prompt(theorem))


def guidance_block(theorem: str, tactics: list[str] | None) -> str:
    """R2BLOCK. Delegates to policy.guidance_block (theorem-independent, separately
    hashed) but re-derives the same prefix from the frozen full-prompt renderer and
    asserts they agree. Those are two expressions of the same text, and if they ever
    drift, B/D prompts stop matching what CoLM actually sent -- silently."""
    block = policy.guidance_block(tactics)
    if block:
        base = policy.official_prompt(theorem)
        guided = policy.concrete_guidance_prompt(theorem, tactics)
        assert guided == block + base, (
            "policy.guidance_block() and concrete_guidance_prompt() disagree; "
            "the frozen renderer and the block renderer have drifted"
        )
    return block


def wrapper_block(raw_prior_attempt: str) -> str:
    return NEUTRAL_PRIOR_ATTEMPT_WRAPPER.format(prior_attempt=raw_prior_attempt)


def arm_prompt(arm: str, theorem: str, tactics: list[str] | None = None,
               raw_prior_attempt: str | None = None) -> str:
    """The single user turn for A/B/C/D. Arm E does not have one -- use arm_messages."""
    if arm not in ARM_FACTORS:
        raise ValueError(f"arm_prompt is for A/B/C/D only, got {arm!r}")
    want_guidance, want_prior = ARM_FACTORS[arm]
    if want_guidance and not tactics:
        raise ValueError(f"arm {arm} requires guidance tactics")
    if want_prior and not raw_prior_attempt:
        raise ValueError(f"arm {arm} requires a prior attempt")

    parts = []
    if want_guidance:
        parts.append(guidance_block(theorem, tactics))
    if want_prior:
        parts.append(wrapper_block(raw_prior_attempt))
    parts.append(policy.official_prompt(theorem))
    return "".join(parts)


def arm_messages(arm: str, theorem: str, tactics: list[str] | None = None,
                 raw_prior_attempt: str | None = None,
                 native_feedback: str | None = None) -> list[dict[str, str]]:
    """Chat payload for any arm. Goedel takes NO system message -- CoLM's
    build_chat_payload passes system_message=None and the GGUF chat template injects no
    fallback. Do not add one."""
    if arm == "E":
        if not raw_prior_attempt or not native_feedback:
            raise ValueError("arm E requires both a prior attempt and native feedback")
        return [
            {"role": "user", "content": policy.official_prompt(theorem)},
            {"role": "assistant", "content": raw_prior_attempt},
            {"role": "user", "content": native_feedback},
        ]
    return [{"role": "user", "content":
             arm_prompt(arm, theorem, tactics, raw_prior_attempt)}]
