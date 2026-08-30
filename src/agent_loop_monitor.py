"""Reusable invariant checks for the fixed-policy agent-loop replay.

The replay and the mutation test import these same checks.  Keeping the monitor in one
module prevents the sensitivity experiment from testing a second, easier-to-pass copy of
the assertions used by the conformance audit.
"""

from __future__ import annotations

from typing import Iterable

import agent_loop as al


def trace_violations(trace: al.Trace, direct_accounting: dict | None = None) -> list[str]:
    """Return budget, stop-rule, and optional accounting violations for one trace."""
    out: list[str] = []
    committed = sum(step.cap for step in trace.steps)
    if committed > trace.budget:
        out.append(f"budget: committed {committed} > {trace.budget}")

    any_verified = any(step.verified for step in trace.steps)
    if any_verified and trace.stop_reason is not al.StopReason.VERIFIED:
        out.append(f"stop_rule: verified draw but stop={trace.stop_reason}")
    if not any_verified and trace.stop_reason is al.StopReason.VERIFIED:
        out.append("stop_rule: stop=VERIFIED with no verified draw")

    if direct_accounting is not None:
        got = trace.accounting(stop_after_first_success=True)
        if got != direct_accounting:
            out.append(f"accounting: {got} != {direct_accounting}")
    return out


def non_adaptivity_violations(
    action_sequences: Iterable[tuple[tuple[str, int], ...]],
    policy: al.FixedPolicy,
) -> list[str]:
    """Require every executed sequence to be a prefix of the fixed action plan."""
    plan = [(action.value, cap) for action, cap in policy.plan]
    bad = [seq for seq in action_sequences if list(seq) != plan[: len(seq)]]
    return [f"non_adaptivity: sequence is not a fixed-plan prefix: {seq}" for seq in bad]


def determinism_violations(first: list[str], second: list[str]) -> list[str]:
    """Require byte-identical serialized traces across repeated replay."""
    if first == second:
        return []
    return ["determinism: repeated replay signatures differ"]
