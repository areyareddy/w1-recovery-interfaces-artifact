"""Fault-injection sensitivity test for the W2 agent-loop conformance monitor.

This is CPU-only and never writes an experiment database.  It injects one fault at a
time into immutable replay state, uses the same monitor functions as s34, and records
which invariant detects the fault and the detection latency.

    python scripts\s43_agent_loop_mutations.py
"""

from __future__ import annotations

import json
import sqlite3
import sys
import time
from dataclasses import replace
from pathlib import Path


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT / "src"))
sys.path.insert(0, str(HERE))

import agent_loop as al  # noqa: E402
import agent_loop_monitor as monitor  # noqa: E402
import s34_agent_loop_replay as replay_check  # noqa: E402


DB = ROOT / "data" / "alloc_split2.sqlite"
COHORT = "alloc_split2_eval"
OUT = ROOT / "audit" / "agent_loop_mutations.json"


def timed(name: str, expected: str, fn) -> dict:
    start = time.perf_counter_ns()
    observed = fn()
    elapsed_ms = (time.perf_counter_ns() - start) / 1_000_000
    detected = expected in observed
    if not detected:
        raise AssertionError(f"{name}: expected {expected!r}, observed {observed!r}")
    return {
        "fault": name,
        "expected_invariant": expected,
        "observed": observed,
        "detected": detected,
        "detection_ms": round(elapsed_ms, 3),
    }


def main() -> int:
    roots = replay_check.roots_of(DB, COHORT)
    if len(roots) != 40:
        raise AssertionError(f"expected 40 held-out roots, found {len(roots)}")

    # Select a root with two failed draws so every mutation has a two-step base trace.
    con = sqlite3.connect(f"file:{DB}?mode=ro", uri=True)
    root = con.execute(
        "SELECT root_id FROM branches WHERE cohort=? GROUP BY root_id "
        "HAVING COUNT(*)=2 AND SUM(verified)=0 ORDER BY root_id LIMIT 1",
        (COHORT,),
    ).fetchone()[0]
    con.close()

    key_fn = lambda theorem, i, action: f"{theorem}|split2|d{i + 1}"
    backend = al.ReplayBackend(DB, key_fn)
    try:
        base = al.run(root, al.SPLIT2, backend, prior_attempt="<historic failed attempt>")
    finally:
        backend.close()
    if len(base.steps) != 2 or any(step.verified for step in base.steps):
        raise AssertionError("mutation base trace must contain two failed draws")
    direct = replay_check.direct_accounting(DB, COHORT, root)
    base_sig = replay_check.trace_signature(base)

    cases: list[dict] = []

    def missing_branch() -> str:
        bad = al.ReplayBackend(DB, lambda theorem, i, action: "corrupted|branch|key")
        try:
            try:
                al.run(root, al.SPLIT2, bad, prior_attempt="<historic failed attempt>")
            except LookupError:
                return "conformance"
            return "none"
        finally:
            bad.close()

    cases.append(timed("corrupt_branch_key", "conformance", missing_branch))

    def corrupt_cap() -> str:
        bad_policy = al.FixedPolicy(
            "corrupt_cap", ((al.Action.REGENERATE, 6000), (al.Action.REGENERATE, 6288))
        )
        bad = al.ReplayBackend(DB, key_fn)
        try:
            try:
                al.run(root, bad_policy, bad, prior_attempt="<historic failed attempt>")
            except ValueError:
                return "conformance"
            return "none"
        finally:
            bad.close()

    cases.append(timed("corrupt_cap", "conformance", corrupt_cap))

    overrun = replace(base, budget=sum(step.cap for step in base.steps) - 1)
    cases.append(timed(
        "inject_budget_overrun",
        "budget",
        lambda: "|".join(monitor.trace_violations(overrun, direct)),
    ))

    bad_stop = replace(base, stop_reason=al.StopReason.VERIFIED)
    cases.append(timed(
        "flip_stop_decision",
        "stop_rule",
        lambda: "|".join(monitor.trace_violations(bad_stop, direct)),
    ))

    bad_first = replace(base.steps[0], completion_tokens=base.steps[0].completion_tokens + 1)
    bad_accounting = replace(base, steps=[bad_first, *base.steps[1:]])
    cases.append(timed(
        "corrupt_accounting_token",
        "accounting",
        lambda: "|".join(monitor.trace_violations(bad_accounting, direct)),
    ))

    bad_action = replace(base.steps[0], action=al.Action.REPAIR)
    action_trace = replace(base, steps=[bad_action, *base.steps[1:]])
    bad_seq = {tuple((step.action.value, step.cap) for step in action_trace.steps)}
    cases.append(timed(
        "perturb_action_sequence",
        "non_adaptivity",
        lambda: "|".join(monitor.non_adaptivity_violations(bad_seq, al.SPLIT2)),
    ))

    cases.append(timed(
        "perturb_replay_signature",
        "determinism",
        lambda: "|".join(monitor.determinism_violations(
            [base_sig], [base_sig + "corruption"]
        )),
    ))

    result = {
        "base_policy": "split2",
        "base_root": root,
        "mutations": cases,
        "summary": {
            "faults_injected": len(cases),
            "faults_detected": sum(case["detected"] for case in cases),
            "max_detection_ms": max(case["detection_ms"] for case in cases),
            "database_modified": False,
        },
    }
    OUT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"PASS -- detected {len(cases)}/{len(cases)} injected faults")
    for case in cases:
        print(f"  {case['fault']:<28} -> {case['expected_invariant']:<16} "
              f"{case['detection_ms']:.3f} ms")
    print(f"wrote {OUT.relative_to(ROOT).as_posix()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
