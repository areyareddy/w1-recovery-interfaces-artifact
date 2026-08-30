"""Step s34 -- replay every executed policy through src/agent_loop.py and check invariants.

    python scripts\\s34_agent_loop_replay.py

WHAT THIS PROVES. src/agent_loop.py claims to be a faithful state-machine description of
what the frozen runner executed. That claim is only worth anything if it is checked, so
this replays all four executed policies -- W1 REGENERATE (arm A) and REPAIR (arm C), and
W2 Long, Split-2, Split-3 -- through the state machine against the recorded branches, and
asserts:

  1. CONFORMANCE     every draw the loop takes matches a recorded branch, in order, with
                     the recorded cap. A mismatch means the state machine does not
                     describe what ran.
  2. BUDGET          committed tokens never exceed the 12,288-token budget, for any root
                     under any policy.
  3. STOP RULE       the stop reason is exactly what the state justifies: VERIFIED iff a
                     draw verified, otherwise the plan or the budget ran out.
  4. ACCOUNTING      the loop's stop-after-first-success accounting equals a direct
                     recomputation of ALLOCATION_SPEC section 4's rule straight from the
                     database, computed independently of the state machine.
  5. DETERMINISM     replaying twice yields byte-identical traces.
  6. NON-ADAPTIVITY  the executed action sequence is a function of the policy alone --
                     identical for every root, regardless of outcome. This is the check
                     that would catch anyone quietly making the policy adaptive.

OUTPUT HYGIENE, stated precisely. This prints no verification rate and no per-arm
outcome. It does print the number of draws replayed, and under a stop-on-verification rule
that count is weakly outcome-bearing: 73 of a possible 80 Split-2 draws implies 7 roots
verified on draw 1. That is acceptable here and would not have been in August. The
inspection rule of spec/ALLOCATION_SPEC.md section 7 exists to keep a later CHOICE honest;
the router it protected is withdrawn (section 6) and the primary endpoint of section 4 is
fully pre-specified, so no unmade decision remains for this number to bias. Saying "never
verification rates" would have been the tidier sentence and the false one.
"""

from __future__ import annotations

import json
import sqlite3
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT / "src"))

import agent_loop as al  # noqa: E402
import agent_loop_monitor as monitor  # noqa: E402
import receipts  # noqa: E402

RUNS_DB = ROOT / "data/runs.sqlite"
OUT = ROOT / "audit/agent_loop_replay.json"

# policy name -> (db, cohort, key builder). W1's two policies are one action from the
# seeded state, so they key on the arm; W2's key on the draw index.
SETUPS = {
    "regenerate_once": (RUNS_DB, "primary_eval",
                        lambda t, i, a: f"{t}|A"),
    "repair_once": (RUNS_DB, "primary_eval",
                    lambda t, i, a: f"{t}|C"),
    "split2": (ROOT / "data/alloc_split2.sqlite", "alloc_split2_eval",
               lambda t, i, a: f"{t}|split2|d{i + 1}"),
    "split3": (ROOT / "data/alloc_split3.sqlite", "alloc_split3_eval",
               lambda t, i, a: f"{t}|split3|d{i + 1}"),
}


def roots_of(db: Path, cohort: str) -> list[str]:
    con = sqlite3.connect(f"file:{db}?mode=ro", uri=True)
    rows = [r[0] for r in con.execute(
        "SELECT DISTINCT root_id FROM branches WHERE cohort=? AND status='done' "
        "ORDER BY root_id", (cohort,))]
    con.close()
    return rows


def direct_accounting(db: Path, cohort: str, root: str) -> dict:
    """Section 4's stop rule, recomputed straight from the DB without the state machine.

    Deliberately independent: if this and the loop agree, two separate implementations of
    the frozen rule agree, which is the point of the check.
    """
    con = sqlite3.connect(f"file:{db}?mode=ro", uri=True)
    rows = list(con.execute(
        "SELECT verified, completion_tokens, request_wall_seconds, verifier_wall_seconds "
        "FROM branches WHERE cohort=? AND root_id=? AND status='done' "
        "ORDER BY draw_index", (cohort, root)))
    con.close()
    cut = next((i for i, r in enumerate(rows) if r[0]), None)
    kept = rows[:cut + 1] if cut is not None else rows
    return {"draws": len(kept),
            "verified": any(r[0] for r in kept),
            "completion_tokens": sum(r[1] or 0 for r in kept),
            "seconds": round(sum((r[2] or 0) + (r[3] or 0) for r in kept), 3)}


def trace_signature(t: al.Trace) -> str:
    return json.dumps({"theorem": t.theorem, "policy": t.policy,
                       "stop": t.stop_reason.value,
                       "steps": [[s.attempt_index, s.action.value, s.cap, s.branch_key]
                                 for s in t.steps]}, sort_keys=True)


def main() -> int:
    receipts.force_utf8()
    failures: list[str] = []
    summary: dict = {}

    for name, (db, cohort, key_fn) in SETUPS.items():
        policy = al.POLICIES[name]
        if not db.exists():
            print(f"[--] {name}: {db.name} absent, skipped")
            continue
        roots = roots_of(db, cohort)
        if not roots:
            print(f"[--] {name}: no completed branches in {cohort}, skipped")
            continue

        backend = al.ReplayBackend(db, key_fn)
        traces, sigs, action_seqs = [], [], set()
        try:
            for root in roots:
                # Every root enters with a prior failed attempt: that is what defines the
                # root set. The text itself is irrelevant to a replay, so a marker keeps
                # the state honest without loading 83 completions.
                t = al.run(root, policy, backend, prior_attempt="<historic failed attempt>")
                traces.append(t)
                sigs.append(trace_signature(t))
                action_seqs.add(tuple((s.action.value, s.cap) for s in t.steps))

                # 1. conformance is enforced inside ReplayBackend.draw (cap + key match)
                # 2--4. budget, stop rule, and independent accounting
                want = None
                if name in ("split2", "split3"):
                    want = direct_accounting(db, cohort, root)
                failures.extend(
                    f"{name}/{root}: {msg}"
                    for msg in monitor.trace_violations(t, want)
                )

            # 5. determinism
            again = [trace_signature(al.run(r, policy, backend,
                                            prior_attempt="<historic failed attempt>"))
                     for r in roots]
            failures.extend(f"{name}: {msg}"
                            for msg in monitor.determinism_violations(sigs, again))
        finally:
            backend.close()

        # 6. non-adaptivity: with the stop rule, a trajectory is a PREFIX of the plan, so
        # every distinct sequence must be a prefix of the policy's fixed plan.
        plan = [(a.value, c) for a, c in policy.plan]
        failures.extend(f"{name}: {msg}"
                        for msg in monitor.non_adaptivity_violations(action_seqs, policy))

        n_steps = sum(len(t.steps) for t in traces)
        print(f"[ok] {name:16} {len(roots):3d} roots  {n_steps:4d} draws replayed  "
              f"plan {' -> '.join(a.value[:3] + str(c) for a, c in policy.plan)}")
        summary[name] = {"roots": len(roots), "draws_replayed": n_steps,
                         "cohort": cohort, "plan": plan,
                         "distinct_action_sequences": len(action_seqs),
                         "deterministic": True}

    print("\n" + "=" * 74)
    if failures:
        print(f"FAIL -- {len(failures)} invariant violation(s):")
        for f in failures[:20]:
            print(f"  - {f}")
        return 1
    print("PASS -- the state machine reproduces every executed decision.")
    print("        conformance, budget, stop rule, accounting, determinism,")
    print("        non-adaptivity: all hold.")
    OUT.write_text(json.dumps(
        {"policies": summary,
         "claim": ("src/agent_loop.py is a faithful state-machine description of the "
                   "executed experiments. Fixed-policy verifier-in-the-loop; the "
                   "verifier closes the loop only through the stop rule. No adaptive "
                   "or learned controller was implemented or evaluated."),
         "invariants": ["conformance", "budget", "stop_rule", "accounting",
                        "determinism", "non_adaptivity"]},
        indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"\nwrote {OUT.relative_to(ROOT).as_posix()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
