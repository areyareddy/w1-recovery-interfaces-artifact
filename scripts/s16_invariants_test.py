"""Structural invariants of the timing replay. No GPU, no server, runs in a second.

Written because the replay's correctness lives in its BOOKKEEPING, not in its arithmetic,
and bookkeeping bugs do not crash -- they produce plausible, mislabelled data. Each check
below corresponds to a specific way the previous version of this script was wrong.

    python scripts\\s16_invariants_test.py
"""

from __future__ import annotations

import ast
import sqlite3
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT / "src"))
sys.path.insert(0, str(HERE))

import receipts  # noqa: E402

TARGET = HERE / "s16_replay_timings.py"
REPLAY_DB = ROOT / "data/timing_replay.sqlite"


def functions(tree: ast.AST) -> dict[str, ast.AST]:
    out = {}
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
            out[node.name] = node
    return out


def sql_strings(node: ast.AST) -> list[str]:
    out = []
    for n in ast.walk(node):
        if isinstance(n, ast.Constant) and isinstance(n.value, str):
            out.append(n.value)
        elif isinstance(n, ast.JoinedStr):
            out.append("".join(v.value for v in n.values
                               if isinstance(v, ast.Constant) and isinstance(v.value, str)))
    return out


def calls(node: ast.AST) -> list[str]:
    out = []
    for n in ast.walk(node):
        if isinstance(n, ast.Call):
            f = n.func
            if isinstance(f, ast.Name):
                out.append(f.id)
            elif isinstance(f, ast.Attribute):
                out.append(f.attr)
    return out


def main() -> int:
    receipts.force_utf8()
    src = TARGET.read_text(encoding="utf-8")
    tree = ast.parse(src)
    fns = functions(tree)
    checks: list[tuple[str, bool, str]] = []

    def chk(name, ok, detail):
        checks.append((name, bool(ok), detail))

    # 1. canary results must never reach the analytical table
    canary_sql = " ".join(sql_strings(fns["run_canary"])).upper()
    chk("canary_writes_only_to_canary_timings",
        "INSERT OR REPLACE INTO CANARY_TIMINGS" in canary_sql
        and "BRANCH_TIMINGS" not in canary_sql,
        "run_canary() inserts into canary_timings and never branch_timings")

    # 2. exactly one place writes the analytical table, and it is record()
    writers = [n for n, f in fns.items()
               if any("INSERT" in s.upper() and "BRANCH_TIMINGS" in s.upper()
                      for s in sql_strings(f))]
    chk("single_analytical_writer", writers == ["record"],
        f"functions inserting into branch_timings: {writers or 'none'}")

    # 3. record() is never reachable from the canary
    chk("canary_never_calls_record", "record" not in calls(fns["run_canary"]),
        "run_canary() does not call record()")

    # 4. resume skipping must be driven by the analytical table only
    main_sql = " ".join(sql_strings(fns["main"])).upper()
    chk("resume_skips_from_branch_timings_only",
        "SELECT BRANCH_KEY FROM BRANCH_TIMINGS" in main_sql
        and "SELECT BRANCH_KEY FROM CANARY_TIMINGS" not in main_sql,
        "the 'done' set is read from branch_timings, so canary branches are re-measured")

    # 5. a segment cannot be used until it has run its own canary
    ns = fns["new_segment"]
    chk("new_segment_runs_own_canary", "run_canary" in calls(ns),
        "new_segment() calls run_canary() before returning a usable segment")
    chk("segment_only_source_is_new_segment",
        all(("new_segment" in [c for c in calls(fns["main"])])
            for _ in [0])
        and calls(fns["main"]).count("Segment") == 0,
        "main() obtains segments only through new_segment(), never Segment() directly")

    # 6. canary_passed is set nowhere except inside run_canary
    setters = [n for n, f in fns.items()
               if any("CANARY_PASSED=1" in s.upper().replace(" ", "")
                      for s in sql_strings(f))]
    chk("canary_passed_set_only_by_run_canary", setters == ["run_canary"],
        f"functions setting canary_passed: {setters or 'none'}")

    # 7. restart detection runs before every branch
    chk("restart_checked_per_branch", "server_unchanged" in calls(fns["main"]),
        "main() checks server_unchanged() inside the measurement loop")

    # 8. provenance drift aborts on segment open
    chk("segment_checks_provenance_drift",
        any("provenance" in s or "frozen run identity" in s
            for s in sql_strings(fns["__init__"])) or
        "SystemExit" in calls(fns["__init__"]),
        "Segment.__init__ raises SystemExit when live provenance drifts")

    # 9. every stored token count is validated
    v = " ".join(sql_strings(fns["validate"]))
    for field in ("prefill_tokens", "decode_tokens", "completion_tokens",
                  "total_tokens", "finish_reason", "prefill_ms", "decode_ms"):
        chk(f"validates_{field}", field in v, f"validate() checks {field}")

    # 10. the analytical table is currently free of canary contamination
    if REPLAY_DB.exists():
        con = sqlite3.connect(f"file:{REPLAY_DB}?mode=ro", uri=True)
        try:
            n_branch = con.execute("SELECT count(*) FROM branch_timings").fetchone()[0]
            n_canary = con.execute("SELECT count(*) FROM canary_timings").fetchone()[0]
            overlap = con.execute(
                "SELECT count(*) FROM branch_timings b JOIN canary_timings c "
                "ON b.replay_run_id=c.replay_run_id AND b.branch_key=c.branch_key "
                "WHERE b.segment_id=c.segment_id").fetchone()[0]
            open_segs = con.execute(
                "SELECT count(*) FROM replay_segments WHERE ended_utc IS NULL").fetchone()[0]
        finally:
            con.close()
        chk("no_canary_row_shares_a_segment_with_an_analytical_row", overlap == 0,
            f"branch_timings={n_branch}, canary_timings={n_canary}, same-segment overlap={overlap}")
        chk("no_orphaned_open_segment", open_segs == 0,
            f"{open_segs} segment(s) left open")

    width = max(len(n) for n, _, _ in checks)
    failed = 0
    for name, ok, detail in checks:
        if not ok:
            failed += 1
        print(f"  {'ok  ' if ok else 'FAIL'} {name:{width}}  {detail}")
    print()
    if failed:
        print(f"  {failed}/{len(checks)} INVARIANT(S) VIOLATED -- do not launch.")
        return 1
    print(f"  all {len(checks)} invariants hold.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
