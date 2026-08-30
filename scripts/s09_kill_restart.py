"""Step s09 / Gate 10 -- kill the runner mid-branch, restart, prove nothing was lost.

The primary run is hours long and will be interrupted at some point. The question this
answers is not "does the code have a try/except" but "after a hard kill, is the store
still a correct description of what was generated". Three ways that can go wrong:

  LOST      the in-flight branch stays 'running' forever and never gets generated
  DUPLICATE the in-flight branch was already recorded, and the restart generates it
            again into the same row, overwriting a real result with a second draw
  PARTIAL   a row is 'done' but some of the seven W2 resource columns are NULL

The kill is SIGKILL-equivalent (Popen.kill -> TerminateProcess on Windows), not Ctrl+C.
No cleanup handler runs, no flush happens. That is the case worth testing: a graceful
shutdown path proves nothing about a power loss.

It runs on the pilot fixture -- the 13 excluded roots in their own database -- so the 83
analysis roots are never touched and no real branch is consumed.
"""

from __future__ import annotations

import json
import sqlite3
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT / "src"))
sys.path.insert(0, str(HERE))

import pilot_common  # noqa: E402
import pipeline  # noqa: E402
import receipts  # noqa: E402

STEP = pipeline.BY_ID["s09"]
MAX_TOKENS = 4096          # short enough to keep the gate quick, long enough that some
                           # completions finish and actually reach the Lean verifier
KILL_AFTER = 2             # kill once this many branches are committed
PHASE_LIMIT = 5
RESOURCE_COLUMNS = ["model_calls", "completion_tokens", "total_tokens",
                    "prefill_tokens", "decode_tokens", "request_wall_seconds",
                    "verifier_wall_seconds"]


def counts(db: Path) -> dict[str, int]:
    con = sqlite3.connect(f"file:{db}?mode=ro", uri=True)
    out = dict(con.execute("SELECT status, count(*) FROM branches GROUP BY status"))
    con.close()
    return out


def launch(limit: int) -> subprocess.Popen:
    return subprocess.Popen(
        [sys.executable, "-u", str(HERE / "s12_run.py"),
         "--db", "data/pilot.sqlite", "--prompts", "data/pilot_prompts.jsonl",
         "--cohort", "pilot", "--max-tokens", str(MAX_TOKENS),
         "--limit", str(limit), "--no-seed-check"],
        cwd=str(ROOT), stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        text=True, encoding="utf-8", errors="replace")


def main() -> int:
    receipts.force_utf8()

    print("[1/5] building the pilot fixture (13 excluded roots, separate store)")
    branches = pilot_common.ensure(reset=True)
    db = pilot_common.PILOT_DB
    total = len(branches)
    print(f"      {total} pilot branches in {db.relative_to(ROOT).as_posix()}")

    print(f"\n[2/5] phase 1 -- run, then hard-kill after {KILL_AFTER} commits")
    proc = launch(PHASE_LIMIT)
    killed_at = None
    t0 = time.time()
    while True:
        if proc.poll() is not None:
            print("      process exited before the kill point; nothing to kill")
            break
        done = counts(db).get("done", 0)
        if done >= KILL_AFTER:
            proc.kill()
            proc.wait(timeout=30)
            killed_at = done
            print(f"      killed after {done} commit(s), {time.time() - t0:.0f}s in")
            break
        if time.time() - t0 > 900:
            proc.kill()
            print("      TIMEOUT waiting for the kill point")
            return 1
        time.sleep(2)
    try:
        proc.stdout.close()
    except Exception:  # noqa: BLE001
        pass

    mid = counts(db)
    print(f"      store right after the kill: {mid}")
    orphaned = mid.get("running", 0)
    assert orphaned <= 1, f"more than one in-flight branch ({orphaned}); one slot only"

    print("\n[3/5] phase 2 -- restart and continue")
    con = sqlite3.connect(f"file:{db}?mode=ro", uri=True)
    before = {k: (s, a) for k, s, a in
              con.execute("SELECT branch_key, status, attempt FROM branches")}
    con.close()

    proc2 = launch(PHASE_LIMIT)
    out2, _ = proc2.communicate(timeout=1800)
    print(f"      restart exit={proc2.returncode}")
    reclaimed = [l for l in out2.splitlines() if "reclaim" in l.lower()]
    for l in reclaimed[:3]:
        print(f"      {l.strip()}")

    print("\n[4/5] checks")
    con = sqlite3.connect(f"file:{db}?mode=ro", uri=True)
    after = {k: (s, a) for k, s, a in
             con.execute("SELECT branch_key, status, attempt FROM branches")}
    done_rows = list(con.execute(
        "SELECT branch_key, completion_sha256, outcome_state, "
        + ", ".join(RESOURCE_COLUMNS) + " FROM branches WHERE status='done'"))
    stuck = list(con.execute(
        "SELECT branch_key FROM branches WHERE status='running'"))
    con.close()

    checks: list[dict] = []

    def chk(name, ok, detail):
        checks.append({"check": name, "pass": bool(ok), "detail": detail})
        print(f"      {'ok  ' if ok else 'FAIL'} {name:32} {detail}")

    chk("no_branch_lost", len(after) == total,
        f"{len(after)} rows, expected {total}")
    chk("nothing_stuck_running", not stuck,
        f"{len(stuck)} row(s) left in 'running'")
    chk("progress_after_restart",
        sum(1 for v in after.values() if v[0] == "done") >
        sum(1 for v in before.values() if v[0] == "done"),
        f"{sum(1 for v in before.values() if v[0]=='done')} -> "
        f"{sum(1 for v in after.values() if v[0]=='done')} done")

    # the branch that was in flight at the kill must have been retried, i.e. claimed twice
    retried = [k for k, (s, a) in after.items()
               if a >= 2 and before.get(k, ("", 0))[0] != "done"]
    chk("interrupted_branch_retried", bool(retried) or orphaned == 0,
        f"{len(retried)} branch(es) claimed more than once: {retried[:3]}")

    # a branch that was already 'done' before the restart must not have been touched again
    resumed_over_done = [k for k, (s, a) in after.items()
                         if before.get(k, ("", 0))[0] == "done" and a != before[k][1]]
    chk("done_rows_never_regenerated", not resumed_over_done,
        f"{len(resumed_over_done)} completed row(s) re-claimed")

    incomplete = [r[0] for r in done_rows
                  if r[1] is None or any(v is None for v in r[3:])]
    chk("all_resource_columns_recorded", not incomplete,
        f"{len(done_rows)} done rows, {len(incomplete)} with a NULL column")

    print("\n[5/5] writing")
    payload = {
        "fixture": "pilot (13 excluded roots)",
        "pilot_branches": total,
        "max_tokens": MAX_TOKENS,
        "kill_signal": "Popen.kill (TerminateProcess; no cleanup handler runs)",
        "killed_after_commits": killed_at,
        "orphaned_running_at_kill": orphaned,
        "done_after": sum(1 for v in after.values() if v[0] == "done"),
        "checks": checks,
        "result": "PASS" if all(c["pass"] for c in checks) else "FAIL",
    }
    (ROOT / "audit/kill_restart.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    if not all(c["pass"] for c in checks):
        print("\n  GATE 10 FAILED. Do not start a multi-hour run on this store.")
        return 1

    receipts.write(STEP["id"], STEP["title"], STEP["inputs"], STEP["outputs"], {
        "pilot_branches": total,
        "killed_after_commits": killed_at,
        "orphaned_running_at_kill": orphaned,
        "checks_passed": len(checks),
        "done_after": payload["done_after"],
        "result": "PASS",
    })
    print(f"\n  GATE 10 PASS -- {len(checks)} checks. Safe to run unattended.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
