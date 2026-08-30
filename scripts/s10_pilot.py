"""Step s10 -- full-budget end-to-end rehearsal on the 13 excluded roots.

s09 already exercised the whole path, but at max_tokens 4096. This runs the same path at
the real 12288 budget, which is where the failure modes that actually threaten an
overnight run live:

  - a long generation that fills the context and changes what the verifier receives
  - a Lean proof slow enough to hit the 180 s REPL timeout, and the REPL restart after it
  - the truncated-vs-verified outcome split at the real budget, which is what the
    runtime projection assumed

Nothing here touches the 83 analysis roots or data/runs.sqlite. It finishes whatever
s09 left pending in data/pilot.sqlite, so re-running it is free and idempotent.

The receipt is written only if every pilot branch completes with no failures and no NULL
resource column. If the rehearsal cannot finish cleanly, the primary run should not start.
"""

from __future__ import annotations

import json
import sqlite3
import subprocess
import sys
import time
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT / "src"))
sys.path.insert(0, str(HERE))

import pilot_common  # noqa: E402
import pipeline  # noqa: E402
import receipts  # noqa: E402

STEP = pipeline.BY_ID["s10"]
RESOURCE_COLUMNS = ["model_calls", "completion_tokens", "total_tokens",
                    "prefill_tokens", "decode_tokens", "request_wall_seconds",
                    "verifier_wall_seconds"]


def main() -> int:
    receipts.force_utf8()
    db = pilot_common.PILOT_DB

    print("[1/3] pilot fixture")
    branches = pilot_common.ensure(reset=False)   # keeps whatever s09 finished
    con = sqlite3.connect(f"file:{db}?mode=ro", uri=True)
    before = dict(con.execute("SELECT status, count(*) FROM branches GROUP BY status"))
    con.close()
    print(f"      {len(branches)} branches, current state {before}")

    print("\n[2/3] running the remainder at the full 12288 budget")
    t0 = time.time()
    proc = subprocess.run(
        [sys.executable, "-u", str(HERE / "s12_run.py"),
         "--db", "data/pilot.sqlite", "--prompts", "data/pilot_prompts.jsonl",
         "--cohort", "pilot", "--no-seed-check"],
        cwd=str(ROOT), text=True, encoding="utf-8", errors="replace")
    print(f"      exit={proc.returncode}, {time.time() - t0:.0f}s")

    print("\n[3/3] checks")
    con = sqlite3.connect(f"file:{db}?mode=ro", uri=True)
    status = dict(con.execute("SELECT status, count(*) FROM branches GROUP BY status"))
    outcomes = dict(con.execute(
        "SELECT outcome_state, count(*) FROM branches WHERE status='done' "
        "GROUP BY outcome_state"))
    by_arm = list(con.execute(
        "SELECT arm, outcome_state, count(*) FROM branches WHERE status='done' "
        "GROUP BY arm, outcome_state ORDER BY arm, outcome_state"))
    nulls = con.execute(
        "SELECT count(*) FROM branches WHERE status='done' AND ("
        + " OR ".join(f"{c} IS NULL" for c in RESOURCE_COLUMNS) + ")").fetchone()[0]
    timeouts = con.execute(
        "SELECT count(*) FROM branches WHERE lean_returncode=124").fetchone()[0]
    wall = con.execute(
        "SELECT sum(request_wall_seconds), sum(verifier_wall_seconds) "
        "FROM branches WHERE status='done'").fetchone()
    con.close()

    print(f"      status   {status}")
    print(f"      outcomes {outcomes}")
    for arm, state, n in by_arm:
        print(f"        {arm}  {state:14} {n}")
    print(f"      lean timeouts (rc=124): {timeouts}")
    print(f"      wall: {wall[0]:.0f}s generation + {wall[1]:.0f}s verifier")

    ok = (status.get("done", 0) == len(branches) and not status.get("failed")
          and nulls == 0)
    if not ok:
        print(f"\n  s10 INCOMPLETE -- done {status.get('done', 0)}/{len(branches)}, "
              f"failed {status.get('failed', 0)}, NULL resource columns {nulls}")
        print("  Re-run to continue, or investigate before starting the primary run.")
        return 1

    receipts.write(STEP["id"], STEP["title"], STEP["inputs"], STEP["outputs"], {
        "pilot_branches": len(branches),
        "outcomes": outcomes,
        "by_arm": {f"{a}|{s}": n for a, s, n in by_arm},
        "lean_timeouts": timeouts,
        "generation_wall_seconds": round(wall[0], 1),
        "verifier_wall_seconds": round(wall[1], 1),
        "max_tokens": 12288,
        "result": "PASS",
    })
    (ROOT / "audit/pilot_summary.json").write_text(json.dumps({
        "branches": len(branches), "status": status, "outcomes": outcomes,
        "by_arm": [{"arm": a, "outcome_state": s, "n": n} for a, s, n in by_arm],
        "lean_timeouts": timeouts,
        "generation_wall_seconds": round(wall[0], 1),
        "verifier_wall_seconds": round(wall[1], 1),
    }, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"\n  s10 PASS -- {len(branches)} pilot branches end-to-end at full budget.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
