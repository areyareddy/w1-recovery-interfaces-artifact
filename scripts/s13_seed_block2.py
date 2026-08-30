"""Step s13 -- create the eval-40 second seed block (160 branches, A/B/C/D only).

MASTER_CORRECTION Sec.2: "second matched seed, eval-40 A/B/C/D only = +160". Arm E is
excluded on purpose. E is a positive control on a 21-root subset; a second draw of it
buys much less than a second draw of the factorial cells, and it costs the most per
branch.

WHAT A SECOND SEED BLOCK BUYS, AND WHAT IT DOES NOT. It reduces Monte-Carlo noise on a
fixed root pool: the same 40 theorems, drawn again. It does NOT buy theorem-level
generalization -- only new roots do that, which is what the dev-43 full-pool cohort is
for. So block 2 is analyzed as a REPLICATION (does the sign and rough magnitude of
C-A and D-B hold on an independent draw?), not silently pooled into block 1 to
manufacture a tighter interval on a pre-registered contrast.

Rows get their own cohort ('eval_block2') and their own branch_key suffix ('#b2') so
they can never be confused with block 1 in a query that forgets to filter on seed_block.
The payload is identical -- same prompt bytes, different seed -- so the runner strips the
suffix when it looks the payload up.
"""

from __future__ import annotations

import json
import sqlite3
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT / "src"))
sys.path.insert(0, str(HERE))

import receipts  # noqa: E402
import seeds as seeds_mod  # noqa: E402

DB = ROOT / "data/runs.sqlite"
COHORT = "eval_block2"
BLOCK = 2


def main() -> int:
    receipts.force_utf8()

    branches = [json.loads(l) for l in
                (ROOT / "data/prompts.jsonl").open(encoding="utf-8") if l.strip()]
    target = [b for b in branches
              if b["split"] == "held_out" and b["arm"] in ("A", "B", "C", "D")]
    assert len(target) == 160, f"expected 160 eval A/B/C/D branches, got {len(target)}"

    con = sqlite3.connect(DB, timeout=60)
    con.execute("PRAGMA busy_timeout=60000")
    root_ids = [r[0] for r in con.execute("SELECT DISTINCT root_id FROM branches "
                                          "WHERE seed_block=1")]
    seed_of = seeds_mod.all_seeds(root_ids, block=BLOCK)

    inserted = 0
    con.execute("BEGIN IMMEDIATE")
    for b in target:
        key = f"{b['branch_key']}#b{BLOCK}"
        cur = con.execute(
            "INSERT OR IGNORE INTO branches (branch_key, root_id, split, arm, cohort, "
            "seed_block, seed, payload_sha256, conversation_turns, fine_failure_class, "
            "coarse_failure_group) VALUES (?,?,?,?,?,?,?,?,?,?,?)",
            (key, b["root_id"], b["split"], b["arm"], COHORT, BLOCK,
             seed_of[b["root_id"]], b["payload_sha256"], b["conversation_turns"],
             b["fine_failure_class"], b["coarse_failure_group"]))
        inserted += cur.rowcount
    con.execute("COMMIT")

    n = con.execute("SELECT count(*) FROM branches WHERE cohort=?", (COHORT,)).fetchone()[0]
    lo, hi = con.execute("SELECT min(seed), max(seed) FROM branches WHERE cohort=?",
                         (COHORT,)).fetchone()
    shared = con.execute(
        "SELECT count(*) FROM (SELECT root_id, count(DISTINCT seed) c FROM branches "
        "WHERE cohort=? GROUP BY root_id) WHERE c != 1", (COHORT,)).fetchone()[0]
    overlap = con.execute(
        "SELECT count(*) FROM branches b1 JOIN branches b2 ON b1.seed=b2.seed "
        "WHERE b1.seed_block=1 AND b2.seed_block=2").fetchone()[0]
    con.close()

    assert n == 160, f"cohort {COHORT} should hold 160 branches, has {n}"
    assert shared == 0, "all arms of a root must share one block-2 seed"
    assert overlap == 0, "block 1 and block 2 seeds must not overlap"

    print(f"      cohort {COHORT}: {n} branches ({inserted} inserted this run)")
    print(f"      block {BLOCK} seeds {lo}..{hi}, no overlap with block 1")
    print(f"      arms A/B/C/D only; E excluded by design")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
