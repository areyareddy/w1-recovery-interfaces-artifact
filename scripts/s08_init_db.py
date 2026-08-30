"""Step s08 -- create/refresh the SQLite job store. One row per branch.

Safe to re-run. It inserts branches that are missing and leaves every existing row
alone, so a half-finished generation run is never disturbed. If a branch already in the
store has a DIFFERENT payload_sha256 than data/prompts.jsonl now says, that is fatal and
the step refuses: it means completed generations in this database were produced from
prompts that no longer exist, and quietly repointing them would silently mix two
experiments.

Why SQLite rather than JSONL append. The run is 181 branches at roughly 3-8 minutes each
across many hours, and it WILL be interrupted -- Windows updates, a full disk, a wedged
REPL. What is needed is an atomic claim so a restarted worker cannot redo or skip a
branch. `UPDATE ... WHERE status='pending'` plus `changes()==1` gives exactly that; an
append-only log does not.

W2 resource columns are declared here, all seven, and the runner must fill every one:

    model_calls  completion_tokens  total_tokens  prefill_tokens
    decode_tokens  request_wall_seconds  verifier_wall_seconds

prefill and decode are kept SEPARATE from the token counts on purpose. The ~80x gap
between prefill and decode cost is the whole point of W2's accounting section, and it
disappears the moment they are summed into one "tokens" number.

Seeds are intentionally left NULL. The seed-block-2 derivation is still an open decision
(audit/step1_freeze.json), and s11 is where it gets frozen. The runner fills seeds from
the frozen spec, never from anything computed here.
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

import pipeline  # noqa: E402
import receipts  # noqa: E402

STEP = pipeline.BY_ID["s08"]
DB = ROOT / "data/runs.sqlite"
SCHEMA_VERSION = 1

SCHEMA = """
CREATE TABLE IF NOT EXISTS branches (
    branch_key            TEXT PRIMARY KEY,
    root_id               TEXT NOT NULL,
    split                 TEXT NOT NULL,
    arm                   TEXT NOT NULL,
    cohort                TEXT NOT NULL,
    seed_block            INTEGER NOT NULL DEFAULT 1,
    seed                  INTEGER,
    payload_sha256        TEXT NOT NULL,
    conversation_turns    INTEGER NOT NULL,
    fine_failure_class    TEXT,
    coarse_failure_group  TEXT,

    status                TEXT NOT NULL DEFAULT 'pending',
    attempt               INTEGER NOT NULL DEFAULT 0,
    worker                TEXT,
    claimed_at            TEXT,
    finished_at           TEXT,
    error_message         TEXT,
    spec_sha256           TEXT,

    completion            TEXT,
    completion_sha256     TEXT,
    finish_reason         TEXT,

    model_calls           INTEGER,
    completion_tokens     INTEGER,
    total_tokens          INTEGER,
    prefill_tokens        INTEGER,
    decode_tokens         INTEGER,
    request_wall_seconds  REAL,
    verifier_wall_seconds REAL,

    outcome_state         TEXT,
    verified              INTEGER,
    lean_returncode       INTEGER,
    lean_stdout           TEXT,
    lean_stderr           TEXT,
    error_class           TEXT
);

CREATE INDEX IF NOT EXISTS idx_branches_status ON branches(status);
CREATE INDEX IF NOT EXISTS idx_branches_cohort ON branches(cohort, status);
CREATE INDEX IF NOT EXISTS idx_branches_root   ON branches(root_id, arm);

CREATE TABLE IF NOT EXISTS runs (
    run_id        TEXT PRIMARY KEY,
    started_at    TEXT NOT NULL,
    finished_at   TEXT,
    cohort        TEXT NOT NULL,
    seed_block    INTEGER NOT NULL,
    spec_sha256   TEXT,
    server_config TEXT,
    host          TEXT,
    note          TEXT
);

CREATE TABLE IF NOT EXISTS events (
    id          INTEGER PRIMARY KEY AUTOINCREMENT,
    at          TEXT NOT NULL,
    run_id      TEXT,
    branch_key  TEXT,
    kind        TEXT NOT NULL,
    detail      TEXT
);
"""

RESOURCE_COLUMNS = [
    "model_calls", "completion_tokens", "total_tokens", "prefill_tokens",
    "decode_tokens", "request_wall_seconds", "verifier_wall_seconds",
]


def read_jsonl(path: Path) -> list[dict]:
    with path.open(encoding="utf-8") as fh:
        return [json.loads(line) for line in fh if line.strip()]


def cohort_of(rec: dict) -> str:
    """primary_eval is the 181-branch run: eval-40 x A/B/C/D plus E on the 21 eligible
    eval roots. Everything else is the descriptive full-pool remainder."""
    return "primary_eval" if rec["split"] == "held_out" else "full_pool_dev"


def main() -> int:
    receipts.force_utf8()

    print("[1/4] loading branch payloads")
    branches = read_jsonl(ROOT / "data/prompts.jsonl")
    print(f"      {len(branches)} branches")

    print(f"\n[2/4] opening {DB.relative_to(ROOT).as_posix()}")
    fresh = not DB.exists()
    con = sqlite3.connect(DB)
    con.execute("PRAGMA journal_mode=WAL")
    con.execute("PRAGMA synchronous=FULL")
    con.executescript(SCHEMA)
    con.execute(f"PRAGMA user_version={SCHEMA_VERSION}")
    con.commit()
    print(f"      {'created' if fresh else 'existing'}, schema v{SCHEMA_VERSION}, WAL")

    # every declared resource column must actually exist -- a typo here would surface
    # as a silently-NULL W2 column after the run, when it is far too late
    cols = {r[1] for r in con.execute("PRAGMA table_info(branches)")}
    missing = [c for c in RESOURCE_COLUMNS if c not in cols]
    assert not missing, f"resource columns missing from schema: {missing}"

    print("\n[3/4] reconciling")
    existing = {k: (p, s) for k, p, s in
                con.execute("SELECT branch_key, payload_sha256, status FROM branches")}
    conflicts, inserted, unchanged = [], 0, 0

    for rec in branches:
        key = rec["branch_key"]
        if key in existing:
            if existing[key][0] != rec["payload_sha256"]:
                conflicts.append((key, existing[key][1]))
            else:
                unchanged += 1
            continue
        con.execute(
            "INSERT INTO branches (branch_key, root_id, split, arm, cohort, "
            "payload_sha256, conversation_turns, fine_failure_class, coarse_failure_group) "
            "VALUES (?,?,?,?,?,?,?,?,?)",
            (key, rec["root_id"], rec["split"], rec["arm"], cohort_of(rec),
             rec["payload_sha256"], rec["conversation_turns"],
             rec["fine_failure_class"], rec["coarse_failure_group"]))
        inserted += 1

    if conflicts:
        con.rollback()
        con.close()
        print(f"      REFUSING: {len(conflicts)} branch(es) already in the store have a "
              f"different payload than data/prompts.jsonl now produces.")
        for key, status in conflicts[:10]:
            print(f"        {key}  (status={status})")
        print("\n  Completed rows in this database came from prompts that no longer")
        print("  exist. Repointing them would mix two experiments. Either restore the")
        print("  old prompts, or move data/runs.sqlite aside and start a clean store.")
        return 1

    con.commit()
    print(f"      inserted {inserted}, unchanged {unchanged}")

    print("\n[4/4] summary")
    rows = list(con.execute(
        "SELECT cohort, arm, count(*), sum(status='done') FROM branches "
        "GROUP BY cohort, arm ORDER BY cohort, arm"))
    for cohort, arm, n, ndone in rows:
        print(f"      {cohort:16} {arm}  {n:4d} branches   {ndone or 0} done")

    primary = con.execute(
        "SELECT count(*) FROM branches WHERE cohort='primary_eval'").fetchone()[0]
    total = con.execute("SELECT count(*) FROM branches").fetchone()[0]
    pending = con.execute(
        "SELECT count(*) FROM branches WHERE status='pending'").fetchone()[0]
    con.close()

    assert primary == 181, f"primary_eval cohort should be 181 branches, got {primary}"
    assert total == 376, f"expected 376 branches, got {total}"

    stats = {
        "schema_version": SCHEMA_VERSION,
        "branches_total": total,
        "primary_eval_cohort": primary,
        "full_pool_dev_cohort": total - primary,
        "pending": pending,
        "inserted_this_run": inserted,
        "resource_columns": RESOURCE_COLUMNS,
        "seeds": "NULL until s11 freezes the seed rule",
    }
    receipts.write(STEP["id"], STEP["title"], STEP["inputs"], STEP["outputs"], stats)
    print()
    for k, v in stats.items():
        print(f"      {k:22} {v}")
    print("\n  s08 done.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
