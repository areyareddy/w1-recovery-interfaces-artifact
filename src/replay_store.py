"""Storage for the timing replay. A SEPARATE database file; runs.sqlite is never opened
for writing by any part of the replay.

Three tables, and the segment table is the one that carries the scientific weight.

replay_runs      one row per replay attempt, holding a FROZEN RUN IDENTITY: spec hash,
                 prompts hash, sampler, max_tokens, server build, model file identity,
                 chat-template hash, server arguments. A resumed replay may only join a
                 run whose identity hash is identical -- otherwise measurements taken
                 under different configurations could be silently pooled.

replay_segments  one row per CONTIGUOUS MEASUREMENT PERIOD. A server restart ends a
                 segment and opens a new one, because a restarted server is a different
                 timing regime: cold caches, fresh allocator state, possibly a different
                 build. Determinism makes the TEXT identical across a restart; it says
                 nothing about the milliseconds. Any timing analysis must be able to
                 group by segment and check that conclusions do not depend on it.

branch_timings   the measurements, keyed by (replay_run_id, branch_key) so the same
                 branch measured under two run identities cannot collide.
"""

from __future__ import annotations

import json
import sqlite3
from pathlib import Path

SCHEMA = """
CREATE TABLE IF NOT EXISTS replay_runs (
    replay_run_id        TEXT PRIMARY KEY,
    identity_sha256      TEXT NOT NULL,
    started_utc          TEXT NOT NULL,
    finished_utc         TEXT,
    status               TEXT NOT NULL DEFAULT 'open',
    spec_sha256          TEXT NOT NULL,
    prompts_sha256       TEXT NOT NULL,
    roots_sha256         TEXT NOT NULL,
    source_db_sha256     TEXT NOT NULL,
    sampler_json         TEXT NOT NULL,
    max_tokens           INTEGER NOT NULL,
    llama_build          TEXT NOT NULL,
    model_path           TEXT NOT NULL,
    model_ftype          TEXT NOT NULL,
    chat_template_sha256 TEXT NOT NULL,
    n_ctx                INTEGER NOT NULL,
    total_slots          INTEGER NOT NULL,
    server_args_json     TEXT NOT NULL,
    note                 TEXT
);

CREATE TABLE IF NOT EXISTS replay_segments (
    segment_id       INTEGER PRIMARY KEY AUTOINCREMENT,
    replay_run_id    TEXT NOT NULL,
    started_utc      TEXT NOT NULL,
    ended_utc        TEXT,
    open_reason      TEXT NOT NULL,
    close_reason     TEXT,
    llama_build      TEXT NOT NULL,
    provenance_json  TEXT NOT NULL,
    canary_passed    INTEGER NOT NULL DEFAULT 0,
    server_pid       INTEGER,
    server_started   REAL,
    canary_json      TEXT,
    warmup_calls     INTEGER NOT NULL DEFAULT 0,
    branches_measured INTEGER NOT NULL DEFAULT 0
);

CREATE TABLE IF NOT EXISTS branch_timings (
    replay_run_id       TEXT NOT NULL,
    branch_key          TEXT NOT NULL,
    segment_id          INTEGER NOT NULL,
    cohort              TEXT NOT NULL,
    root_id             TEXT NOT NULL,
    arm                 TEXT NOT NULL,
    seed_block          INTEGER NOT NULL,
    seed                INTEGER NOT NULL,
    max_tokens          INTEGER NOT NULL,

    prefill_ms          REAL NOT NULL,
    decode_ms           REAL NOT NULL,
    prefill_tokens      INTEGER NOT NULL,
    decode_tokens       INTEGER NOT NULL,
    completion_tokens   INTEGER NOT NULL,
    total_tokens        INTEGER NOT NULL,
    request_wall_seconds REAL NOT NULL,

    cache_n             INTEGER NOT NULL,
    cached_tokens       INTEGER NOT NULL,
    finish_reason       TEXT NOT NULL,
    completion_sha256   TEXT NOT NULL,
    original_sha256     TEXT NOT NULL,
    hash_match          INTEGER NOT NULL,

    raw_timings_json    TEXT NOT NULL,
    replayed_utc        TEXT NOT NULL,
    PRIMARY KEY (replay_run_id, branch_key)
);

CREATE INDEX IF NOT EXISTS idx_timings_segment ON branch_timings(segment_id);
CREATE INDEX IF NOT EXISTS idx_timings_arm ON branch_timings(arm, cohort);

-- Canary rows are DIAGNOSTIC ONLY and live in their own table.
-- They must never enter the analytical set: a canary measures an unmatched handful of
-- branches whose paired A/C and B/D partners are measured hours later under different
-- thermal and scheduling conditions, so pairing them would compare across time rather
-- than across arm.
CREATE TABLE IF NOT EXISTS canary_timings (
    replay_run_id       TEXT NOT NULL,
    segment_id          INTEGER NOT NULL,
    branch_key          TEXT NOT NULL,
    cohort              TEXT NOT NULL,
    root_id             TEXT NOT NULL,
    arm                 TEXT NOT NULL,
    seed_block          INTEGER NOT NULL,
    prefill_ms          REAL NOT NULL,
    decode_ms           REAL NOT NULL,
    prefill_tokens      INTEGER NOT NULL,
    decode_tokens       INTEGER NOT NULL,
    completion_tokens   INTEGER NOT NULL,
    request_wall_seconds REAL NOT NULL,
    completion_sha256   TEXT NOT NULL,
    original_sha256     TEXT NOT NULL,
    hash_match          INTEGER NOT NULL,
    raw_timings_json    TEXT NOT NULL,
    measured_utc        TEXT NOT NULL,
    PRIMARY KEY (replay_run_id, segment_id, branch_key)
);

CREATE TABLE IF NOT EXISTS replay_events (
    id            INTEGER PRIMARY KEY AUTOINCREMENT,
    at            TEXT NOT NULL,
    replay_run_id TEXT,
    segment_id    INTEGER,
    kind          TEXT NOT NULL,
    detail        TEXT
);
"""


def connect(path: Path) -> sqlite3.Connection:
    con = sqlite3.connect(path, timeout=60, isolation_level=None)
    con.execute("PRAGMA journal_mode=WAL")
    con.execute("PRAGMA synchronous=FULL")
    con.execute("PRAGMA busy_timeout=60000")
    con.executescript(SCHEMA)
    return con


def backup(source: Path, dest: Path) -> tuple[int, str]:
    """SQLite's own backup API, then reopen and integrity-check the copy.

    A plain file copy of a WAL database can capture a torn state: the -wal file holds
    committed pages the main file does not yet have. The backup API takes a consistent
    snapshot through the same locking protocol the database itself uses."""
    src = sqlite3.connect(f"file:{source}?mode=ro", uri=True)
    dst = sqlite3.connect(dest)
    with dst:
        src.backup(dst)
    dst.close()
    src.close()

    check = sqlite3.connect(f"file:{dest}?mode=ro", uri=True)
    integrity = check.execute("PRAGMA integrity_check").fetchone()[0]
    rows = check.execute("SELECT count(*) FROM branches").fetchone()[0]
    check.close()
    return rows, integrity


def event(con: sqlite3.Connection, run_id: str | None, segment_id: int | None,
          kind: str, detail: str = "") -> None:
    import time
    con.execute("INSERT INTO replay_events (at, replay_run_id, segment_id, kind, detail) "
                "VALUES (?,?,?,?,?)",
                (time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
                 run_id, segment_id, kind, json.dumps(detail) if not isinstance(detail, str) else detail))
