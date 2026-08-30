"""Step s29 -- persist phase timings at generation time. Idempotent; CPU only.

    python scripts\\s29_migrate_timings.py data/alloc_s2_eval.sqlite

WHY THIS EXISTS. src/generate.py already parses llama.cpp's `timings` block into
Result.prefill_ms / .decode_ms / .cached_tokens / .raw_timings, and src/runner.py even
computes decode_tok_per_s into its record dict -- and then record() drops every one of
them, because `branches` has no columns to hold them. That discard is the whole reason the
W2 timing replay had to exist: eight GPU-hours to recover numbers the client had already
been handed and thrown away.

Any run whose analysis needs a phase split must therefore be created with these columns
present BEFORE the first call. Adding them afterwards recovers nothing.

The added columns mirror data/timing_replay.sqlite's branch_timings, so a run recorded
this way can be analysed by the same code without a replay join:

    prefill_ms, decode_ms      the phase split
    cached_tokens, cache_n     the zero-cache-reuse gate (generate.py also hard-fails)
    raw_timings_json           the server's untouched timings block, for audit
    max_tokens                 the cap actually in force for THIS branch -- essential once
                               a design varies the cap, where a global config value lies
    policy, draw_index,        allocation-experiment bookkeeping: which policy this branch
    budget_tokens              belongs to, which draw within the root, and the per-root
                               completion-token budget the policy is spending
"""

from __future__ import annotations

import sqlite3
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT / "src"))
sys.path.insert(0, str(HERE))

import receipts  # noqa: E402

# column -> SQL type
TIMING_COLUMNS = {
    "prefill_ms": "REAL",
    "decode_ms": "REAL",
    "cached_tokens": "INTEGER",
    "cache_n": "INTEGER",
    "raw_timings_json": "TEXT",
    "max_tokens": "INTEGER",
    "policy": "TEXT",
    "draw_index": "INTEGER",
    "budget_tokens": "INTEGER",
}


def existing(con: sqlite3.Connection) -> set[str]:
    return {r[1] for r in con.execute("PRAGMA table_info(branches)")}


def migrate(db: Path, verbose: bool = True) -> list[str]:
    """Add any missing timing columns. Safe to call repeatedly and on a populated DB:
    ALTER TABLE ADD COLUMN is metadata-only in SQLite and rewrites no rows."""
    con = sqlite3.connect(db)
    try:
        have = existing(con)
        added = []
        for name, sqltype in TIMING_COLUMNS.items():
            if name not in have:
                con.execute(f"ALTER TABLE branches ADD COLUMN {name} {sqltype}")
                added.append(name)
        con.commit()
    finally:
        con.close()
    if verbose:
        rel = db.name
        if added:
            print(f"      {rel}: added {len(added)} column(s) -- {', '.join(added)}")
        else:
            print(f"      {rel}: already migrated")
    return added


def main(argv: list[str]) -> int:
    receipts.force_utf8()
    if not argv:
        print(__doc__)
        return 2
    print("[1/1] adding phase-timing columns")
    for a in argv:
        db = Path(a)
        if not db.is_absolute():
            db = ROOT / a
        if not db.exists():
            print(f"      {db} does not exist -- skipped")
            continue
        migrate(db)
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
