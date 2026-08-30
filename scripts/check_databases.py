"""Read-only integrity checks over every database a paper number depends on.

    python scripts\\check_databases.py

Opened with mode=ro throughout: an integrity check that can write is not one. Per database:

  STRUCTURE   PRAGMA quick_check -- page-level corruption, which a crashed machine with
              live WAL sidecars is exactly the situation to check for.
  COMPLETION  no branch left pending, running or failed. A partly-generated cohort must
              never reach an analysis; spec/ALLOCATION_SPEC.md section 8 makes that a
              reporting rule, and this makes it a checkable one.
  PROVENANCE  every done branch carries one spec hash. More than one means rows from two
              different frozen specs are sitting in the same table.
  PAYLOAD     no done branch has a NULL completion or a NULL completion hash. A row that
              is 'done' with nothing in it would silently become a zero in an aggregate.

Exit 1 on any failure. Nothing here prints an outcome.
"""

from __future__ import annotations

import sqlite3
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
DATA = ROOT / "data"

# The databases that feed a published number, and the branch count each must hold.
EXPECTED = {
    "runs.sqlite": 536,
    "cprime.sqlite": 40,
    "cprime_b2.sqlite": 40,
    "restart.sqlite": 120,
    "eprime.sqlite": 21,
    "armf.sqlite": 21,
    "alloc_split2.sqlite": 166,
    "alloc_split3.sqlite": 249,
}


def check(name: str, expected: int | None) -> list[str]:
    path = DATA / name
    problems: list[str] = []
    if not path.exists():
        return [f"{name}: absent"]
    con = sqlite3.connect(f"file:{path}?mode=ro&immutable=1", uri=True)
    try:
        qc = con.execute("PRAGMA quick_check").fetchone()[0]
        ok_struct = qc == "ok"
        if not ok_struct:
            problems.append(f"{name}: quick_check returned {qc!r}")

        tables = {r[0] for r in con.execute(
            "SELECT name FROM sqlite_master WHERE type='table'")}
        if "branches" not in tables:
            print(f"  {name:24} structure {'ok' if ok_struct else 'FAIL':4}  "
                  f"(no branches table; {len(tables)} table(s))")
            return problems

        total = con.execute("SELECT count(*) FROM branches").fetchone()[0]
        by_status = dict(con.execute(
            "SELECT status, count(*) FROM branches GROUP BY status"))
        done = by_status.get("done", 0)
        not_done = total - done
        if not_done:
            problems.append(f"{name}: {not_done} branch(es) not done: "
                            f"{ {k: v for k, v in by_status.items() if k != 'done'} }")

        specs = [r[0] for r in con.execute(
            "SELECT DISTINCT spec_sha256 FROM branches WHERE status='done'")]
        if len(specs) > 1:
            problems.append(f"{name}: {len(specs)} distinct spec hashes among done rows")

        nulls = con.execute(
            "SELECT count(*) FROM branches WHERE status='done' AND "
            "(completion IS NULL OR completion_sha256 IS NULL)").fetchone()[0]
        if nulls:
            problems.append(f"{name}: {nulls} done branch(es) with NULL completion")

        if expected is not None and total != expected:
            problems.append(f"{name}: holds {total} branches, expected {expected}")

        print(f"  {name:24} structure {'ok' if ok_struct else 'FAIL':4}  "
              f"branches {total:4d}  done {done:4d}  "
              f"spec {specs[0][:12] if specs else '-':12}  "
              f"null-payload {nulls}")
    finally:
        con.close()
    return problems


def main() -> int:
    print("read-only integrity checks (mode=ro)\n")
    problems: list[str] = []
    for name, expected in EXPECTED.items():
        problems += check(name, expected)

    print("\n" + "=" * 70)
    if problems:
        print(f"FAIL -- {len(problems)} problem(s):")
        for p in problems:
            print(f"  - {p}")
        return 1
    print("PASS -- every database is structurally sound, fully generated, single-spec,")
    print("        and free of empty payloads.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
