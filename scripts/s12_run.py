"""Step s12 -- generate and verify a cohort of branches. Resumable; safe to re-run.

    python scripts\\s12_run.py                       the primary 181, seed block 1
    python scripts\\s12_run.py --limit 4             a short rehearsal
    python scripts\\s12_run.py --cohort full_pool_dev  the descriptive remainder

Kill it at any point (Ctrl+C, power loss, a crash). Re-running picks up exactly where it
stopped: finished branches are already committed, and the one branch that was in flight
goes back to 'pending' on the next start. Nothing is generated twice into the same row.

Progress is visible from a second terminal at any time, because the counters live in
SQLite rather than in this process:

    python scripts\\status.py --watch 600

The receipt is written only when the cohort is FULLY complete. A partially finished run
leaves s12 showing as pending with a live branch count, which is the honest state.
"""

from __future__ import annotations

import argparse
import json
import sqlite3
import sys
import time
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT / "src"))
sys.path.insert(0, str(HERE))

import anchoring  # noqa: E402
import pipeline  # noqa: E402
import receipts  # noqa: E402
import runner as runner_mod  # noqa: E402

STEP = pipeline.BY_ID["s12"]


def fmt_hms(seconds: float) -> str:
    h, rem = divmod(int(max(0, seconds)), 3600)
    m, s = divmod(rem, 60)
    return f"{h:d}h{m:02d}m{s:02d}s"


def main(argv: list[str]) -> int:
    receipts.force_utf8()
    ap = argparse.ArgumentParser()
    ap.add_argument("--config", default="configs/primary.json")
    ap.add_argument("--db", default="data/runs.sqlite")
    ap.add_argument("--prompts", default="data/prompts.jsonl")
    ap.add_argument("--cohort", default="primary_eval")
    ap.add_argument("--block", type=int, default=1)
    ap.add_argument("--max-tokens", type=int, default=None)
    ap.add_argument("--limit", type=int, default=None)
    ap.add_argument("--no-seed-check", action="store_true",
                    help="rehearsal only; the real run must have frozen seeds")
    ap.add_argument("--blind", action="store_true",
                    help="print NO outcome of any kind -- required for a cohort under "
                         "an inspection rule, because this stdout is redirected into a "
                         "plaintext job log. Progress and errors still print.")
    args = ap.parse_args(argv)

    cfg = json.loads((ROOT / args.config).read_text(encoding="utf-8"))
    base_url = cfg["server"]["url"]
    max_tokens = args.max_tokens or cfg["generation"]["max_tokens"]

    print(f"[1/3] preflight")
    live, detail = anchoring.ServerTokenizer(base_url).probe()
    if not live:
        print(f"      server unavailable: {detail}")
        print("      powershell -NoProfile -File scripts\\start_server.ps1")
        return 2
    print(f"      server: {detail}")

    spec_sha = None
    spec_file = ROOT / "spec/frozen_spec.sha256"
    if spec_file.exists():
        spec_sha = spec_file.read_text(encoding="utf-8").split()[0]
        print(f"      spec:   {spec_sha[:16]}")
    elif not args.no_seed_check:
        print("      no spec/frozen_spec.sha256 -- run scripts/s11_freeze_spec.py first,")
        print("      or pass --no-seed-check for a rehearsal.")
        return 2

    db = ROOT / args.db
    r = runner_mod.Runner(
        db_path=db,
        prompts_path=ROOT / args.prompts,
        roots_path=ROOT / "data/roots.jsonl",
        lean_cfg=cfg["lean"], base_url=base_url, max_tokens=max_tokens,
        spec_sha256=spec_sha, require_seed=not args.no_seed_check)
    print(f"      db:     {db.relative_to(ROOT).as_posix()}")
    print(f"      cohort: {args.cohort}  block {args.block}  max_tokens {max_tokens}")
    print(f"      worker: {r.worker}")

    print(f"\n[2/3] running")
    t0 = time.time()
    seen = Counter()

    def on_branch(rec: dict, done: int, total: int) -> None:
        seen[rec["outcome_state"]] += 1
        elapsed = time.time() - t0
        rate = elapsed / max(1, done - (done - sum(seen.values())))
        eta = rate * (total - done)
        if args.blind:
            # No mark, no outcome_state, and no token or wall-time figures: a branch that
            # stops exactly at the cap is a truncation tell, and wall time tracks it.
            print(f"      {done:3d}/{total} ({100 * done // total:3d}%) "
                  f"{rec['branch_key']:52} ETA {fmt_hms(eta)}", flush=True)
            return
        mark = "OK " if rec["verified"] else "   "
        print(f"      {done:3d}/{total} ({100 * done // total:3d}%) {mark}"
              f"{rec['branch_key']:52} {rec['outcome_state']:12} "
              f"{rec['completion_tokens']:5d}tok "
              f"{rec['request_wall_seconds']:5.1f}s+{rec['verifier_wall_seconds']:5.1f}s "
              f"ETA {fmt_hms(eta)}", flush=True)

    try:
        summary = r.run(args.cohort, seed_block=args.block, limit=args.limit,
                        on_branch=on_branch)
    except KeyboardInterrupt:
        print("\n      interrupted -- the in-flight branch returns to pending on restart.")
        return 130

    print(f"\n[3/3] summary")
    for k, v in summary.items():
        print(f"      {k:18} {v}")
    if args.blind:
        print("      outcomes: WITHHELD (--blind)")
    else:
        print(f"      outcomes: {dict(sorted(seen.items()))}")

    con = sqlite3.connect(f"file:{db}?mode=ro", uri=True)
    rows = list(con.execute(
        "SELECT arm, outcome_state, count(*) FROM branches "
        "WHERE cohort=? AND seed_block=? AND status='done' GROUP BY arm, outcome_state "
        "ORDER BY arm, outcome_state", (args.cohort, args.block)))
    verified = dict(con.execute(
        "SELECT arm, sum(verified) FROM branches WHERE cohort=? AND seed_block=? "
        "AND status='done' GROUP BY arm", (args.cohort, args.block)))
    n_by_arm = dict(con.execute(
        "SELECT arm, count(*) FROM branches WHERE cohort=? AND seed_block=? "
        "AND status='done' GROUP BY arm", (args.cohort, args.block)))
    incomplete = con.execute(
        "SELECT count(*) FROM branches WHERE cohort=? AND seed_block=? AND status!='done'",
        (args.cohort, args.block)).fetchone()[0]
    con.close()

    print()
    if args.blind:
        print(f"      {sum(n_by_arm.values())} branch(es) done across "
              f"{len(n_by_arm)} arm(s)")
        print("      per-arm outcome table and verified counts: WITHHELD (--blind)")
        print("      read them only through the frozen analysis for this cohort")
    else:
        for arm, state, n in rows:
            print(f"      {arm}  {state:14} {n:4d}")
        print()
        for arm in sorted(n_by_arm):
            v = verified.get(arm) or 0
            print(f"      arm {arm}: verified {v}/{n_by_arm[arm]} "
                  f"({100 * v / n_by_arm[arm]:.1f}%)")

    if incomplete:
        print(f"\n  {incomplete} branch(es) still incomplete -- re-run to continue.")
        print("  No receipt written; s12 stays pending with a live count.")
        return 0

    # A receipt carries verified_by_arm, so a blinded cohort must never write one.
    # The cohort test below already excludes them; this is belt and braces.
    if (args.cohort == "primary_eval" and args.block == 1
            and not args.no_seed_check and not args.blind):
        receipts.write(STEP["id"], STEP["title"], STEP["inputs"], STEP["outputs"], {
            "cohort": args.cohort, "seed_block": args.block,
            "branches": sum(n_by_arm.values()),
            "verified_by_arm": {a: (verified.get(a) or 0) for a in sorted(n_by_arm)},
            "n_by_arm": n_by_arm,
            "spec_sha256": spec_sha,
            "elapsed_seconds": summary["elapsed_seconds"],
            "max_tokens": max_tokens,
        })
        print("\n  s12 done -- cohort complete, receipt written.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
