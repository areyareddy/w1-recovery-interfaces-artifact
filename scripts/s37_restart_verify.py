"""Step s37 -- structural verification of the restart-permissive arms. NO OUTCOMES READ.

    python scripts\\s37_restart_verify.py

This runs BEFORE any restart outcome is analysed, and deliberately reads no verification
result, so it can be run while the analysis plan is still being written.

  COMPLETENESS  120 branches, all done, one spec hash.
  ALIGNMENT     each restart arm covers exactly the 40 block-1 evaluation roots, and the
                arms cover the same roots as each other.
  SEEDS         each restart branch reuses its own arm's block-1 seed, so A-R/C-R/C'-R stay
                seed-matched to A/C/C' within root.
  CAPS          every restart branch was generated at the 12,288-token cap of the arms it
                is compared against.
  PAYLOAD       the registered substitution, re-audited from the stored prompts rather
                than trusting the builder: every restart payload must differ from its
                original by EXACTLY the commit -> restart sentence, and reversing the
                substitution must restore the original payload digest byte-for-byte.
  TIMING        prefill/decode fields are populated, so restart branches can enter the
                same accounting as everything else.

The payload check is the one that matters. If a restart prompt differs from its original in
any way other than the one registered sentence, then C-R vs C'-R is not the contrast the
design claims and no amount of downstream statistics repairs that.
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
import s32_build_restart as build  # noqa: E402

RESTART_DB = ROOT / "data/restart.sqlite"
RESTART_PROMPTS = ROOT / "data/restart_prompts.jsonl"
BASE_PROMPTS = ROOT / "data/prompts.jsonl"
CPRIME_PROMPTS = ROOT / "data/cprime_prompts.jsonl"
RUNS_DB = ROOT / "data/runs.sqlite"
OUT = ROOT / "audit/restart_verify.json"

# arm label in restart.sqlite -> source arm it is the restart-permissive twin of
SOURCE = {"AR": "A", "CR": "C", "CpR": "Cp"}


def main() -> int:
    receipts.force_utf8()
    problems: list[str] = []
    result: dict = {"reads_outcomes": False}

    print("[1/5] completeness")
    con = sqlite3.connect(f"file:{RESTART_DB}?mode=ro", uri=True)
    con.row_factory = sqlite3.Row
    rows = [dict(r) for r in con.execute("SELECT * FROM branches")]
    con.close()
    by_cohort: dict = {}
    for r in rows:
        by_cohort.setdefault(r["cohort"], []).append(r)
    for coh, rs in sorted(by_cohort.items()):
        done = sum(1 for r in rs if r["status"] == "done")
        print(f"      {coh:12} {done:3d}/{len(rs):3d} done")
        if done != len(rs):
            problems.append(f"{coh}: {len(rs) - done} not done")
    specs = {r["spec_sha256"] for r in rows if r["status"] == "done"}
    print(f"      spec hashes among done rows: {len(specs)} "
          f"({next(iter(specs))[:16] if specs else '-'})")
    if len(specs) != 1:
        problems.append(f"{len(specs)} distinct spec hashes")
    result["cohorts"] = {c: len(rs) for c, rs in by_cohort.items()}

    print("\n[2/5] root alignment against the block-1 evaluation set")
    con = sqlite3.connect(f"file:{RUNS_DB}?mode=ro", uri=True)
    block1 = {r[0] for r in con.execute(
        "SELECT DISTINCT root_id FROM branches WHERE cohort='primary_eval' AND arm='A'")}
    seeds_by_arm: dict = {}
    for arm in ("A", "C"):
        seeds_by_arm[arm] = dict(con.execute(
            "SELECT root_id, seed FROM branches WHERE cohort='primary_eval' AND arm=?",
            (arm,)))
    con.close()
    cp_con = sqlite3.connect(f"file:{ROOT / 'data/cprime.sqlite'}?mode=ro", uri=True)
    seeds_by_arm["Cp"] = dict(cp_con.execute(
        "SELECT root_id, seed FROM branches WHERE cohort='eval_cprime'"))
    cp_con.close()

    for coh, rs in sorted(by_cohort.items()):
        got = {r["root_id"] for r in rs}
        same = got == block1
        print(f"      {coh:12} {len(got):3d} roots, identical to block 1: {same}")
        if not same:
            problems.append(f"{coh}: root set differs from block 1")

    print("\n[3/5] seeds and caps")
    for coh, rs in sorted(by_cohort.items()):
        arm = rs[0]["arm"]
        src_arm = SOURCE.get(arm)
        ref = seeds_by_arm.get(src_arm, {})
        bad_seed = [r["root_id"] for r in rs if ref.get(r["root_id"]) != r["seed"]]
        caps = {r["max_tokens"] for r in rs}
        print(f"      {coh:12} arm {arm:5} seed-matched to {src_arm}: "
              f"{len(rs) - len(bad_seed)}/{len(rs)}   caps {sorted(caps)}")
        if bad_seed:
            problems.append(f"{coh}: {len(bad_seed)} seed mismatches vs arm {src_arm}")
        if caps != {12288}:
            problems.append(f"{coh}: caps {sorted(caps)}, expected {{12288}}")

    print("\n[4/5] payload: exactly the registered commit -> restart substitution")
    print(f"      commit  sha256 {receipts.sha_text(build.COMMIT)[:32]}")
    print(f"      restart sha256 {receipts.sha_text(build.RESTART)[:32]}")
    orig: dict = {}
    for ledger in (BASE_PROMPTS, CPRIME_PROMPTS):
        for line in ledger.read_text(encoding="utf-8").splitlines():
            if line.strip():
                rec = json.loads(line)
                orig[(rec["root_id"], rec["arm"])] = rec
    restart = [json.loads(l) for l in
               RESTART_PROMPTS.read_text(encoding="utf-8").splitlines() if l.strip()]
    checked = reversible = 0
    for rec in restart:
        src_arm = SOURCE[rec["arm"]]
        o = orig.get((rec["root_id"], src_arm))
        if o is None:
            problems.append(f"{rec['root_id']}/{rec['arm']}: no source payload")
            continue
        checked += 1
        msgs = rec["messages"]
        n_restart = sum(m["content"].count(build.RESTART) for m in msgs)
        n_commit = sum(m["content"].count(build.COMMIT) for m in msgs)
        if n_restart != 1 or n_commit != 0:
            problems.append(f"{rec['root_id']}/{rec['arm']}: restart x{n_restart}, "
                            f"commit x{n_commit}; expected 1 and 0")
            continue
        back = [{**m, "content": m["content"].replace(build.RESTART, build.COMMIT)}
                for m in msgs]
        digest = receipts.sha_text(json.dumps(back, ensure_ascii=False, sort_keys=True))
        if digest == o["payload_sha256"] == rec["original_payload_sha256"]:
            reversible += 1
        else:
            problems.append(f"{rec['root_id']}/{rec['arm']}: reversing the substitution "
                            "does not restore the original payload digest")
    print(f"      {checked} restart prompts checked")
    print(f"      {reversible}/{checked} restore their original digest exactly on reversal")
    result["payload_audit"] = {"checked": checked, "reversible": reversible}

    print("\n[5/5] timing fields")
    for coh, rs in sorted(by_cohort.items()):
        miss = sum(1 for r in rs if r["status"] == "done"
                   and (r["prefill_ms"] is None or r["decode_ms"] is None))
        print(f"      {coh:12} missing prefill/decode: {miss}")
        if miss:
            problems.append(f"{coh}: {miss} done branches lack phase timings")

    result["problems"] = problems
    OUT.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print("\n" + "=" * 70)
    if problems:
        print(f"FAIL -- {len(problems)} problem(s):")
        for p in problems[:20]:
            print(f"  - {p}")
        return 1
    print("PASS -- restart arms are complete, root- and seed-aligned, capped alike,")
    print("        and differ from their originals by exactly the registered sentence.")
    print(f"wrote {OUT.relative_to(ROOT).as_posix()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
