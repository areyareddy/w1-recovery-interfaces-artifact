"""Step s32 -- stage the restart-permissive robustness arms. CPU only.

    python scripts\\s32_build_restart.py

THE CONFOUND THIS ADDRESSES. W1 limitation (7): the base prompt tells the model to
"Commit to your first derivation -- do not restart the analysis or re-derive earlier steps
if you notice a possible error; fix it in place and proceed directly to the Lean 4 code."
Every arm carries it, so the design still isolates the artifact's presence -- but in arms C
and C' the "earlier derivation" sitting in context is a rejected proof, and the instruction
plausibly amplifies retention there specifically. The commitment reading is then partly a
restatement of an instruction rather than a finding.

The clean test is a restart-permissive counterpart of each arm:

                          commit (original)   restart permitted
    fresh                        A                   A-R
    mismatched attempt           C'                  C'-R
    own rejected attempt         C                   C-R

C-R vs C'-R asks whether trajectory-specific harm survives when the model is explicitly
free to abandon the attempt. Comparing that against the original C vs C' asks whether the
instruction was amplifying it.

policy.py IS NOT TOUCHED. The commit sentence lives in src/policy.py, which is a frozen
surface copied byte-identical from CoLM and verified by sync_policy.py. This script does
not edit it. It renders the ordinary prompts and performs one audited string substitution
on the rendered text, asserting for every payload that the target sentence occurs exactly
once, that exactly one substitution is made, and that reversing the substitution restores
the original payload digest byte-for-byte. A prompt whose original digest does not come
back is not staged.

RUN ORDER. Cohorts are queued C-R, C'-R, A-R. The first two carry the contrast the
experiment exists for; A-R is a rate anchor and is the arm to drop if the window runs
short, since arms A and C already supply block-1 rates under the commit instruction.
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
import s08_init_db  # noqa: E402
import s29_migrate_timings as migrate  # noqa: E402

PROMPTS = ROOT / "data/prompts.jsonl"
CPRIME_PROMPTS = ROOT / "data/cprime_prompts.jsonl"
RUNS_DB = ROOT / "data/runs.sqlite"
OUT_DB = ROOT / "data/restart.sqlite"
OUT_PROMPTS = ROOT / "data/restart_prompts.jsonl"

COMMIT = ("Commit to your first derivation -- do not restart the analysis or re-derive "
          "earlier steps if you notice a possible error; fix it in place and proceed "
          "directly to the Lean 4 code.")

RESTART = ("You may restart the analysis at any point: if you notice a possible error you "
           "are free to abandon the derivation so far -- including any earlier derivation "
           "reproduced above -- and solve the theorem independently, rather than fixing it "
           "in place.")

# cohort -> (source arm, run priority). Lower priority number runs first.
ARMS = {"C": ("restart_C", 1), "Cp": ("restart_Cp", 2), "A": ("restart_A", 3)}


def substitute(messages: list[dict], original_sha: str) -> list[dict]:
    """One audited substitution. Reversing it must restore the original digest."""
    out, hits = [], 0
    for m in messages:
        c = m["content"]
        n = c.count(COMMIT)
        hits += n
        out.append({**m, "content": c.replace(COMMIT, RESTART)} if n else dict(m))
    assert hits == 1, f"commit sentence occurs {hits} times, expected exactly 1"
    # reverse it and require the original payload back, byte for byte
    back = [{**m, "content": m["content"].replace(RESTART, COMMIT)} for m in out]
    assert receipts.sha_text(json.dumps(back, ensure_ascii=False,
                                        sort_keys=True)) == original_sha, \
        "reversing the substitution did not restore the original payload"
    return out


def main() -> int:
    receipts.force_utf8()

    print("[1/4] loading source payloads (block 1, held-out roots)")
    src: dict[tuple[str, str], dict] = {}
    for line in PROMPTS.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        r = json.loads(line)
        if r["split"] == "held_out" and r["arm"] in ("A", "C"):
            src[(r["arm"], r["root_id"])] = r
    for line in CPRIME_PROMPTS.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        r = json.loads(line)
        src[("Cp", r["root_id"])] = r
    for arm in ARMS:
        n = sum(1 for a, _ in src if a == arm)
        print(f"      arm {arm:2}: {n} payloads")
        assert n == 40, f"expected 40 payloads for arm {arm}, got {n}"

    con = sqlite3.connect(f"file:{RUNS_DB}?mode=ro", uri=True)
    seed = dict(con.execute(
        "SELECT root_id, seed FROM branches WHERE cohort='primary_eval' AND arm='A'"))
    con.close()

    print("\n[2/4] audited substitution")
    records = []
    for arm, (cohort, _) in ARMS.items():
        for (a, rid), r in sorted(src.items()):
            if a != arm:
                continue
            msgs = substitute(r["messages"], r["payload_sha256"])
            rec = dict(r)
            rec["messages"] = msgs
            rec["arm"] = f"{arm}R"
            rec["cohort"] = cohort
            rec["branch_key"] = f"{rid}|{arm}R"
            rec["seed"] = seed[rid]
            rec["seed_block"] = 1
            rec["payload_sha256"] = receipts.sha_text(
                json.dumps(msgs, ensure_ascii=False, sort_keys=True))
            rec["original_payload_sha256"] = r["payload_sha256"]
            rec["instruction_variant"] = "restart_permissive"
            records.append(rec)
    print(f"      {len(records)} payloads: commit sentence found exactly once in each,")
    print(f"      and each reverses to its original digest byte-for-byte")
    assert len({r["payload_sha256"] for r in records}) == len(records), \
        "payload collision after substitution"

    print("\n[3/4] staging")
    OUT_PROMPTS.write_text(
        "\n".join(json.dumps(r, ensure_ascii=False, sort_keys=True) for r in records)
        + "\n", encoding="utf-8")
    if OUT_DB.exists():
        chk = sqlite3.connect(f"file:{OUT_DB}?mode=ro", uri=True)
        done = chk.execute(
            "SELECT count(*) FROM branches WHERE status != 'pending'").fetchone()[0]
        chk.close()
        assert done == 0, f"{OUT_DB.name} holds {done} non-pending branches"
        OUT_DB.unlink()
        for sfx in ("-wal", "-shm"):
            side = OUT_DB.with_name(OUT_DB.name + sfx)
            if side.exists():
                side.unlink()
    con = sqlite3.connect(OUT_DB)
    con.executescript(s08_init_db.SCHEMA)
    con.close()
    migrate.migrate(OUT_DB, verbose=False)
    con = sqlite3.connect(OUT_DB)
    for r in records:
        con.execute(
            "INSERT INTO branches (branch_key, root_id, split, arm, cohort, seed_block, "
            "seed, payload_sha256, conversation_turns, fine_failure_class, "
            "coarse_failure_group, policy, max_tokens) "
            "VALUES (?,?,?,?,?,1,?,?,?,?,?,?,?)",
            (r["branch_key"], r["root_id"], r["split"], r["arm"], r["cohort"], r["seed"],
             r["payload_sha256"], r["conversation_turns"], r["fine_failure_class"],
             r["coarse_failure_group"], "restart_permissive", 12288))
    con.commit()
    for c, n in sorted(con.execute("SELECT cohort, count(*) FROM branches GROUP BY cohort")):
        print(f"      {c:14} {n:3d} branches")
    con.close()
    print(f"      {OUT_DB.relative_to(ROOT).as_posix()}")

    print("\n[4/4] instruction digests, for the record")
    print(f"      commit  sha256 : {receipts.sha_text(COMMIT)}")
    print(f"      restart sha256 : {receipts.sha_text(RESTART)}")
    print("\n  Run order: restart_C, restart_Cp, restart_A (drop A-R first if short).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
