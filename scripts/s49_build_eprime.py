"""Step s49 -- stage arm E', native correction content in ONE turn. CPU only.

Governed by spec/EPRIME_SPEC.md, frozen before this script staged anything.

THE OBJECTION. Arm C shows the failed proof and says nothing about why it failed. For
a checkpoint trained on verifier-guided self-correction that withholds exactly the signal
the model expects, so the C-A deficit is consistent both with anchoring on the rejected
trajectory and with C simply being off-distribution. E' supplies the diagnosis and holds
everything else that can be held.

    C  = WRAPPER(own attempt)                          + OFFICIAL(theorem)
    E' = WRAPPER'(own attempt) + CORRECTION_TURN(errs) + OFFICIAL(theorem)
    E  = three turns: OFFICIAL(theorem) / attempt / CORRECTION_TURN(errs)

so  E' - C  isolates the diagnosis, one turn held fixed
    E' - A  is the deployed configuration against fresh generation
    E' - E  is conversation structure alone, content byte-identical

WHAT THIS SCRIPT REFUSES TO DO. It does not touch prompts.ARMS, data/prompts.jsonl or
data/runs.sqlite. Arm E's three-turn path must remain byte-identical, so gate 4 rebuilds
that root's arm-E payload and asserts the correction turn E' embeds is the same string.
The frozen A/B/C prompts are re-derived and compared against data/prompts.jsonl (gate 0),
so if adding E' perturbed the shared prompt surface by one byte, this aborts.
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

import goedel_native  # noqa: E402
import policy  # noqa: E402
import prompts  # noqa: E402
import receipts  # noqa: E402
import s08_init_db  # noqa: E402

EPRIME_DB = ROOT / "data/eprime.sqlite"
EPRIME_PROMPTS = ROOT / "data/eprime_prompts.jsonl"
ELIGIBILITY_CSV = ROOT / "audit/eprime_eligibility.csv"
COHORT = "eval_eprime"
ARM = "Ep"
PREV_ROUND = 1  # identical to s02_build_prompts.py; part of the arm-E prompt text
EXPECTED_ROOTS = 21


def read_jsonl(path: Path) -> list[dict]:
    with path.open(encoding="utf-8") as fh:
        return [json.loads(line) for line in fh if line.strip()]


def main() -> int:
    receipts.force_utf8()

    print("[1/5] loading roots and the frozen prompt set")
    roots = {r["root_id"]: r for r in read_jsonl(ROOT / "data/roots.jsonl")
             if r["split"] == "held_out"}
    assert len(roots) == 40, f"expected 40 held-out roots, got {len(roots)}"
    frozen = read_jsonl(ROOT / "data/prompts.jsonl")
    by_arm: dict[tuple[str, str], dict] = {}
    for rec in frozen:
        by_arm[(rec["root_id"], rec["arm"])] = rec

    # ---- gate 0: adding E' must not have perturbed the shared prompt surface --------
    n_checked = 0
    for rid, rec in sorted(roots.items()):
        theorem = rec["theorem_text"]
        raw = (ROOT / "artifacts/roots" / rid / "raw_completion.txt").read_text(
            encoding="utf-8")
        for arm, built in (("A", policy.official_prompt(theorem)),
                           ("C", prompts.wrapper_block(raw)
                            + policy.official_prompt(theorem))):
            ref = by_arm.get((rid, arm))
            if ref is None:
                continue
            assert ref["messages"][0]["content"] == built, (
                f"{rid}/{arm}: re-derived prompt differs from data/prompts.jsonl. "
                "The shared prompt surface changed -- do not generate anything.")
            n_checked += 1
    print(f"      gate 0 ok: {n_checked} frozen A/C prompts re-derive byte-identically")

    print("\n[2/5] selecting eligible roots (native_error only)")
    eligible = []
    for rid, rec in sorted(roots.items()):
        if rec["native_feedback_available"]:
            eligible.append(rid)
    assert len(eligible) == EXPECTED_ROOTS, (
        f"expected {EXPECTED_ROOTS} eligible held-out roots, got {len(eligible)}: "
        f"{eligible}")
    print(f"      {len(eligible)} of 40 held-out roots carry a native compiler error")
    print(f"      the other {40 - len(eligible)} have no compilable proof, so no error "
          "exists -- a corpus ceiling, not a sampling choice")

    print("\n[3/5] rebuilding feedback and building E' prompts")
    seeds = {}
    con = sqlite3.connect(f"file:{ROOT / 'data/runs.sqlite'}?mode=ro", uri=True)
    for rid, seed in con.execute(
            "SELECT root_id, seed FROM branches WHERE cohort='primary_eval' AND arm='A'"):
        seeds[rid] = seed
    con.close()
    assert all(rid in seeds for rid in eligible), "missing a frozen arm-A seed"

    records, rows = [], []
    wrapper_sha = receipts.sha_text(prompts.EPRIME_PRIOR_ATTEMPT_WRAPPER)
    c_head = prompts.NEUTRAL_PRIOR_ATTEMPT_WRAPPER.split("{prior_attempt}")[0]
    c_tail = prompts.NEUTRAL_PRIOR_ATTEMPT_WRAPPER.split("{prior_attempt}")[1]
    ep_head = prompts.EPRIME_PRIOR_ATTEMPT_WRAPPER.split("{prior_attempt}")[0]
    ep_tail = prompts.EPRIME_PRIOR_ATTEMPT_WRAPPER.split("{prior_attempt}")[1]

    for rid in eligible:
        rec = roots[rid]
        theorem = rec["theorem_text"]
        adir = ROOT / "artifacts/roots" / rid
        raw = (adir / "raw_completion.txt").read_text(encoding="utf-8")

        # rebuild the native feedback exactly as s02_build_prompts.py does
        stdout = (adir / "lean_stdout.json").read_text(encoding="utf-8")
        errors = goedel_native.repl_errors(stdout)
        extracted = (adir / "extracted_prior.lean").read_text(encoding="utf-8")
        code = goedel_native.submitted_code(extracted)
        feedback, error_block, kind = goedel_native.build_feedback(
            rec["outcome_state"], code, errors, prev_round=PREV_ROUND)

        # ---- gate 1: eligibility is native, never synthesised
        assert kind == "native_error", f"{rid}: E' built from non-native kind {kind!r}"
        # ---- gate 6: the rebuilt error block matches the frozen hash
        assert receipts.sha_text(error_block) == rec["native_feedback_sha256"], \
            f"{rid}: rebuilt <error> block differs from native_feedback_sha256"

        base = policy.official_prompt(theorem)
        prompt_ep = prompts.eprime_prompt(theorem, raw, feedback)
        prompt_c = prompts.wrapper_block(raw) + base

        # ---- gate 2: E' ends with OFFICIAL(theorem), byte-identical to arm A
        assert prompt_ep.endswith(base), f"{rid}: E' does not end with OFFICIAL(theorem)"
        assert by_arm[(rid, "A")]["messages"][0]["content"] == base, \
            f"{rid}: base prompt differs from frozen arm A"
        # ---- gate 3: the <previous_attempt> segment is byte-identical to arm C's
        c_seg = c_head.split("\n\n", 1)[1] + raw + c_tail
        ep_seg = ep_head.split("\n\n", 1)[1] + raw + ep_tail
        assert c_seg == ep_seg, (
            f"{rid}: the <previous_attempt> segment of E' differs from C's. Only the "
            "announcing sentence may differ between the two wrappers.")
        assert raw in prompt_ep, f"{rid}: prior attempt missing from E'"
        assert prompt_c.startswith(c_head) and prompt_ep.startswith(ep_head), \
            f"{rid}: wrapper header differs"
        # ---- gate 4: the correction turn is byte-identical to arm E's third turn
        e_ref = by_arm.get((rid, "E"))
        assert e_ref is not None, f"{rid}: eligible for E' but has no frozen arm-E payload"
        assert len(e_ref["messages"]) == 3, f"{rid}: frozen arm E is not three turns"
        assert e_ref["messages"][2]["content"] == feedback, (
            f"{rid}: rebuilt correction turn differs from frozen arm E's third turn. "
            "E' would then be a different treatment from E.")
        assert e_ref["messages"][1]["content"] == raw, \
            f"{rid}: frozen arm E's assistant turn is not this root's attempt"
        assert feedback in prompt_ep, f"{rid}: correction turn missing from E'"
        # ---- gate 5: exact reconstruction
        assert prompt_ep == ep_head + raw + ep_tail + feedback + "\n\n" + base, \
            f"{rid}: E' is not exactly wrapper + attempt + correction + base"

        messages = [{"role": "user", "content": prompt_ep}]
        records.append({
            "branch_key": f"{rid}|{ARM}",
            "root_id": rid, "split": "held_out", "arm": ARM, "cohort": COHORT,
            "seed": seeds[rid],
            "messages": messages,
            "conversation_turns": 1,
            "payload_chars": len(prompt_ep),
            "payload_sha256": receipts.sha_text(
                json.dumps(messages, ensure_ascii=False, sort_keys=True)),
            "wrapper_sha256": wrapper_sha,
            "base_prompt_sha256": receipts.sha_text(base),
            "native_feedback_sha256": rec["native_feedback_sha256"],
            "fine_failure_class": rec["fine_failure_class"],
            "coarse_failure_group": rec["coarse_failure_group"],
        })
        rows.append({"root_id": rid, "seed": seeds[rid],
                     "prompt_chars": len(prompt_ep),
                     "c_prompt_chars": len(prompt_c),
                     "error_block_chars": len(error_block),
                     "fine_failure_class": rec["fine_failure_class"],
                     "coarse_failure_group": rec["coarse_failure_group"]})

    grew = [r["prompt_chars"] - r["c_prompt_chars"] for r in rows]
    print(f"      {len(records)} prompts built, all gates passed")
    print(f"      E' is longer than C by {min(grew)}..{max(grew)} chars "
          f"(the correction turn); this is disclosed, not controlled")

    print("\n[4/5] writing prompts and eligibility record")
    with EPRIME_PROMPTS.open("w", encoding="utf-8", newline="\n") as fh:
        for r in records:
            fh.write(json.dumps(r, ensure_ascii=False, sort_keys=True) + "\n")
    import csv
    with ELIGIBILITY_CSV.open("w", encoding="utf-8", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)

    print("\n[5/5] staging the job store (separate database)")
    if EPRIME_DB.exists():
        chk = sqlite3.connect(f"file:{EPRIME_DB}?mode=ro", uri=True)
        done = chk.execute(
            "SELECT count(*) FROM branches WHERE status != 'pending'").fetchone()[0]
        chk.close()
        assert done == 0, (
            f"{EPRIME_DB.name} already holds {done} non-pending branches. Refusing to "
            "rebuild: that would discard generated data. Move it aside deliberately.")
        stamp = __import__("time").strftime("%Y%m%dT%H%M%S")
        moved = ROOT / "Backup" / f"eprime.sqlite.{stamp}.prerebuild"
        EPRIME_DB.replace(moved)
        for suffix in ("-wal", "-shm"):
            side = EPRIME_DB.with_name(EPRIME_DB.name + suffix)
            if side.exists():
                side.unlink()
        print(f"      previous empty store moved to Backup/{moved.name}")

    con = sqlite3.connect(EPRIME_DB)
    con.execute("PRAGMA journal_mode=WAL")
    con.executescript(s08_init_db.SCHEMA)
    for r in records:
        con.execute(
            "INSERT OR IGNORE INTO branches (branch_key, root_id, split, arm, cohort, "
            "seed_block, seed, payload_sha256, conversation_turns, fine_failure_class, "
            "coarse_failure_group) VALUES (?,?,?,?,?,1,?,?,?,?,?)",
            (r["branch_key"], r["root_id"], r["split"], r["arm"], COHORT, r["seed"],
             r["payload_sha256"], r["conversation_turns"], r["fine_failure_class"],
             r["coarse_failure_group"]))
    con.commit()
    n = con.execute("SELECT count(*) FROM branches").fetchone()[0]
    con.close()
    assert n == EXPECTED_ROOTS, f"expected {EXPECTED_ROOTS} staged branches, got {n}"

    print(f"      {EPRIME_DB.relative_to(ROOT).as_posix()}: {n} branches pending")
    print(f"      {EPRIME_PROMPTS.relative_to(ROOT).as_posix()}")
    print(f"      {ELIGIBILITY_CSV.relative_to(ROOT).as_posix()}")
    print("\nnext: python scripts/s12_run.py --db data/eprime.sqlite "
          "--prompts data/eprime_prompts.jsonl --cohort eval_eprime --blind")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
