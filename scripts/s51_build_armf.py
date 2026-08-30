"""Step s51 -- stage arm F, native feedback WITHOUT the prior attempt. CPU only.

Governed by spec/ARM_F_SPEC.md, frozen before this script staged anything.

WHY. E' - A still varies the prior attempt AND the feedback together, so it cannot
isolate prior-attempt access when genuine feedback is present -- the configuration
deployed systems actually ship. Arm F removes the attempt and keeps the feedback:

    A  =                                                OFFICIAL(theorem)
    C  = WRAPPER(own attempt)                         + OFFICIAL(theorem)
    F  = FEEDBACK_ONLY_WRAPPER + CORRECTION_TURN(errs) + OFFICIAL(theorem)
    E' = WRAPPER'(own attempt) + CORRECTION_TURN(errs) + OFFICIAL(theorem)

so  E' - F  isolates prior-attempt access with feedback held present  <- the point
    F  - A  is feedback alone (see ARM_F_SPEC.md s2 on the referent asymmetry)
    F  - B  is a grounded compiler error against static failure-class guidance

GATE 4 IS THE DEFINING ONE: the root's own attempt -- and no 200-character fragment of
it -- may appear anywhere in its F prompt. No placeholder replaces it either; a
placeholder would reintroduce the artifact whose absence defines this arm.

WHAT THIS SCRIPT REFUSES TO DO. It does not touch prompts.ARMS, data/prompts.jsonl or
data/runs.sqlite. Arm E's three-turn path must remain byte-identical, so gate 3 rebuilds
that root's arm-E payload and asserts the correction turn F embeds is the same string --
which is what makes E'-F a single-factor contrast. The frozen A/C prompts are re-derived
and compared against data/prompts.jsonl (gate 0), so if adding F perturbed the shared
prompt surface by one byte, this aborts.
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

ARMF_DB = ROOT / "data/armf.sqlite"
ARMF_PROMPTS = ROOT / "data/armf_prompts.jsonl"
ELIGIBILITY_CSV = ROOT / "audit/armf_eligibility.csv"
COHORT = "eval_armf"
ARM = "F"
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

    print("\n[3/5] rebuilding feedback and building F prompts")
    seeds = {}
    con = sqlite3.connect(f"file:{ROOT / 'data/runs.sqlite'}?mode=ro", uri=True)
    for rid, seed in con.execute(
            "SELECT root_id, seed FROM branches WHERE cohort='primary_eval' AND arm='A'"):
        seeds[rid] = seed
    con.close()
    assert all(rid in seeds for rid in eligible), "missing a frozen arm-A seed"

    records, rows = [], []
    wrapper_sha = receipts.sha_text(prompts.FEEDBACK_ONLY_WRAPPER)

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
        assert kind == "native_error", f"{rid}: F built from non-native kind {kind!r}"
        # ---- gate 6: the rebuilt error block matches the frozen hash
        assert receipts.sha_text(error_block) == rec["native_feedback_sha256"],             f"{rid}: rebuilt <error> block differs from native_feedback_sha256"

        base = policy.official_prompt(theorem)
        prompt_f = prompts.armf_prompt(theorem, feedback)

        # ---- gate 2: F ends with OFFICIAL(theorem), byte-identical to arm A
        assert prompt_f.endswith(base), f"{rid}: F does not end with OFFICIAL(theorem)"
        assert by_arm[(rid, "A")]["messages"][0]["content"] == base,             f"{rid}: base prompt differs from frozen arm A"
        # ---- gate 3: the correction turn is byte-identical to arm E's third turn,
        #      hence to the one E' inlines -- so E'-F varies attempt-presence only
        e_ref = by_arm.get((rid, "E"))
        assert e_ref is not None, f"{rid}: eligible for F but has no frozen arm-E payload"
        assert len(e_ref["messages"]) == 3, f"{rid}: frozen arm E is not three turns"
        assert e_ref["messages"][2]["content"] == feedback, (
            f"{rid}: rebuilt correction turn differs from frozen arm E's third turn. "
            "F would then carry different feedback from E'.")
        assert feedback in prompt_f, f"{rid}: correction turn missing from F"
        # ---- gate 4: THE DEFINING PROPERTY -- the attempt appears nowhere in F
        assert raw not in prompt_f, \
            f"{rid}: the root's own attempt leaked into its F prompt"
        for probe in (raw[:200], raw[-200:]):
            if probe.strip():
                assert probe not in prompt_f, \
                    f"{rid}: a fragment of the attempt leaked into its F prompt"
        assert "<previous_attempt>" not in prompt_f, \
            f"{rid}: F carries a <previous_attempt> block"
        # ---- gate 5: exact reconstruction
        assert prompt_f == (prompts.FEEDBACK_ONLY_WRAPPER + feedback + "\n\n" + base), \
            f"{rid}: F is not exactly wrapper + correction + base"


        messages = [{"role": "user", "content": prompt_f}]
        records.append({
            "branch_key": f"{rid}|{ARM}",
            "root_id": rid, "split": "held_out", "arm": ARM, "cohort": COHORT,
            "seed": seeds[rid],
            "messages": messages,
            "conversation_turns": 1,
            "payload_chars": len(prompt_f),
            "payload_sha256": receipts.sha_text(
                json.dumps(messages, ensure_ascii=False, sort_keys=True)),
            "wrapper_sha256": wrapper_sha,
            "base_prompt_sha256": receipts.sha_text(base),
            "native_feedback_sha256": rec["native_feedback_sha256"],
            "fine_failure_class": rec["fine_failure_class"],
            "coarse_failure_group": rec["coarse_failure_group"],
        })
        rows.append({"root_id": rid, "seed": seeds[rid],
                     "prompt_chars": len(prompt_f),
                     "attempt_chars_excluded": len(raw),
                     "error_block_chars": len(error_block),
                     "fine_failure_class": rec["fine_failure_class"],
                     "coarse_failure_group": rec["coarse_failure_group"]})

    print(f"      {len(records)} prompts built, all gates passed")
    print(f"      gate 4 held on every root: no prior attempt, and no 200-char fragment "
          f"of one, appears in any F prompt")

    print("\n[4/5] writing prompts and eligibility record")
    with ARMF_PROMPTS.open("w", encoding="utf-8", newline="\n") as fh:
        for r in records:
            fh.write(json.dumps(r, ensure_ascii=False, sort_keys=True) + "\n")
    import csv
    with ELIGIBILITY_CSV.open("w", encoding="utf-8", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)

    print("\n[5/5] staging the job store (separate database)")
    if ARMF_DB.exists():
        chk = sqlite3.connect(f"file:{ARMF_DB}?mode=ro", uri=True)
        done = chk.execute(
            "SELECT count(*) FROM branches WHERE status != 'pending'").fetchone()[0]
        chk.close()
        assert done == 0, (
            f"{ARMF_DB.name} already holds {done} non-pending branches. Refusing to "
            "rebuild: that would discard generated data. Move it aside deliberately.")
        stamp = __import__("time").strftime("%Y%m%dT%H%M%S")
        moved = ROOT / "Backup" / f"armf.sqlite.{stamp}.prerebuild"
        ARMF_DB.replace(moved)
        for suffix in ("-wal", "-shm"):
            side = ARMF_DB.with_name(ARMF_DB.name + suffix)
            if side.exists():
                side.unlink()
        print(f"      previous empty store moved to Backup/{moved.name}")

    con = sqlite3.connect(ARMF_DB)
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

    print(f"      {ARMF_DB.relative_to(ROOT).as_posix()}: {n} branches pending")
    print(f"      {ARMF_PROMPTS.relative_to(ROOT).as_posix()}")
    print(f"      {ELIGIBILITY_CSV.relative_to(ROOT).as_posix()}")
    print("\nnext: python scripts/s12_run.py --db data/armf.sqlite "
          "--prompts data/armf_prompts.jsonl --cohort eval_armf --blind")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
