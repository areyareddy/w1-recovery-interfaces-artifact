"""Shared pilot fixture: the 13 excluded stage-one failures, built into their own store.

Root hygiene (README): the 83 analysis roots are never touched by pilot or smoke work.
Pilot work runs on the 13 baseline failures from transfer42_stage1, which sit permanently
outside the 83 -- verified here, not assumed.

Only arms A, C and E are built. B and D need the frozen R2 guidance, and R2 guidance
exists only for the 83 roots that went through the CoLM cascade. Inventing guidance for a
pilot root to make B and D constructible would create a fixture that does not correspond
to anything, so the pilot exercises the plumbing that exists: a bare prompt (A), a prompt
carrying the prior attempt through the neutral wrapper (C), and the native multi-turn
correction format (E).

Pilot seeds live at 9_000_000 + index, far from the run's 2_000_000 block and from
CoLM's entire seed history, so a pilot row can never be confused with a real branch.
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

COLM = ROOT.parent / "CoLM_Jul2026_MoSpe_Navi"
STAGE1 = COLM / "runs/transfer42_stage1/evaluation/attempts.jsonl"
DATASET = COLM / "data/minif2f_test_inspected42.jsonl"

PILOT_PROMPTS = ROOT / "data/pilot_prompts.jsonl"
PILOT_DB = ROOT / "data/pilot.sqlite"
PILOT_SEED_BASE = 9_000_000
PREV_ROUND = 1


def _rj(path: Path) -> list[dict]:
    with Path(path).open(encoding="utf-8") as fh:
        return [json.loads(line) for line in fh if line.strip()]


def build_prompts() -> list[dict]:
    """Idempotent. Rebuilds data/pilot_prompts.jsonl from the CoLM tree (read-only)."""
    problems = {r["name"]: r for r in _rj(DATASET)}
    attempts = _rj(STAGE1)
    fails = sorted((r for r in attempts
                    if r.get("arm") == "baseline" and not r.get("verified")),
                   key=lambda r: r["problem_id"])
    assert len(fails) == 13, f"expected 13 pilot roots, got {len(fails)}"

    analysis_roots = {r["root_id"] for r in _rj(ROOT / "data/roots.jsonl")}
    overlap = {r["problem_id"] for r in fails} & analysis_roots
    assert not overlap, f"pilot roots must not touch the 83: {sorted(overlap)}"

    out: list[dict] = []
    for idx, rec in enumerate(fails):
        pid = rec["problem_id"]
        theorem = problems[pid]["formal_statement"]
        raw = rec["response"]["choices"][0]["message"]["content"]
        state = rec["outcome_state"]
        seed = PILOT_SEED_BASE + idx

        errors = goedel_native.repl_errors(rec.get("lean_stdout"))
        kind = goedel_native.feedback_kind(state, errors, rec.get("lean_stdout"))
        feedback = None
        if kind == "native_error":
            proof_rel = rec.get("proof_path")
            extracted = ""
            if proof_rel:
                p = COLM / str(proof_rel).replace("\\", "/")
                if p.exists():
                    extracted = p.read_text(encoding="utf-8", errors="replace")
            if not extracted:
                extracted = policy.extract_lean(raw, theorem)
            code = goedel_native.submitted_code(extracted)
            feedback, _, _ = goedel_native.build_feedback(
                state, code, errors, prev_round=PREV_ROUND)

        for arm in ("A", "C", "E"):
            if arm == "E":
                if feedback is None:
                    continue
                messages = prompts.arm_messages("E", theorem, raw_prior_attempt=raw,
                                                native_feedback=feedback)
            else:
                messages = prompts.arm_messages(
                    arm, theorem,
                    raw_prior_attempt=raw if arm == "C" else None)
            out.append({
                "branch_key": f"{pid}|{arm}",
                "root_id": pid,
                "split": "pilot",
                "arm": arm,
                "seed": seed,
                "messages": messages,
                "conversation_turns": len(messages),
                "payload_chars": sum(len(m["content"]) for m in messages),
                "payload_sha256": receipts.sha_text(
                    json.dumps(messages, ensure_ascii=False, sort_keys=True)),
                "fine_failure_class": policy.error_class(
                    state, rec.get("lean_stdout"), rec.get("lean_stderr")),
                "coarse_failure_group": "pilot",
                "theorem_text": theorem,
                "native_feedback_kind": kind,
            })

    with PILOT_PROMPTS.open("w", encoding="utf-8", newline="\n") as fh:
        for r in out:
            fh.write(json.dumps(r, ensure_ascii=False, sort_keys=True) + "\n")
    return out


def build_db(branches: list[dict], reset: bool = False) -> None:
    """Same schema as the real store, separate file. reset=True wipes prior pilot rows."""
    if reset and PILOT_DB.exists():
        for suffix in ("", "-wal", "-shm"):
            p = Path(str(PILOT_DB) + suffix)
            if p.exists():
                p.unlink()
    con = sqlite3.connect(PILOT_DB)
    con.execute("PRAGMA journal_mode=WAL")
    con.executescript(s08_init_db.SCHEMA)
    for b in branches:
        con.execute(
            "INSERT OR IGNORE INTO branches (branch_key, root_id, split, arm, cohort, "
            "seed_block, seed, payload_sha256, conversation_turns, fine_failure_class, "
            "coarse_failure_group) VALUES (?,?,?,?,'pilot',1,?,?,?,?,?)",
            (b["branch_key"], b["root_id"], b["split"], b["arm"], b["seed"],
             b["payload_sha256"], b["conversation_turns"], b["fine_failure_class"],
             b["coarse_failure_group"]))
    con.commit()
    con.close()


def ensure(reset: bool = False) -> list[dict]:
    branches = build_prompts()
    build_db(branches, reset=reset)
    return branches
