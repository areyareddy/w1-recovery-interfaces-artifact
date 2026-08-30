"""The resumable branch runner. Used by the kill/restart test, the pilot, and the run.

CRASH MODEL. One runner process at a time, because there is one GPU slot and one Lean
worker. That assumption is what lets reclaim() be simple: on startup, any row still
marked 'running' belongs to a process that died, so it goes back to 'pending'. With
concurrent runners this would steal live work, so start_run() refuses if another runner
holds a lease that is still warm.

COMMIT DISCIPLINE. Each branch is claimed in its own transaction and written in its own
transaction. A kill between the two loses at most the in-flight generation, and the
branch returns to 'pending' on the next start. Nothing is ever half-written, and nothing
is ever generated twice into the same row -- the claim is `UPDATE ... WHERE
status='pending'` and a claim that changes zero rows means somebody else took it.

OUTCOME STATES follow CoLM exactly, via the verbatim policy.generation_prefilter:

    truncated      finish_reason == 'length'; the model ran out of budget mid-proof and
                   Lean is never invoked -- costs a full decode, produces no verdict
    format_error   no usable Lean came back, or a sorry/admit placeholder appeared
    verified       Lean accepted it
    lean_failed    Lean rejected it

Only 'verified' and 'lean_failed' consume verifier wall time. That asymmetry is the
substance of W2's failure-state economics, so the runner records verifier_wall_seconds
as 0.0 for the skipped states rather than leaving it NULL -- 'we did not spend it' and
'we did not measure it' must not look the same in the analysis.
"""

from __future__ import annotations

import json
import os
import socket
import sqlite3
import time
from pathlib import Path
from typing import Any, Callable

import generate
import policy
from wsl_lean_repl import LeanReplPool

LEASE_WARM_SECONDS = 900

# If the server dies, every remaining branch fails in milliseconds. Without a breaker an
# 8-hour queue would burn through 500 branches marking them all failed in under a minute,
# and the damage would look like a completed run. Five in a row means something systemic.
MAX_CONSECUTIVE_FAILURES = 5

# A branch that failed transiently is retried on the next start. Three attempts, then it
# stays failed and needs a human -- retrying forever would hide a genuinely broken branch.
MAX_ATTEMPTS = 3


class Runner:
    def __init__(self, db_path: Path, prompts_path: Path, roots_path: Path,
                 lean_cfg: dict[str, Any], base_url: str = "http://127.0.0.1:8080",
                 max_tokens: int = generate.MAX_TOKENS,
                 spec_sha256: str | None = None,
                 require_seed: bool = True):
        self.db_path = Path(db_path)
        self.lean_cfg = lean_cfg
        self.max_tokens = max_tokens
        self.spec_sha256 = spec_sha256
        self.require_seed = require_seed
        self.worker = f"{socket.gethostname()}:{os.getpid()}"
        self.client = generate.Client(base_url)
        self._pool: LeanReplPool | None = None

        self.payloads = {r["branch_key"]: r for r in _read_jsonl(prompts_path)}
        self.theorem = {r["root_id"]: r["theorem_text"] for r in _read_jsonl(roots_path)}
        # a pilot payload file carries its own theorem text, because pilot roots are not
        # in data/roots.jsonl by design (root hygiene: the 83 stay untouched)
        for p in self.payloads.values():
            if "theorem_text" in p:
                self.theorem.setdefault(p["root_id"], p["theorem_text"])

    # ------------------------------------------------------------------ plumbing

    def _connect(self) -> sqlite3.Connection:
        con = sqlite3.connect(self.db_path, timeout=60, isolation_level=None)
        con.execute("PRAGMA journal_mode=WAL")
        con.execute("PRAGMA synchronous=FULL")
        con.execute("PRAGMA busy_timeout=60000")
        return con

    @property
    def pool(self) -> LeanReplPool:
        if self._pool is None:
            self._pool = LeanReplPool(
                workers=self.lean_cfg.get("workers", 1),
                distro=self.lean_cfg["wsl_distro"],
                workspace=self.lean_cfg["wsl_workspace"],
                timeout=self.lean_cfg.get("timeout_seconds", 180))
        return self._pool

    def close(self) -> None:
        if self._pool is not None:
            self._pool.close()
            self._pool = None

    def _event(self, con: sqlite3.Connection, kind: str,
               branch_key: str | None = None, detail: str = "") -> None:
        con.execute("INSERT INTO events (at, run_id, branch_key, kind, detail) "
                    "VALUES (?,?,?,?,?)",
                    (_utc(), self.worker, branch_key, kind, detail))

    # ------------------------------------------------------------------ lifecycle

    def reclaim(self, cohort: str) -> int:
        """Return orphaned 'running' rows to 'pending'. Refuses if another runner's
        lease is still warm -- a stale reclaim under a live runner would double-generate."""
        con = self._connect()
        try:
            warm = con.execute(
                "SELECT worker, claimed_at FROM branches WHERE status='running' "
                "AND cohort=? AND worker IS NOT NULL AND worker != ?",
                (cohort, self.worker)).fetchall()
            for worker, claimed_at in warm:
                if claimed_at and (time.time() - _epoch(claimed_at)) < LEASE_WARM_SECONDS:
                    raise RuntimeError(
                        f"another runner ({worker}) claimed a branch {int(time.time() - _epoch(claimed_at))}s "
                        f"ago, which is inside the {LEASE_WARM_SECONDS}s lease. Refusing to "
                        f"reclaim -- stop that runner first, or wait for the lease to go cold."
                    )
            n = con.execute(
                "UPDATE branches SET status='pending', worker=NULL, claimed_at=NULL "
                "WHERE status='running' AND cohort=?", (cohort,)).rowcount
            # a server blip can mark many branches 'failed' in seconds; a restart should
            # retry those rather than lose them permanently to one hiccup
            n += con.execute(
                "UPDATE branches SET status='pending', worker=NULL, claimed_at=NULL, "
                "error_message=NULL WHERE status='failed' AND cohort=? AND attempt<?",
                (cohort, MAX_ATTEMPTS)).rowcount
            if n:
                self._event(con, "reclaim", detail=f"{n} orphaned branch(es) in {cohort}")
            return n
        finally:
            con.close()

    def claim(self, con: sqlite3.Connection, cohort: str,
              seed_block: int) -> dict | None:
        """Atomically take the next pending branch. None when the cohort is exhausted."""
        con.execute("BEGIN IMMEDIATE")
        row = con.execute(
            "SELECT branch_key, root_id, arm, seed FROM branches "
            "WHERE cohort=? AND seed_block=? AND status='pending' "
            "ORDER BY branch_key LIMIT 1", (cohort, seed_block)).fetchone()
        if row is None:
            con.execute("COMMIT")
            return None
        key, root_id, arm, seed = row
        changed = con.execute(
            "UPDATE branches SET status='running', worker=?, claimed_at=?, "
            "attempt=attempt+1 WHERE branch_key=? AND status='pending'",
            (self.worker, _utc(), key)).rowcount
        con.execute("COMMIT")
        if changed != 1:
            return self.claim(con, cohort, seed_block)  # lost a race; take the next
        if self.require_seed and seed is None:
            raise RuntimeError(
                f"{key} has no seed. Seeds are assigned when the spec is frozen "
                f"(s11); running without one would make the block unreproducible.")
        return {"branch_key": key, "root_id": root_id, "arm": arm, "seed": seed}

    # ------------------------------------------------------------------ one branch

    def run_branch(self, job: dict) -> dict:
        key = job["branch_key"]
        # a second-seed-block row reuses block 1's payload byte for byte and differs only
        # in its seed, so its key carries a '#b2' suffix that is not part of the payload id
        payload = self.payloads[key.split("#", 1)[0]]
        seed = job["seed"] if job["seed"] is not None else 0

        result = self.client.chat(payload["messages"], seed=seed,
                                  max_tokens=self.max_tokens)

        # outcome_state, exactly as CoLM derives it
        code = policy.extract_lean(result.completion, self.theorem[job["root_id"]])
        response_shape = {"choices": [{"finish_reason": result.finish_reason,
                                       "message": {"content": result.completion}}]}
        prefilter = policy.generation_prefilter(response_shape, code)

        if prefilter is None:
            verdict = self._verify(code)
            state = "verified" if verdict["verified"] else "lean_failed"
            verifier_wall = verdict["lean_latency_seconds"]
        else:
            state = prefilter
            verdict = {"verified": False, "lean_returncode": -1, "lean_stdout": "",
                       "lean_stderr": f"Lean skipped: {prefilter}"}
            verifier_wall = 0.0   # not spent, as distinct from not measured

        return {
            "branch_key": key,
            "completion": result.completion,
            "completion_sha256": _sha(result.completion),
            "finish_reason": result.finish_reason,
            "model_calls": result.model_calls,
            "completion_tokens": result.completion_tokens,
            "total_tokens": result.total_tokens,
            "prefill_tokens": result.prefill_tokens,
            "decode_tokens": result.decode_tokens,
            "request_wall_seconds": result.request_wall_seconds,
            "verifier_wall_seconds": verifier_wall,
            "outcome_state": state,
            "verified": 1 if verdict["verified"] else 0,
            "lean_returncode": verdict["lean_returncode"],
            "lean_stdout": verdict["lean_stdout"],
            "lean_stderr": verdict["lean_stderr"],
            "error_class": policy.error_class(state, verdict["lean_stdout"],
                                              verdict["lean_stderr"]),
            "seed": seed,
            "decode_tok_per_s": result.decode_tokens_per_second,
            # phase timings: the client has parsed these all along (generate.py reads
            # llama.cpp's timings block) and record() used to drop them, which is why the
            # W2 analysis needed an eight-hour replay to recover them. Persisted now.
            "prefill_ms": result.prefill_ms,
            "decode_ms": result.decode_ms,
            "cached_tokens": result.cached_tokens,
            "cache_n": result.raw_timings.get("cache_n", 0),
            "raw_timings_json": json.dumps(result.raw_timings, sort_keys=True),
            "max_tokens": self.max_tokens,
        }

    def _verify(self, code: str, attempts: int = 3, backoff: float = 20.0) -> dict:
        """LeanReplWorker.verify() absorbs a crashed REPL, but its recovery path calls
        _start(), which re-issues the Mathlib import through _request -- and THAT can
        raise, escaping verify()'s own handler. One transient WSL hiccup then costs a
        branch. So the pool is torn down and rebuilt here, and the branch is retried.

        Retrying verification is free of scientific consequence: Lean is deterministic on
        a pinned Mathlib, so a second check of the same proof yields the same verdict."""
        last: Exception | None = None
        for i in range(attempts):
            try:
                return self.pool.verify_many([code])[0]
            except Exception as exc:  # noqa: BLE001
                last = exc
                self.close()          # drop the wedged pool; the next call rebuilds it
                if i == attempts - 1:
                    break
                wait = backoff * (i + 1)
                print(f"      [verify] {type(exc).__name__}: {exc} -- rebuilding the "
                      f"Lean REPL in {wait:.0f}s (try {i + 1}/{attempts})", flush=True)
                time.sleep(wait)
        raise RuntimeError(
            f"Lean verification failed after {attempts} attempts; last: "
            f"{type(last).__name__}: {last}") from last

    # columns added by scripts/s29_migrate_timings.py; absent in the frozen runs.sqlite
    _TIMING_COLS = ("prefill_ms", "decode_ms", "cached_tokens", "cache_n",
                    "raw_timings_json", "max_tokens")

    def _timing_cols(self, con: sqlite3.Connection) -> tuple[str, ...]:
        """Which timing columns this database actually has. Cached per connection target
        so the PRAGMA runs once, not once per branch."""
        if getattr(self, "_timing_cols_cache", None) is None:
            have = {r[1] for r in con.execute("PRAGMA table_info(branches)")}
            self._timing_cols_cache = tuple(c for c in self._TIMING_COLS if c in have)
        return self._timing_cols_cache

    def record(self, con: sqlite3.Connection, rec: dict) -> None:
        extra = self._timing_cols(con)
        con.execute("BEGIN IMMEDIATE")
        con.execute(
            "UPDATE branches SET status='done', finished_at=?, spec_sha256=?, "
            "completion=?, completion_sha256=?, finish_reason=?, "
            "model_calls=?, completion_tokens=?, total_tokens=?, prefill_tokens=?, "
            "decode_tokens=?, request_wall_seconds=?, verifier_wall_seconds=?, "
            "outcome_state=?, verified=?, lean_returncode=?, lean_stdout=?, "
            "lean_stderr=?, error_class=?"
            + "".join(f", {c}=?" for c in extra)
            + " WHERE branch_key=?",
            (_utc(), self.spec_sha256, rec["completion"], rec["completion_sha256"],
             rec["finish_reason"], rec["model_calls"], rec["completion_tokens"],
             rec["total_tokens"], rec["prefill_tokens"], rec["decode_tokens"],
             rec["request_wall_seconds"], rec["verifier_wall_seconds"],
             rec["outcome_state"], rec["verified"], rec["lean_returncode"],
             rec["lean_stdout"], rec["lean_stderr"], rec["error_class"])
            + tuple(rec.get(c) for c in extra)
            + (rec["branch_key"],))
        con.execute("COMMIT")

    def fail(self, con: sqlite3.Connection, key: str, message: str) -> None:
        con.execute("BEGIN IMMEDIATE")
        con.execute("UPDATE branches SET status='failed', finished_at=?, "
                    "error_message=? WHERE branch_key=?", (_utc(), message[:4000], key))
        self._event(con, "branch_failed", key, message[:500])
        con.execute("COMMIT")

    # ------------------------------------------------------------------ main loop

    def run(self, cohort: str, seed_block: int = 1, limit: int | None = None,
            on_branch: Callable[[dict, int, int], None] | None = None) -> dict:
        self.reclaim(cohort)
        con = self._connect()
        total = con.execute("SELECT count(*) FROM branches WHERE cohort=? AND seed_block=?",
                            (cohort, seed_block)).fetchone()[0]
        done_at_start = con.execute(
            "SELECT count(*) FROM branches WHERE cohort=? AND seed_block=? AND status='done'",
            (cohort, seed_block)).fetchone()[0]
        self._event(con, "run_start", detail=f"cohort={cohort} block={seed_block} "
                                             f"done={done_at_start}/{total}")

        completed = failed = consecutive = 0
        t0 = time.time()
        try:
            while limit is None or completed + failed < limit:
                job = self.claim(con, cohort, seed_block)
                if job is None:
                    break
                try:
                    rec = self.run_branch(job)
                    self.record(con, rec)
                    completed += 1
                    consecutive = 0
                    if on_branch:
                        done_now = done_at_start + completed
                        on_branch(rec, done_now, total)
                except KeyboardInterrupt:
                    self.fail(con, job["branch_key"], "interrupted")
                    raise
                except Exception as exc:  # noqa: BLE001
                    self.fail(con, job["branch_key"], f"{type(exc).__name__}: {exc}")
                    failed += 1
                    consecutive += 1
                    if consecutive >= MAX_CONSECUTIVE_FAILURES:
                        self._event(con, "circuit_break",
                                    detail=f"{consecutive} consecutive: {exc}")
                        raise RuntimeError(
                            f"{consecutive} consecutive branch failures, last: "
                            f"{type(exc).__name__}: {exc}. Stopping rather than marking "
                            f"the rest of the cohort failed. The branches are still "
                            f"pending and a restart will retry them."
                        ) from exc
            self._event(con, "run_end", detail=f"completed={completed} failed={failed}")
            remaining = con.execute(
                "SELECT count(*) FROM branches WHERE cohort=? AND seed_block=? "
                "AND status='pending'", (cohort, seed_block)).fetchone()[0]
        finally:
            con.close()
            self.close()

        return {"cohort": cohort, "seed_block": seed_block, "total": total,
                "done_at_start": done_at_start, "completed": completed,
                "failed": failed, "pending_after": remaining,
                "elapsed_seconds": round(time.time() - t0, 1)}


# ---------------------------------------------------------------------- helpers


def _utc() -> str:
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


def _epoch(stamp: str) -> float:
    return time.mktime(time.strptime(stamp, "%Y-%m-%dT%H:%M:%SZ")) - time.timezone


def _sha(text: str) -> str:
    import hashlib
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def _read_jsonl(path: Path) -> list[dict]:
    with Path(path).open(encoding="utf-8") as fh:
        return [json.loads(line) for line in fh if line.strip()]
