from __future__ import annotations

import collections
import concurrent.futures
import json
import queue
import re
import subprocess
import threading
import time
from typing import Any


IMPORTS = """import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat
"""


class LeanReplWorker:
    """One long-lived Lean REPL process inside WSL."""

    def __init__(self, distro: str, workspace: str, timeout: float) -> None:
        self.distro = distro
        self.workspace = workspace
        self.timeout = timeout
        self.process: subprocess.Popen[str] | None = None
        self.responses: queue.Queue[str | None] = queue.Queue()
        self.stderr: collections.deque[str] = collections.deque(maxlen=200)
        self._lock = threading.Lock()
        self._start()

    def _start(self) -> None:
        command = (
            f"cd '{self.workspace}' && "
            "exec lake exe repl"
        )
        creationflags = getattr(subprocess, "CREATE_NO_WINDOW", 0)
        self.process = subprocess.Popen(
            ["wsl", "-d", self.distro, "--", "bash", "-lc", command],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            encoding="utf-8",
            errors="replace",
            bufsize=1,
            creationflags=creationflags,
        )
        self.responses = queue.Queue()
        self.stderr = collections.deque(maxlen=200)
        threading.Thread(target=self._read_stdout, daemon=True).start()
        threading.Thread(target=self._read_stderr, daemon=True).start()
        response = self._request({"cmd": IMPORTS}, timeout=max(120.0, self.timeout))
        errors = [m for m in response.get("messages", []) if m.get("severity") == "error"]
        if errors:
            self.close()
            raise RuntimeError(f"Lean REPL import failed: {errors}")
        self.env = int(response["env"])

    def _read_stdout(self) -> None:
        assert self.process is not None and self.process.stdout is not None
        block: list[str] = []
        for raw in self.process.stdout:
            line = raw.rstrip("\r\n")
            if line:
                block.append(line)
            elif block:
                self.responses.put("\n".join(block))
                block = []
        if block:
            self.responses.put("\n".join(block))
        self.responses.put(None)

    def _read_stderr(self) -> None:
        assert self.process is not None and self.process.stderr is not None
        for raw in self.process.stderr:
            self.stderr.append(raw.rstrip())

    def _request(self, payload: dict[str, Any], timeout: float) -> dict[str, Any]:
        assert self.process is not None and self.process.stdin is not None
        self.process.stdin.write(json.dumps(payload, ensure_ascii=False) + "\n\n")
        self.process.stdin.flush()
        block = self.responses.get(timeout=timeout)
        if block is None:
            raise RuntimeError("Lean REPL exited: " + "\n".join(self.stderr))
        return json.loads(block)

    def verify(self, code: str) -> dict[str, Any]:
        started = time.perf_counter()
        command = re.sub(r"(?m)^\s*import\s+[^\n]+\n?", "", code).lstrip()
        try:
            with self._lock:
                response = self._request({"cmd": command, "env": self.env}, timeout=self.timeout)
            messages = response.get("messages", [])
            errors = [m for m in messages if m.get("severity") == "error"]
            warnings = [m for m in messages if m.get("severity") == "warning"]
            sorries = response.get("sorries", [])
            verified = not errors and not sorries and not any(
                "declaration uses 'sorry'" in str(m.get("data", "")) for m in warnings
            )
            return {
                "verified": verified,
                "lean_returncode": 0 if verified else 1,
                "lean_stdout": json.dumps(response, ensure_ascii=False)[-8000:],
                "lean_stderr": "",
                "lean_latency_seconds": time.perf_counter() - started,
                "lean_backend": "wsl_repl",
            }
        except queue.Empty:
            self.close()
            self._start()
            return {
                "verified": False,
                "lean_returncode": 124,
                "lean_stdout": "",
                "lean_stderr": "Lean REPL proof timeout",
                "lean_latency_seconds": time.perf_counter() - started,
                "lean_backend": "wsl_repl",
            }
        except Exception as exc:
            diagnostic = "\n".join(self.stderr)
            self.close()
            self._start()
            return {
                "verified": False,
                "lean_returncode": 125,
                "lean_stdout": "",
                "lean_stderr": f"Lean REPL error: {exc}\n{diagnostic}"[-8000:],
                "lean_latency_seconds": time.perf_counter() - started,
                "lean_backend": "wsl_repl",
            }

    def close(self) -> None:
        process = self.process
        self.process = None
        if process is None:
            return
        try:
            process.terminate()
            process.wait(timeout=5)
        except Exception:
            process.kill()


class LeanReplPool:
    def __init__(self, workers: int, distro: str, workspace: str, timeout: float) -> None:
        self.workers = [LeanReplWorker(distro, workspace, timeout) for _ in range(workers)]

    def verify_many(self, codes: list[str]) -> list[dict[str, Any]]:
        if not codes:
            return []
        available: queue.Queue[LeanReplWorker] = queue.Queue()
        for worker in self.workers:
            available.put(worker)

        def run(code: str) -> dict[str, Any]:
            worker = available.get()
            try:
                return worker.verify(code)
            finally:
                available.put(worker)

        with concurrent.futures.ThreadPoolExecutor(max_workers=len(self.workers)) as executor:
            return list(executor.map(run, codes))

    def close(self) -> None:
        for worker in self.workers:
            worker.close()
