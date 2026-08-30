"""Step receipts -- the progress substrate for the whole harness.

Every pipeline step writes exactly one receipt to audit/receipts/<step>.json when it
finishes cleanly. A receipt records the sha256 of every file the step READ and every
file it WROTE, so `python scripts/status.py` can tell three different situations apart:

  pending  no receipt        -- step has not run
  stale    receipt, but an input's sha256 changed since it ran, or a declared output
           is missing/changed -- the step's conclusions no longer describe what is on
           disk and it must be re-run
  done     receipt, inputs unchanged, outputs intact

Staleness matters more than it looks. data/roots.jsonl is upstream of every later gate;
if it is ever regenerated, silently trusting a Gate 5 audit produced against the old
root set is exactly the kind of error that survives to the camera-ready.
"""

from __future__ import annotations

import hashlib
import json
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
RECEIPTS = ROOT / "audit" / "receipts"


def force_utf8() -> None:
    """Windows consoles default to cp1252 and a stray non-ASCII character will kill a
    script with UnicodeEncodeError. An overnight generation run dying at hour three on
    a print() is not a hypothetical. Call this first in every entry point."""
    for stream in (sys.stdout, sys.stderr):
        try:
            stream.reconfigure(encoding="utf-8", errors="replace")
        except (AttributeError, ValueError):
            pass


def sha_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def sha_file(path: Path) -> str | None:
    path = Path(path)
    if not path.exists():
        return None
    if path.is_dir():
        # directory digest = sha over (relpath, filesha) pairs, sorted
        parts = []
        for f in sorted(path.rglob("*")):
            if f.is_file():
                parts.append(f"{f.relative_to(path).as_posix()}:{sha_file(f)}")
        return sha_text("\n".join(parts))
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def _digest_map(paths) -> dict[str, str | None]:
    return {str(Path(p)): sha_file(ROOT / p if not Path(p).is_absolute() else p)
            for p in paths}


def write(step: str, title: str, inputs, outputs, stats=None, progress=None) -> Path:
    """Called by a step script on success. `inputs`/`outputs` are repo-relative paths."""
    RECEIPTS.mkdir(parents=True, exist_ok=True)
    payload = {
        "step": step,
        "title": title,
        "finished_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "inputs": _digest_map(inputs),
        "outputs": _digest_map(outputs),
        "stats": stats or {},
    }
    if progress is not None:
        payload["progress"] = progress
    path = RECEIPTS / f"{step}.json"
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return path


def load(step: str) -> dict | None:
    path = RECEIPTS / f"{step}.json"
    if not path.exists():
        return None
    return json.loads(path.read_text(encoding="utf-8"))


def verify(step: str) -> tuple[str, str]:
    """Returns (status, detail) in {pending, stale, done}."""
    rec = load(step)
    if rec is None:
        return "pending", ""
    for kind in ("inputs", "outputs"):
        for rel, recorded in rec[kind].items():
            now = sha_file(ROOT / rel)
            if now is None:
                return "stale", f"missing {kind[:-1]} {rel}"
            if now != recorded:
                return "stale", f"{kind[:-1]} changed: {rel}"
    return "done", rec["finished_utc"]
