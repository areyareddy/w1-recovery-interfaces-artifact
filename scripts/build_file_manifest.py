"""Generate the artifact's SHA-256 file manifest."""

from __future__ import annotations

import csv
import hashlib
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / "FILE_MANIFEST_SHA256.csv"


def digest(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def included(path: Path) -> bool:
    rel = path.relative_to(ROOT)
    return (
        path.is_file()
        and ".git" not in rel.parts
        and ".venv" not in rel.parts
        and "__pycache__" not in rel.parts
        and "tmp" not in rel.parts
        and path != OUT
        and not path.name.endswith((".sqlite-shm", ".sqlite-wal", ".pyc"))
    )


paths = sorted(
    (path for path in ROOT.rglob("*") if included(path)),
    key=lambda path: path.relative_to(ROOT).as_posix(),
)
with OUT.open("w", encoding="utf-8", newline="") as stream:
    writer = csv.DictWriter(
        stream,
        fieldnames=["sha256", "bytes", "path"],
        lineterminator="\n",
    )
    writer.writeheader()
    for path in paths:
        writer.writerow({
            "sha256": digest(path),
            "bytes": path.stat().st_size,
            "path": path.relative_to(ROOT).as_posix(),
        })
print(f"wrote {OUT.relative_to(ROOT).as_posix()} with {len(paths)} entries")
