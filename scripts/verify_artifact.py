"""Read-only integrity and completeness gate for the W1 artifact.

This gate checks the shipped databases, the 978-completion paper denominator,
the frozen-spec digest, required files, the file manifest, and a small
set of private path and identity strings.  CoLM is deliberately *not* a banned
term: the paper cites its COLM 2026 predecessor, Proof Yahtzee.
"""

from __future__ import annotations

import csv
import hashlib
import sqlite3
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
DATA = ROOT / "data"

DATABASES = {
    "runs.sqlite": {"total": 536},
    "cprime.sqlite": {"total": 40},
    "cprime_b2.sqlite": {"total": 40},
    "restart.sqlite": {"total": 120},
    "eprime.sqlite": {"total": 21},
    "armf.sqlite": {"total": 21},
    "alloc_split2.sqlite": {
        "total": 166,
        "cohorts": {"alloc_split2_eval": 80, "alloc_split2_dev": 86},
    },
    "alloc_split3.sqlite": {
        "total": 249,
        "cohorts": {"alloc_split3_eval": 120, "alloc_split3_dev": 129},
    },
}

PAPER_COMPONENTS = {
    "core": 536,
    "cprime_block1": 40,
    "cprime_block2": 40,
    "restart": 120,
    "eprime": 21,
    "arm_f": 21,
    "allocation_eval_split2": 80,
    "allocation_eval_split3": 120,
}

REQUIRED = [
    "README.md",
    "REPRODUCE.md",
    "ARTIFACT_MANIFEST.md",
    "ENVIRONMENT.md",
    "spec/frozen_spec.yaml",
    "spec/frozen_spec.sha256",
    "spec/ALLOCATION_SPEC.md",
    "data/roots.jsonl",
    "data/prompts.jsonl",
    "data/cprime_prompts.jsonl",
    "data/cprime_b2_prompts.jsonl",
    "data/restart_prompts.jsonl",
    "data/eprime_prompts.jsonl",
    "data/armf_prompts.jsonl",
    "data/alloc_split2_prompts.jsonl",
    "data/alloc_split3_prompts.jsonl",
    "data/predecessor_epp_confirmatory_202_attempts.jsonl",
    "audit/statistical_tests.json",
    "audit/coprimary_interaction.json",
    "audit/cprime_analysis.json",
    "audit/cprime_b2_analysis.json",
    "audit/restart_analysis.json",
    "audit/eprime_analysis.json",
    "audit/armf_analysis.json",
    "audit/allocation_analysis.json",
    "audit/mediation_and_ceiling.json",
    "scripts/s11_freeze_spec.py",
    "scripts/s12_run.py",
    "scripts/s13_seed_block2.py",
    "scripts/s14_anchoring_analysis.py",
    "scripts/s17_statistical_tests.py",
    "scripts/s19_coprimary_interaction.py",
    "scripts/s21_build_cprime.py",
    "scripts/s23_cprime_analysis.py",
    "scripts/s30_build_cprime_block2.py",
    "scripts/s31_build_allocation.py",
    "scripts/s34_agent_loop_replay.py",
    "scripts/s35_allocation_analysis.py",
    "scripts/s32_build_restart.py",
    "scripts/s37_restart_verify.py",
    "scripts/s38_restart_analysis.py",
    "scripts/s39_restart_anchoring.py",
    "scripts/s48_draw_diversity.py",
    "scripts/s49_build_eprime.py",
    "scripts/s50_eprime_analysis.py",
    "scripts/s51_build_armf.py",
    "scripts/s52_armf_analysis.py",
    "scripts/s58_mediation_and_ceiling.py",
    "scripts/build_assets.py",
    "prior_work/Prior_Work_Title_Withheld_for_Double-Blind_Review.pdf",
]

TEXT_SUFFIXES = {
    ".csv", ".json", ".jsonl", ".md", ".ps1", ".py", ".tex",
    ".txt", ".yaml", ".yml",
}
BANNED = (
    b"gpu" + b"mo",
    b"kar" + b"cube",
    b"/home/" + b"kar/",
    b"c:" + b"\\users\\",
)


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def check_databases(problems: list[str]) -> None:
    for name, expected in DATABASES.items():
        path = DATA / name
        if not path.exists():
            problems.append(f"missing database: data/{name}")
            continue
        con = sqlite3.connect(
            f"file:{path.as_posix()}?mode=ro&immutable=1", uri=True
        )
        try:
            qc = con.execute("PRAGMA quick_check").fetchone()[0]
            total = con.execute("SELECT count(*) FROM branches").fetchone()[0]
            done = con.execute(
                "SELECT count(*) FROM branches WHERE status='done'"
            ).fetchone()[0]
            nulls = con.execute(
                "SELECT count(*) FROM branches WHERE status='done' AND "
                "(completion IS NULL OR completion_sha256 IS NULL)"
            ).fetchone()[0]
            cohorts = dict(con.execute(
                "SELECT cohort, count(*) FROM branches GROUP BY cohort"
            ))
            if qc != "ok":
                problems.append(f"data/{name}: quick_check={qc!r}")
            if total != expected["total"]:
                problems.append(
                    f"data/{name}: {total} branches, expected {expected['total']}"
                )
            if done != total:
                problems.append(f"data/{name}: {total - done} branches are not done")
            if nulls:
                problems.append(f"data/{name}: {nulls} done rows have null payloads")
            for cohort, count in expected.get("cohorts", {}).items():
                if cohorts.get(cohort) != count:
                    problems.append(
                        f"data/{name}: cohort {cohort} has {cohorts.get(cohort)}, "
                        f"expected {count}"
                    )
            print(
                f"  {name:22} quick_check={qc:2} branches={total:3} "
                f"sha256={sha256(path)[:16]}"
            )
        finally:
            con.close()


def check_manifest(problems: list[str]) -> None:
    path = ROOT / "FILE_MANIFEST_SHA256.csv"
    if not path.exists():
        problems.append("missing FILE_MANIFEST_SHA256.csv")
        return
    with path.open(encoding="utf-8", newline="") as stream:
        rows = list(csv.DictReader(stream))
    for row in rows:
        if row["path"].endswith((".sqlite-shm", ".sqlite-wal")):
            problems.append(f"SQLite sidecar listed in manifest: {row['path']}")
            continue
        target = ROOT / row["path"]
        if not target.is_file():
            problems.append(f"manifest target missing: {row['path']}")
            continue
        if target.stat().st_size != int(row["bytes"]):
            problems.append(f"manifest size mismatch: {row['path']}")
        if sha256(target) != row["sha256"]:
            problems.append(f"manifest digest mismatch: {row['path']}")


def check_identity(problems: list[str]) -> None:
    for path in ROOT.rglob("*"):
        if (
            not path.is_file()
            or any(part in {".git", ".venv", "__pycache__", "tmp"}
                   for part in path.parts)
        ):
            continue
        if path.suffix.lower() not in TEXT_SUFFIXES:
            continue
        blob = path.read_bytes().lower()
        for term in BANNED:
            if term in blob:
                problems.append(
                    f"identity string {term.decode(errors='replace')!r} in "
                    f"{path.relative_to(ROOT).as_posix()}"
                )
def main() -> int:
    problems: list[str] = []
    print("Database integrity")
    check_databases(problems)

    paper_total = sum(PAPER_COMPONENTS.values())
    print(f"\nPaper denominator: {paper_total} completions")
    if paper_total != 978:
        problems.append(f"paper denominator is {paper_total}, expected 978")

    for rel in REQUIRED:
        if not (ROOT / rel).exists():
            problems.append(f"missing required artifact: {rel}")

    spec = ROOT / "spec/frozen_spec.yaml"
    spec_record = (ROOT / "spec/frozen_spec.sha256").read_text(
        encoding="utf-8"
    ).split()[0]
    spec_actual = sha256(spec)
    print(f"Frozen spec: {spec_actual}")
    if spec_record != spec_actual:
        problems.append(
            f"frozen spec digest mismatch: recorded {spec_record}, actual {spec_actual}"
        )

    check_identity(problems)
    check_manifest(problems)

    if problems:
        print("\nFAIL")
        for problem in problems:
            print(f"  - {problem}")
        return 1
    print("\nPASS -- complete, internally consistent, and free of the checked private path and identity strings.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
