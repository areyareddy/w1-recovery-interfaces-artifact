"""Step s30 -- stage arm C' seed block 2. CPU only; writes a new database.

    python scripts\\s30_build_cprime_block2.py

WHY BLOCK 2 IS BEING RUN. spec/CPRIME_SPEC.md section 9 fixes the stopping rule before
any C' branch existed: "One block of 40. A second seed block is run ONLY if the first is
directionally important but inconclusive." Block 1 returned C-C' = -0.125 with an exact
McNemar p = .125, a 95% interval of [-0.250, 0.000] touching zero, and a Holm-adjusted
p = .250 -- directionally important and inconclusive, exactly the described trigger. The
decision and its date are recorded in spec/CPRIME_SPEC.md before this script runs, as
section 9 also requires.

WHAT CHANGES AND WHAT DOES NOT. Only the seed. The donor assignment, the wrapper, the
base prompt, and therefore every payload are byte-identical to block 1: this script reuses
data/cprime_prompts.jsonl verbatim rather than re-deriving the pairing, so there is no way
for a rebuild to quietly produce a different donor map. The canonical donor-map digest is
re-asserted against the frozen value before anything is staged.

SEEDS. The corpus derives block 2 from block 1 by adding 1,000,000 -- primary_eval root
seeds are 2,000,000 + index and eval_block2 seeds are 3,000,000 + index. C' block 1 shares
each root's block-1 seed with arms A and C; C' block 2 therefore takes the same root's
eval_block2 seed, so A, C and C' remain seed-matched within root in both blocks. The seed
is read from runs.sqlite rather than recomputed, so an index-arithmetic slip cannot
silently desynchronise the arms.
"""

from __future__ import annotations

import csv
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

RUNS_DB = ROOT / "data/runs.sqlite"
SRC_PROMPTS = ROOT / "data/cprime_prompts.jsonl"
PAIRING_CSV = ROOT / "audit/cprime_pairing.csv"
OUT_DB = ROOT / "data/cprime_b2.sqlite"
OUT_PROMPTS = ROOT / "data/cprime_b2_prompts.jsonl"
COHORT = "eval_cprime_b2"
ARM = "Cp"

FROZEN_DONOR_MAP_SHA = "ea0ea22a3196e841c7cac9df702cd0fc26cbefab73e6e15dcfb89546ce167a4b"
FROZEN_PROMPTS_SHA = "5b009fe19829558f11a0e2ce6fec438edac96a2bf218c379ff7758ea7a421f8b"


def main() -> int:
    receipts.force_utf8()

    print("[1/5] re-asserting the frozen block-1 identity")
    donor = {r["root_id"]: r["donor_root_id"]
             for r in csv.DictReader(PAIRING_CSV.open(encoding="utf-8"))}
    canon = receipts.sha_text("\n".join(f"{r}->{donor[r]}" for r in sorted(donor)))
    prompts_sha = receipts.sha_file(SRC_PROMPTS)
    print(f"      canonical donor-map sha256 : {canon}")
    print(f"      prompts sha256             : {prompts_sha}")
    assert canon == FROZEN_DONOR_MAP_SHA, (
        "donor map does not match the frozen value; block 2 must reuse block 1's pairing")
    assert prompts_sha == FROZEN_PROMPTS_SHA, (
        "cprime_prompts.jsonl differs from the frozen value; refusing to build block 2")
    print("      both match -- block 2 reuses block 1's pairing and payloads exactly")

    print("\n[2/5] reading eval_block2 seeds from runs.sqlite")
    con = sqlite3.connect(f"file:{RUNS_DB}?mode=ro", uri=True)
    b2_seed = dict(con.execute(
        "SELECT root_id, seed FROM branches WHERE cohort='eval_block2' AND arm='A'"))
    b1_seed = dict(con.execute(
        "SELECT root_id, seed FROM branches WHERE cohort='primary_eval' AND arm='A'"))
    con.close()
    records = [json.loads(l) for l in SRC_PROMPTS.read_text(encoding="utf-8").splitlines() if l.strip()]
    assert len(records) == 40, f"expected 40 C' prompts, got {len(records)}"
    missing = [r["root_id"] for r in records if r["root_id"] not in b2_seed]
    assert not missing, f"no eval_block2 seed for {missing}"
    for r in records:
        rid = r["root_id"]
        assert b2_seed[rid] == b1_seed[rid] + 1_000_000, (
            f"{rid}: block-2 seed {b2_seed[rid]} is not block-1 {b1_seed[rid]} + 1e6; "
            "the corpus convention does not hold, so do not guess")
    print(f"      40 roots, all seeds are block-1 + 1,000,000 as the corpus defines")

    print("\n[3/5] writing block-2 prompts (payload identical, seed and keys changed)")
    out = []
    for r in records:
        rec = dict(r)
        rec["seed"] = b2_seed[rec["root_id"]]
        rec["seed_block"] = 2
        rec["cohort"] = COHORT
        rec["branch_key"] = f"{rec['root_id']}|{ARM}|b2"
        out.append(rec)
    # the payload digest must be unchanged: only seed/keys differ
    assert {r["payload_sha256"] for r in out} == {r["payload_sha256"] for r in records}
    OUT_PROMPTS.write_text(
        "\n".join(json.dumps(r, ensure_ascii=False, sort_keys=True) for r in out) + "\n",
        encoding="utf-8")
    print(f"      {OUT_PROMPTS.relative_to(ROOT).as_posix()}")

    print("\n[4/5] staging the job store")
    if OUT_DB.exists():
        chk = sqlite3.connect(f"file:{OUT_DB}?mode=ro", uri=True)
        done = chk.execute(
            "SELECT count(*) FROM branches WHERE status != 'pending'").fetchone()[0]
        chk.close()
        assert done == 0, (
            f"{OUT_DB.name} already holds {done} non-pending branches. Refusing to "
            "rebuild: that would discard generated data.")
        OUT_DB.unlink()
        for suffix in ("-wal", "-shm"):
            side = OUT_DB.with_name(OUT_DB.name + suffix)
            if side.exists():
                side.unlink()
    con = sqlite3.connect(OUT_DB)
    con.executescript(s08_init_db.SCHEMA)
    for r in out:
        con.execute(
            "INSERT INTO branches (branch_key, root_id, split, arm, cohort, seed_block, "
            "seed, payload_sha256, conversation_turns, fine_failure_class, "
            "coarse_failure_group) VALUES (?,?,?,?,?,2,?,?,?,?,?)",
            (r["branch_key"], r["root_id"], r["split"], ARM, COHORT, r["seed"],
             r["payload_sha256"], r["conversation_turns"], r["fine_failure_class"],
             r["coarse_failure_group"]))
    con.commit()
    n = con.execute("SELECT count(*) FROM branches").fetchone()[0]
    con.close()
    assert n == 40, f"expected 40 staged branches, got {n}"
    print(f"      {OUT_DB.relative_to(ROOT).as_posix()}: {n} branches pending")

    print("\n[5/5] phase-timing columns")
    migrate.migrate(OUT_DB)

    print("\n  To generate:")
    print(f"    python scripts\\s12_run.py --db data/{OUT_DB.name} "
          f"--prompts data/{OUT_PROMPTS.name} --cohort {COHORT} --block 2")
    print("\n  Analysis is spec/CPRIME_SPEC.md unchanged. Report block 1 and block 2")
    print("  separately; the two blocks share 40 theorems and are NOT 80 roots.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
