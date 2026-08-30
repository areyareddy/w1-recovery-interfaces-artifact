"""Step s31 -- stage the fixed-budget retry-allocation experiment. CPU only.

    python scripts\\s31_build_allocation.py

THE QUESTION. Every arm in the main study spends its whole completion budget on one long
draw. W2 measured that 51.6% of all serving time goes to branches that hit the 12,288-token
cap and never reach Lean. This experiment asks whether that compute can be reallocated:
at the SAME per-root completion-token budget, does splitting the budget into several
shorter draws verify more theorems than one long draw?

    Long     1 x 12,288   -- already generated; this is arm A of the frozen study
    Split-2  2 x  6,144   -- staged here
    Split-3  3 x  4,096   -- staged here

WHY THE CAPS. From the frozen ledger, verified completions are short: median 3,263 decode
tokens, p90 7,068. A 6,144 cap retains 82% of all completions that ever verified and buys
two draws; 4,096 retains 61% and buys three. Below that the retained fraction falls faster
than the draw count rises. The caps were chosen from that distribution BEFORE any
allocation branch was generated, and the distribution is a property of the already-published
data, not of this experiment's outcomes.

SEEDS ARE NESTED, NOT INDEPENDENT. Draw j of a root uses base_seed + (j - 1), where
base_seed is that root's frozen arm-A seed. So draw 1 of Split-2 and draw 1 of Split-3
share a seed with each other AND with the existing Long baseline. If the server is
prefix-deterministic under a fixed seed -- same prompt, same sampler, only n_predict
differing -- those three draws are prefixes of one trajectory, and the policies are
compared on a shared first draw rather than on independent luck. We do NOT rely on that
holding: nothing in the analysis assumes it, and every draw is generated for real. It is
stated because if it does hold the comparison is tighter, and because assuming it silently
would be the kind of unchecked premise this project keeps catching.

PREFILL IS NOT A HANDICAP, AND HERE IS THE NUMBER. A reviewer will ask whether the split
policies are penalised by paying prefill once per draw. Arm-A prompts prefill at 194 tokens,
so three draws cost 582 prefill tokens against a 12,288-token decode budget -- about 0.06
seconds at the measured 8,762 tok/s. Stated in advance so it is not an after-the-fact
rebuttal.

EVAL IS STAGED BEFORE DEV AND BOTH ARE STAGED NOW. Generation order does not threaten
validity; inspection order does. spec/ALLOCATION_SPEC.md is written and hashed before any
branch runs, and it fixes the endpoints, the simulated stop-after-success rule, the router
rule family, how dev thresholds are read off, and what happens to a cohort that does not
finish. Eval is generated first only so that a truncated window costs the router analysis
rather than the primary endpoint.
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
RUNS_DB = ROOT / "data/runs.sqlite"
BUDGET = 12288          # completion-token budget per root, identical for every policy

POLICIES = {
    "split2": {"draws": 2, "cap": 6144},
    "split3": {"draws": 3, "cap": 4096},
}
# split -> (cohort suffix, source cohort in runs.sqlite for the base seed)
SPLITS = {"held_out": ("eval", "primary_eval"), "dev": ("dev", "full_pool_dev")}


def main() -> int:
    receipts.force_utf8()

    print("[1/4] reading arm-A payloads and frozen base seeds")
    arm_a = {}
    for line in PROMPTS.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        r = json.loads(line)
        if r["arm"] == "A":
            arm_a[(r["split"], r["root_id"])] = r
    con = sqlite3.connect(f"file:{RUNS_DB}?mode=ro", uri=True)
    base_seed = {}
    for split, (_, src_cohort) in SPLITS.items():
        for rid, seed in con.execute(
                "SELECT root_id, seed FROM branches WHERE cohort=? AND arm='A'",
                (src_cohort,)):
            base_seed[(split, rid)] = seed
    con.close()
    n_eval = sum(1 for k in arm_a if k[0] == "held_out")
    n_dev = sum(1 for k in arm_a if k[0] == "dev")
    print(f"      arm-A payloads: {n_eval} held-out, {n_dev} dev")
    missing = [k for k in arm_a if k not in base_seed]
    assert not missing, f"no frozen base seed for {missing[:3]}"

    prefill_tok = arm_a[("held_out", sorted(r for s, r in arm_a if s == "held_out")[0])]
    print(f"      base seeds present for every root")

    summary = []
    for pol, cfg in POLICIES.items():
        draws, cap = cfg["draws"], cfg["cap"]
        assert draws * cap == BUDGET, f"{pol}: {draws}x{cap} != {BUDGET} budget"
        db = ROOT / f"data/alloc_{pol}.sqlite"
        pj = ROOT / f"data/alloc_{pol}_prompts.jsonl"

        print(f"\n[2/4] {pol}: {draws} draws x {cap} tokens = {BUDGET} budget")
        records = []
        for split, (suffix, _) in SPLITS.items():
            cohort = f"alloc_{pol}_{suffix}"
            for (sp, rid), src in sorted(arm_a.items()):
                if sp != split:
                    continue
                for j in range(1, draws + 1):
                    rec = dict(src)
                    rec["branch_key"] = f"{rid}|{pol}|d{j}"
                    rec["cohort"] = cohort
                    rec["arm"] = pol
                    rec["policy"] = pol
                    rec["draw_index"] = j
                    rec["max_tokens"] = cap
                    rec["budget_tokens"] = BUDGET
                    rec["seed"] = base_seed[(split, rid)] + (j - 1)
                    rec["seed_block"] = 1
                    records.append(rec)
        pj.write_text(
            "\n".join(json.dumps(r, ensure_ascii=False, sort_keys=True) for r in records)
            + "\n", encoding="utf-8")

        if db.exists():
            chk = sqlite3.connect(f"file:{db}?mode=ro", uri=True)
            done = chk.execute(
                "SELECT count(*) FROM branches WHERE status != 'pending'").fetchone()[0]
            chk.close()
            assert done == 0, (
                f"{db.name} holds {done} non-pending branches; refusing to rebuild")
            db.unlink()
            for sfx in ("-wal", "-shm"):
                side = db.with_name(db.name + sfx)
                if side.exists():
                    side.unlink()
        con = sqlite3.connect(db)
        con.executescript(s08_init_db.SCHEMA)
        con.close()
        migrate.migrate(db, verbose=False)
        con = sqlite3.connect(db)
        for r in records:
            con.execute(
                "INSERT INTO branches (branch_key, root_id, split, arm, cohort, "
                "seed_block, seed, payload_sha256, conversation_turns, "
                "fine_failure_class, coarse_failure_group, policy, draw_index, "
                "max_tokens, budget_tokens) VALUES (?,?,?,?,?,1,?,?,?,?,?,?,?,?,?)",
                (r["branch_key"], r["root_id"], r["split"], pol, r["cohort"], r["seed"],
                 r["payload_sha256"], r["conversation_turns"], r["fine_failure_class"],
                 r["coarse_failure_group"], pol, r["draw_index"], r["max_tokens"],
                 r["budget_tokens"]))
        con.commit()
        by_cohort = dict(con.execute(
            "SELECT cohort, count(*) FROM branches GROUP BY cohort"))
        con.close()
        for c, n in sorted(by_cohort.items()):
            print(f"      {c:22} {n:4d} branches")
            summary.append((c, n, cap))
        print(f"      {db.relative_to(ROOT).as_posix()}")
        print(f"      {pj.relative_to(ROOT).as_posix()}")

    print("\n[3/4] identity of the staged design")
    digest = receipts.sha_text("\n".join(
        f"{c}:{n}:{cap}" for c, n, cap in sorted(summary)))
    print(f"      allocation design sha256 : {digest}")
    print("      (cohort:branches:cap over every staged cohort; record in the spec)")
    total = sum(n for _, n, _ in summary)
    print(f"      total new calls: {total}")

    print("\n[4/4] run order -- eval before dev, so a truncated window keeps the primary")
    for pol in POLICIES:
        for suffix in ("eval", "dev"):
            print(f"    python scripts\\s12_run.py --db data/alloc_{pol}.sqlite "
                  f"--prompts data/alloc_{pol}_prompts.jsonl "
                  f"--cohort alloc_{pol}_{suffix} --max-tokens {POLICIES[pol]['cap']}")
    print("\n  Do NOT open an eval cohort before the dev-derived thresholds are frozen.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
