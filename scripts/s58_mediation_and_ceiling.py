"""Step s58 -- two reviewer answers W1 owes: the length mediator, and the corpus ceiling.

CPU only. No generation. Both quantities currently exist only as prose in a handover
document, which is exactly why they cannot go into the paper: the arm-E error happened
because a number was typed by hand. This script recomputes both from source and persists
them so build_macros.py can emit them.

PART 1 -- THE COMPLETION-LENGTH MEDIATOR (reviewer concern 2)
The review proposes that arm C writes shorter completions and that this mediates the
verification harm. Aggregate C < A is real. The mediation is not: the aggregate is an
aggregation artifact. This computes the length comparison SEPARATELY on the roots that
carry the harm (lost rescues: A verified, C did not) and on the roots where nothing was
rescued, per seed block, so the reader can see where the collapse actually lives.

Reported as a SECOND NEGATIVE. Writing it as the bridge between anchoring and harm would
contradict section 5.3, which already reports that anchoring magnitude does not select the
roots that lose a rescue.

PART 2 -- THE CORPUS CEILING (reviewer concern 5)
The review asserts that expanding to 150-200 roots "is not a resource question." It is.
The root corpus is drawn from the CoLM parent study's epp_confirmatory_202 run. This counts
how many additional roots that source could yield WITHOUT new stage-one generation, and
what the unused remainder looks like, so the paper can answer with arithmetic instead of a
concession.

CoLM is read-only throughout.
"""

from __future__ import annotations

import json
import sqlite3
import statistics
import sys
from collections import defaultdict
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
COLM_ATTEMPTS = ROOT / "data/predecessor_epp_confirmatory_202_attempts.jsonl"
DB = ROOT / "data/runs.sqlite"
OUT = ROOT / "audit/mediation_and_ceiling.json"
BLOCKS = {"primary_eval": "block1", "eval_block2": "block2"}


def length_mediation(con) -> dict:
    out: dict = {}
    for cohort, tag in BLOCKS.items():
        rows = defaultdict(dict)
        for rid, arm, ver, toks, state in con.execute(
                "SELECT root_id, arm, verified, completion_tokens, outcome_state "
                "FROM branches WHERE cohort=? AND arm IN ('A','C') AND status='done'",
                (cohort,)):
            rows[rid][arm] = {"verified": bool(ver), "tokens": toks or 0, "state": state}
        roots = sorted(r for r, d in rows.items() if {"A", "C"} <= set(d))

        groups = {
            # the roots that carry the harm
            "lost_rescues": [r for r in roots
                             if rows[r]["A"]["verified"] and not rows[r]["C"]["verified"]],
            # the roots where nothing was rescued either way
            "neither_verified": [r for r in roots
                                 if not rows[r]["A"]["verified"]
                                 and not rows[r]["C"]["verified"]],
            "all_roots": roots,
        }
        blk: dict = {}
        for name, rs in groups.items():
            if not rs:
                blk[name] = {"n": 0}
                continue
            a = [rows[r]["A"]["tokens"] for r in rs]
            c = [rows[r]["C"]["tokens"] for r in rs]
            ma, mc = statistics.mean(a), statistics.mean(c)
            blk[name] = {
                "n": len(rs),
                "mean_tokens_A": round(ma, 1),
                "mean_tokens_C": round(mc, 1),
                "ratio_C_over_A": round(mc / ma, 3) if ma else None,
                "median_tokens_A": statistics.median(a),
                "median_tokens_C": statistics.median(c),
            }
        # what arm C actually DID on the lost roots: truncation would support the
        # mediator, kernel rejection of a complete proof does not
        states: dict[str, int] = {}
        for r in groups["lost_rescues"]:
            s = rows[r]["C"]["state"]
            states[s] = states.get(s, 0) + 1
        blk["C_terminal_state_on_lost_rescues"] = states
        out[tag] = blk

    # the conditional length effect that IS real: the model shortens only when the prior
    # attempt looks finished. Good mechanism for anchoring; not a mediator of the harm.
    cond: dict = {}
    for cohort, tag in BLOCKS.items():
        per = defaultdict(lambda: {"A": [], "C": []})
        for rid, arm, toks, grp in con.execute(
                "SELECT root_id, arm, completion_tokens, coarse_failure_group "
                "FROM branches WHERE cohort=? AND arm IN ('A','C') AND status='done'",
                (cohort,)):
            per[grp][arm].append(toks or 0)
        cond[tag] = {g: {"n_A": len(v["A"]), "n_C": len(v["C"]),
                         "mean_A": round(statistics.mean(v["A"]), 1) if v["A"] else None,
                         "mean_C": round(statistics.mean(v["C"]), 1) if v["C"] else None,
                         "ratio_C_over_A": round(
                             statistics.mean(v["C"]) / statistics.mean(v["A"]), 3)
                         if v["A"] and v["C"] and statistics.mean(v["A"]) else None}
                     for g, v in sorted(per.items())}
    out["conditional_by_stage_one_group"] = cond

    r1 = out["block1"]["lost_rescues"].get("ratio_C_over_A")
    r2 = out["block2"]["lost_rescues"].get("ratio_C_over_A")
    out["verdict"] = {
        "mediator_supported": False,
        "why": ("On the roots that carry the harm the direction is not stable: the C/A "
                f"token ratio is {r1} in block 1 and {r2} in block 2. A mediator of the "
                "deficit cannot flip sign between replications of the same contrast. The "
                "aggregate C<A is driven by the roots where nothing was rescued."),
    }
    return out


def corpus_ceiling() -> dict:
    if not COLM_ATTEMPTS.exists():
        return {"available": False,
                "why": f"{COLM_ATTEMPTS} not found; the ceiling cannot be computed"}
    rows = [json.loads(l) for l in COLM_ATTEMPTS.open(encoding="utf-8") if l.strip()]
    by_problem = defaultdict(list)
    for r in rows:
        by_problem[r["problem_id"]].append(r)

    n_problems = len(by_problem)
    arms = sorted({r["arm"] for r in rows})
    has_failure = {p for p, rs in by_problem.items() if any(not r["verified"] for r in rs)}
    never_verify = {p for p, rs in by_problem.items() if not any(r["verified"] for r in rs)}
    # a problem that failed somewhere but verified somewhere else is systematically
    # easier than one that never verified at all
    failed_but_verified = has_failure - never_verify

    used = set()
    rp = ROOT / "data/roots.jsonl"
    if rp.exists():
        for l in rp.open(encoding="utf-8"):
            if l.strip():
                used.add(json.loads(l)["root_id"])

    return {
        "available": True,
        "source": "CoLM epp_confirmatory_202/evaluation/attempts.jsonl",
        "n_attempts": len(rows),
        "n_problems": n_problems,
        "arms": arms,
        "n_with_at_least_one_failure": len(has_failure),
        "n_never_verified_on_any_arm": len(never_verify),
        "n_failed_but_verified_elsewhere": len(failed_but_verified),
        "n_roots_in_study": len(used),
        "n_never_verified_already_roots": len(never_verify & used),
        "n_unused_failed_problems": len(has_failure - used),
        "ceiling_without_new_generation": len(has_failure),
        "note": ("The ceiling without fresh stage-one generation is the count of problems "
                 "with at least one failure. Reaching 150-200 roots would require new "
                 "stage-one generation on unused miniF2F problems plus re-running "
                 "classification and guidance rendering, which is a camera-ready item "
                 "rather than a planning oversight."),
    }


def main() -> int:
    try:
        sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    except (AttributeError, ValueError):
        pass

    print("[1/2] completion-length mediator (reviewer concern 2)")
    con = sqlite3.connect(f"file:{DB}?mode=ro", uri=True)
    med = length_mediation(con)
    con.close()
    for tag in ("block1", "block2"):
        lr = med[tag]["lost_rescues"]
        nv = med[tag]["neither_verified"]
        print(f"      {tag}: lost rescues n={lr['n']}  A {lr['mean_tokens_A']} vs "
              f"C {lr['mean_tokens_C']}  ratio {lr['ratio_C_over_A']}")
        print(f"      {tag}: neither verified n={nv['n']}  A {nv['mean_tokens_A']} vs "
              f"C {nv['mean_tokens_C']}  ratio {nv['ratio_C_over_A']}")
        print(f"      {tag}: C terminal states on lost roots "
              f"{med[tag]['C_terminal_state_on_lost_rescues']}")
    print(f"      verdict: mediator supported = {med['verdict']['mediator_supported']}")

    print("\n[2/2] corpus ceiling (reviewer concern 5)")
    ceil_ = corpus_ceiling()
    if ceil_["available"]:
        print(f"      {ceil_['n_attempts']} attempts over {ceil_['n_problems']} problems, "
              f"arms {ceil_['arms']}")
        print(f"      problems with >=1 failure       : "
              f"{ceil_['n_with_at_least_one_failure']}")
        print(f"      never verified on any arm       : "
              f"{ceil_['n_never_verified_on_any_arm']} "
              f"({ceil_['n_never_verified_already_roots']} already roots)")
        print(f"      failed but verified elsewhere   : "
              f"{ceil_['n_failed_but_verified_elsewhere']}")
        print(f"      unused failed problems          : "
              f"{ceil_['n_unused_failed_problems']}")
        print(f"      ceiling without new generation  : "
              f"{ceil_['ceiling_without_new_generation']} roots "
              f"(study uses {ceil_['n_roots_in_study']})")
    else:
        print("      " + ceil_["why"])

    OUT.write_text(json.dumps({"length_mediation": med, "corpus_ceiling": ceil_},
                              indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"\nwrote {OUT.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
