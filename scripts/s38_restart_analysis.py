"""Step s38 -- restart-permissive arms. Analysis frozen in spec/RESTART_SPEC.md.

    python scripts\\s38_restart_analysis.py

EXPLORATORY ROBUSTNESS, NOT CONFIRMATORY. The design was recorded before generation
(scripts/s32_build_restart.py docstring, written 00:40 local; first branch 12:20:44Z), but
the statistical plan was written after generation, with no restart outcome read --
scripts/s37_restart_verify.py validated the arms structurally first and deliberately reads
no verification result. spec/RESTART_SPEC.md section 0 states both halves. Every number
this script prints must be labelled exploratory wherever it is reported.

WHAT IT ANSWERS. W1 limitation (7): every arm's prompt tells the model to commit to its
first derivation, so in arms C and C' -- where the thing in context is a rejected proof --
the retention finding may be partly a restatement of that instruction. The restart triple
substitutes exactly one sentence, permitting abandonment, and asks whether the effect
survives.

    C-R  - C'-R                     does trajectory-specific harm survive?
    C'-R - A-R                      generic long-context cost under restart permission
    (C-R - C'-R) - (C - C')         did the commit instruction amplify it?

Holm family is {C'-R - A-R, C-R - C'-R}, size 2, mirroring spec/CPRIME_SPEC.md section 6.
The interaction is descriptive and enters no family; its resolution is reported with it,
because an under-resolved interaction at n=40 is the expected outcome and is NOT evidence
of no amplification.
"""

from __future__ import annotations

import json
import random
import sqlite3
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT / "src"))
sys.path.insert(0, str(HERE))

import receipts  # noqa: E402
import stats as st  # noqa: E402
import s17_statistical_tests as pair  # noqa: E402
import s27_interaction_resolution as s27  # noqa: E402

RUNS_DB = ROOT / "data/runs.sqlite"
RESTART_DB = ROOT / "data/restart.sqlite"
CPRIME_DB = ROOT / "data/cprime.sqlite"
VERIFY = ROOT / "audit/restart_verify.json"
OUT = ROOT / "audit/restart_analysis.json"


def load() -> dict:
    """Six arms over the same 40 roots: A, C (block 1), Cp (block 1), AR, CR, CpR."""
    data: dict = {}
    con = sqlite3.connect(f"file:{RUNS_DB}?mode=ro", uri=True)
    for root, arm, v, state, tok in con.execute(
            "SELECT root_id, arm, verified, outcome_state, completion_tokens "
            "FROM branches WHERE cohort='primary_eval' AND status='done' "
            "AND arm IN ('A','C')"):
        data.setdefault(arm, {})[root] = {"v": int(bool(v)), "state": state, "tok": tok or 0}
    con.close()
    con = sqlite3.connect(f"file:{CPRIME_DB}?mode=ro", uri=True)
    for root, v, state, tok in con.execute(
            "SELECT root_id, verified, outcome_state, completion_tokens "
            "FROM branches WHERE cohort='eval_cprime' AND status='done'"):
        data.setdefault("Cp", {})[root] = {"v": int(bool(v)), "state": state,
                                           "tok": tok or 0}
    con.close()
    con = sqlite3.connect(f"file:{RESTART_DB}?mode=ro", uri=True)
    for root, arm, v, state, tok in con.execute(
            "SELECT root_id, arm, verified, outcome_state, completion_tokens "
            "FROM branches WHERE status='done'"):
        data.setdefault(arm, {})[root] = {"v": int(bool(v)), "state": state,
                                          "tok": tok or 0}
    con.close()
    return data


def contrast(xn, yn, roots, data) -> dict:
    xs = [data[xn][r]["v"] for r in roots]
    ys = [data[yn][r]["v"] for r in roots]
    b = sum(1 for x, y in zip(xs, ys) if x == 1 and y == 0)
    c = sum(1 for x, y in zip(xs, ys) if x == 0 and y == 1)
    both = sum(1 for x, y in zip(xs, ys) if x == 1 and y == 1)
    lo, hi = st.bootstrap_ci([x - y for x, y in zip(xs, ys)])
    return {"contrast": f"{xn}-{yn}", "n": len(roots), "x_only": b, "y_only": c,
            "both": both, "effect": round((b - c) / len(roots), 4),
            "ci95": [round(lo, 4), round(hi, 4)],
            "p_exact_mcnemar": round(pair.mcnemar_exact(b, c), 6)}


def main() -> int:
    receipts.force_utf8()
    if not VERIFY.exists():
        print("run scripts/s37_restart_verify.py first")
        return 2
    ver = json.loads(VERIFY.read_text(encoding="utf-8"))
    if ver.get("problems"):
        print("s37 reported problems; refusing to analyse")
        return 2
    print(f"[0/5] structural verification passed "
          f"({ver['payload_audit']['reversible']}/{ver['payload_audit']['checked']} "
          "payloads reversible)")
    print("      EXPLORATORY ROBUSTNESS -- statistical plan written after generation")

    data = load()
    arms = ["A", "C", "Cp", "AR", "CR", "CpR"]
    roots = sorted(set.intersection(*(set(data[a]) for a in arms)))
    print(f"\n[1/5] {len(roots)} roots present in all six arms")
    results: dict = {"n": len(roots), "confirmatory": False,
                     "registration": "exploratory robustness; see spec/RESTART_SPEC.md s0",
                     "roots": len(roots)}

    print("\n[2/5] verification rates (same 40 theorems; NOT independent replicates)")
    rates = {a: sum(data[a][r]["v"] for r in roots) for a in arms}
    for a in arms:
        print(f"      {a:4} {rates[a]:2d}/{len(roots)}")
    results["verified_counts"] = rates

    print("\n[3/5] contrasts (exact McNemar, paired within root)")
    cons = [contrast("CR", "CpR", roots, data),
            contrast("CpR", "AR", roots, data),
            contrast("C", "Cp", roots, data),      # original, for the interaction
            contrast("AR", "A", roots, data)]      # rate anchor, reference only
    family = ["CpR-AR", "CR-CpR"]
    fam = [c for c in cons if c["contrast"] in family]
    adj = st.holm({c["contrast"]: c["p_exact_mcnemar"] for c in fam})
    for c in fam:
        c["p_holm"] = round(adj[c["contrast"]], 6)
        c["holm_family"] = "restart_verification"
    for c in cons:
        tag = (f"  Holm {c['p_holm']:.4f}" if "p_holm" in c else
               "  (reference only)" if c["contrast"] == "AR-A" else
               "  (original, for the interaction)")
        print(f"      {c['contrast']:10} {c['x_only']:2d} vs {c['y_only']:2d} discordant"
              f"   effect {c['effect']:+.3f} [{c['ci95'][0]:+.3f}, {c['ci95'][1]:+.3f}]"
              f"   p={c['p_exact_mcnemar']:.4f}{tag}")
    results["contrasts"] = cons
    results["holm_family"] = {"members": family,
                              "descriptive_only": ["interaction", "AR-A"]}

    print("\n[4/5] interaction: did the commit instruction amplify the effect?")
    w = [(data["CR"][r]["v"] - data["CpR"][r]["v"])
         - (data["C"][r]["v"] - data["Cp"][r]["v"]) for r in roots]
    n = len(w)
    point = sum(w) / n
    lo, hi = st.bootstrap_ci(w)
    var = sum((x - point) ** 2 for x in w) / (n - 1)
    se = (var / n) ** 0.5
    mde_a = (s27.Z_ALPHA + s27.Z_POWER) * se
    rng = random.Random(s27.SEED)
    sim = None
    for delta in [x / 100 for x in range(1, 81)]:
        if s27.power_at(w, delta, s27.REPS, rng) >= 0.80:
            sim = round(delta, 2)
            break
    resolved = abs(point) >= mde_a
    print(f"      w = (CR-CpR) - (C-Cp) per root")
    print(f"      point {point:+.3f}  95% CI [{lo:+.3f}, {hi:+.3f}]  SE {se:.4f}")
    print(f"      analytic 80% MDE {mde_a:.3f}   simulated {sim if sim else '>0.80'}")
    print(f"      -> {'RESOLVED' if resolved else 'UNDER-RESOLVED'}")
    print("      An under-resolved interaction is NOT evidence of no amplification.")
    results["interaction"] = {
        "definition": "w_i = (CR_i - CpR_i) - (C_i - Cp_i)",
        "n": n, "point": round(point, 4), "ci95": [round(lo, 4), round(hi, 4)],
        "se": round(se, 4), "mde_analytic_80": round(mde_a, 4),
        "mde_simulated_80": sim, "resolved": resolved,
        "in_test_family": False,
        "note": ("Descriptive. At n=40 an under-resolved interaction is the expected "
                 "outcome and must not be read as evidence of no amplification.")}

    print("\n[5/5] outcome states and truncation")
    states: dict = {}
    for a in arms:
        row: dict = {}
        for r in roots:
            row[data[a][r]["state"]] = row.get(data[a][r]["state"], 0) + 1
        states[a] = row
        print(f"      {a:4} " + "  ".join(f"{k} {v}" for k, v in sorted(row.items())))
    results["outcome_states"] = states

    # section 5 interpretation, fixed in advance
    cr = next(c for c in cons if c["contrast"] == "CR-CpR")
    harm = cr["ci95"][1] < 0
    if harm and not resolved:
        # The interaction being under-resolved is NOT the interaction being zero. Section 3
        # of the spec says so explicitly, so the conclusion here stops at what survives.
        row = ("C-R - C'-R negative and resolved, interaction under-resolved",
               "trajectory-specific harm survives restart permission, so limitation (7)'s "
               "confound does not account for the effect. The interaction is "
               "under-resolved, so how much the commit instruction contributed is not "
               "estimable and must not be reported as zero")
    elif harm and resolved and point >= -1e-9:
        row = ("C-R - C'-R negative and resolved, interaction resolved and ~ 0",
               "trajectory-specific harm survives and the commit instruction was not the "
               "mechanism; limitation (7) is answered")
    elif not harm and resolved and point < 0:
        row = ("C-R - C'-R ~ 0, interaction negative",
               "the original effect depended on the commit instruction; the mechanism "
               "claim must be narrowed to the committed-interface setting")
    elif harm and resolved:
        row = ("C-R - C'-R negative, interaction also negative",
               "harm survives but is attenuated; the instruction contributes without "
               "being necessary")
    else:
        row = ("both under-resolved",
               "report as under-resolved with intervals; name no mechanism, and leave "
               "limitation (7) standing")
    print(f"\n{'=' * 70}\nINTERPRETATION -- spec/RESTART_SPEC.md section 5, fixed in advance")
    print(f"  observed : {row[0]}")
    print(f"  reading  : {row[1]}")
    results["interpretation"] = {"row": row[0], "reading": row[1],
                                 "source": "spec/RESTART_SPEC.md section 5",
                                 "confirmatory": False}

    OUT.write_text(json.dumps(results, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"\nwrote {OUT.relative_to(ROOT).as_posix()}")
    print("Restart arms are EXPLORATORY and must be labelled as such wherever reported.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
