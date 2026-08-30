"""Step s24 -- line- and tactic-level similarity. Answers the reviewer's metric objection.

Token-level Levenshtein over the whole completion cannot tell three very different things
apart:

    reusing `import Mathlib` and the theorem signature   -- forced, carries no information
    reusing the prose plan                                -- stylistic
    reusing the TACTIC BODY of a proof Lean rejected      -- the behaviour the paper claims

That matters most for the one anchoring claim the reframe keeps: that ~10% of arm-C
completions reproduce the failed attempt near-verbatim. If that similarity were mostly
boilerplate, the claim would be empty. This script measures it directly.

Three endpoints per branch, all against the root's own prior attempt:

    LCS_line     longest-common-subsequence ratio over normalized non-empty lines
    LCS_tactic   the same, restricted to lines that begin a Lean tactic, with imports,
                 the theorem signature, comments and prose excluded
    jaccard_tac  set overlap of tactic tokens, order-free

Read together with S: if S is high but LCS_tactic is low, arm C is echoing scaffolding. If
LCS_tactic tracks S, it is reproducing the rejected proof itself.

CPU only. Uses the stored completions; no server, no GPU.
"""

from __future__ import annotations

import csv
import json
import re
import sqlite3
import statistics
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT / "src"))
sys.path.insert(0, str(HERE))

import policy  # noqa: E402
import receipts  # noqa: E402

DB = ROOT / "data/runs.sqlite"
ANCHOR = ROOT / "audit/anchoring_results.csv"
OUT_CSV = ROOT / "audit/line_level_similarity.csv"
OUT_JSON = ROOT / "audit/line_level_similarity.json"

# A Lean tactic line starts with a tactic name. This list is deliberately broad; anything
# not matched is treated as non-tactic, which is the conservative direction here.
TACTIC = re.compile(
    r"^(nlinarith|linarith|norm_num|simp|ring_nf|ring|omega|decide|field_simp|"
    r"positivity|polyrith|intro|intros|induction|cases|rcases|obtain|use|refine|exact|"
    r"apply|constructor|rfl|subst|rw|unfold|have|calc|nlinarith|interval_cases|"
    r"push_cast|norm_cast|linear_combination|aesop|tauto|contrapose|by_contra)\b")
SIGNATURE = re.compile(r"^\s*(import|open|theorem|lemma|example|namespace|end|variable)\b")


def lines_of(text: str) -> list[str]:
    return [ln.strip() for ln in text.replace("\r\n", "\n").split("\n") if ln.strip()]


def tactic_lines(text: str) -> list[str]:
    """Proof body only: no imports, no signature, no comments, no prose."""
    out = []
    for ln in lines_of(policy.strip_lean_comments(text)):
        s = ln.lstrip("· ").lstrip("<;> ").strip()
        if SIGNATURE.match(s):
            continue
        if TACTIC.match(s):
            out.append(s)
    return out


def lcs_ratio(a: list[str], b: list[str]) -> float:
    """2*LCS / (|a| + |b|). Rolling row keeps this O(min) memory."""
    if not a and not b:
        return 1.0
    if not a or not b:
        return 0.0
    if len(a) < len(b):
        a, b = b, a
    prev = [0] * (len(b) + 1)
    for x in a:
        cur = [0] * (len(b) + 1)
        for j, y in enumerate(b, 1):
            cur[j] = prev[j - 1] + 1 if x == y else max(prev[j], cur[j - 1])
        prev = cur
    return 2.0 * prev[-1] / (len(a) + len(b))


def jaccard(a: list[str], b: list[str]) -> float:
    sa, sb = set(a), set(b)
    if not sa and not sb:
        return 1.0
    return len(sa & sb) / len(sa | sb) if (sa | sb) else 0.0


def main() -> int:
    receipts.force_utf8()

    prior = {}
    for d in sorted((ROOT / "artifacts/roots").iterdir()):
        if d.is_dir():
            prior[d.name] = (d / "raw_completion.txt").read_text(encoding="utf-8")
    print(f"[1/3] {len(prior)} prior attempts loaded")

    token_S = {}
    for r in csv.DictReader(ANCHOR.open(encoding="utf-8")):
        token_S[(r["cohort"], r["root_id"], r["arm"])] = float(r["anchoring_S"])

    con = sqlite3.connect(f"file:{DB}?mode=ro", uri=True)
    rows = list(con.execute(
        "SELECT cohort, root_id, arm, verified, completion FROM branches "
        "WHERE status='done' ORDER BY cohort, root_id, arm"))
    con.close()
    print(f"[2/3] scoring {len(rows)} branches (line and tactic level)")

    out = []
    for i, (cohort, rid, arm, verified, completion) in enumerate(rows, 1):
        p = prior[rid]
        pl, cl = lines_of(p), lines_of(completion or "")
        pt, ct = tactic_lines(p), tactic_lines(completion or "")
        out.append({
            "cohort": cohort, "root_id": rid, "arm": arm, "verified": verified,
            "token_S": token_S.get((cohort, rid, arm)),
            "lcs_line": round(lcs_ratio(pl, cl), 6),
            "lcs_tactic": round(lcs_ratio(pt, ct), 6),
            "jaccard_tactic": round(jaccard(pt, ct), 6),
            "prior_tactic_lines": len(pt), "branch_tactic_lines": len(ct),
        })
        if i % 100 == 0 or i == len(rows):
            print(f"      {i}/{len(rows)}")

    with OUT_CSV.open("w", encoding="utf-8", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(out[0].keys()))
        w.writeheader()
        w.writerows(out)

    print("\n[3/3] summary")
    summary = []
    for cohort in ("primary_eval", "eval_block2", "full_pool_dev"):
        print(f"\n  {cohort}")
        print(f"    {'arm':4} {'n':>3}  {'token S':>8} {'LCS line':>9} "
              f"{'LCS tactic':>11} {'Jaccard':>8}")
        for arm in "ABCDE":
            sub = [r for r in out if r["cohort"] == cohort and r["arm"] == arm]
            if not sub:
                continue
            ts = [r["token_S"] for r in sub if r["token_S"] is not None]
            row = {"cohort": cohort, "arm": arm, "n": len(sub),
                   "mean_token_S": round(statistics.mean(ts), 4) if ts else None,
                   "mean_lcs_line": round(statistics.mean(
                       r["lcs_line"] for r in sub), 4),
                   "mean_lcs_tactic": round(statistics.mean(
                       r["lcs_tactic"] for r in sub), 4),
                   "mean_jaccard_tactic": round(statistics.mean(
                       r["jaccard_tactic"] for r in sub), 4)}
            summary.append(row)
            print(f"    {arm:4} {len(sub):3d}  {row['mean_token_S'] or 0:8.4f} "
                  f"{row['mean_lcs_line']:9.4f} {row['mean_lcs_tactic']:11.4f} "
                  f"{row['mean_jaccard_tactic']:8.4f}")

    # the claim that matters: are the near-verbatim arm-C branches reproducing PROOFS?
    print("\n  Near-verbatim arm-C branches (token S >= 0.90):")
    nv = [r for r in out if r["arm"] == "C" and (r["token_S"] or 0) >= 0.90]
    for r in nv:
        print(f"    {r['cohort']:14} {r['root_id'][:34]:34} S={r['token_S']:.3f}  "
              f"LCS_line={r['lcs_line']:.3f}  LCS_tactic={r['lcs_tactic']:.3f}  "
              f"tactics {r['prior_tactic_lines']}->{r['branch_tactic_lines']}")
    if nv:
        print(f"\n    mean LCS_tactic among these {len(nv)}: "
              f"{statistics.mean(r['lcs_tactic'] for r in nv):.4f}")
        print("    If this is high, near-verbatim means the PROOF BODY was reproduced,")
        print("    not just imports and the theorem signature.")

    OUT_JSON.write_text(json.dumps(
        {"summary": summary, "near_verbatim_C": nv}, indent=2, sort_keys=True) + "\n",
        encoding="utf-8")
    print(f"\nwrote {OUT_CSV.relative_to(ROOT).as_posix()} and "
          f"{OUT_JSON.relative_to(ROOT).as_posix()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
