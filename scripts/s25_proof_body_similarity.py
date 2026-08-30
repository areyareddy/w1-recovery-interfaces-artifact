"""Step s25 -- retention restricted to the extracted Lean proof body.

    python scripts\\s25_proof_body_similarity.py              # CPU only, no server
    python scripts\\s25_proof_body_similarity.py --tokenize   # adds S_body, needs /tokenize

WHY THIS REPLACES THE s24 HEADLINE.

s24 compared two different metrics and read the gap as a finding: whole-completion token
similarity S against a longest-common-subsequence ratio over Lean tactic lines. Those are
not commensurable, so "proof-body agreement exceeds whole-text similarity" was not a claim
the numbers could support. Two further defects made the tactic figure itself unsafe:

  * the tactic detector is a hand-written name whitelist, so its coverage is unknown; and
  * lcs_ratio returns 1.0 when BOTH sides have no detected tactic line, which is vacuous.
    Those vacuous 1.0s were inside the reported mean.

This script fixes all three. It extracts the Lean proof body with the frozen extractor the
study already uses, drops the theorem signature -- which is identical across arms by
construction and would inflate every comparison -- and then applies the SAME token metric
the paper uses for S, to the body alone. S and S_body then differ only in their domain, so
the difference between them is interpretable.

    S       = anchoring similarity over the whole completion        (frozen, v7)
    S_body  = the same similarity over the extracted proof body     (new, this script)

Coverage is reported, not assumed: a branch contributes to S_body only when the extractor
returns a usable body on BOTH sides. Branches where it does not are counted and reported,
never scored as 1.0 or silently dropped from a denominator.

The paired C - A difference in S_body carries a bootstrap interval over roots, the same
resampling unit as every other interval in the paper.

TACTIC-LINE LCS is retained as a secondary descriptive, now with its undefined cases
separated out rather than folded into the mean.
"""

from __future__ import annotations

import argparse
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

import anchoring as anch  # noqa: E402
import policy  # noqa: E402
import receipts  # noqa: E402
import stats as st  # noqa: E402

DB = ROOT / "data/runs.sqlite"
ANCHOR = ROOT / "audit/anchoring_results.csv"
OUT_CSV = ROOT / "audit/proof_body_similarity.csv"
OUT_JSON = ROOT / "audit/proof_body_similarity.json"

# Same whitelist as s24, kept verbatim so the two scripts describe the same detector.
TACTIC = re.compile(
    r"^(nlinarith|linarith|norm_num|simp|ring_nf|ring|omega|decide|field_simp|"
    r"positivity|polyrith|intro|intros|induction|cases|rcases|obtain|use|refine|exact|"
    r"apply|constructor|rfl|subst|rw|unfold|have|calc|nlinarith|interval_cases|"
    r"push_cast|norm_cast|linear_combination|aesop|tauto|contrapose|by_contra)\b")
SIGNATURE = re.compile(r"^\s*(import|open|theorem|lemma|example|namespace|end|variable|"
                       r"set_option)\b")


def proof_body(text: str, theorem_text: str) -> tuple[str, str]:
    """(body, status). Status is one of ok / no_lean / no_body.

    The theorem signature is removed because it is byte-identical across arms for a given
    root: leaving it in would give every pair a floor of similarity that has nothing to do
    with what the model chose to keep.
    """
    lean = policy.extract_lean(text or "", theorem_text)
    if not lean or "theorem " not in lean:
        return "", "no_lean"
    lean = anch.normalize(policy.strip_lean_comments(lean))
    head = anch.normalize(policy.strip_lean_comments(theorem_text))
    if head and lean.startswith(head):
        body = lean[len(head):]
    else:
        # Fall back to the ":= by" that closes the statement; keep everything after the
        # first one, which is the top-level proof.
        m = re.search(r":=\s*by\b", lean)
        body = lean[m.end():] if m else ""
        if not body:
            drop = [ln for ln in lean.split("\n") if not SIGNATURE.match(ln)]
            body = "\n".join(drop)
    body = body.strip()
    return (body, "ok") if body else ("", "no_body")


def tactic_lines(body: str) -> list[str]:
    out = []
    for ln in body.replace("\r\n", "\n").split("\n"):
        s = ln.strip().lstrip("· ").lstrip("<;> ").strip()
        if s and not SIGNATURE.match(s) and TACTIC.match(s):
            out.append(s)
    return out


def lcs_ratio(a: list[str], b: list[str]):
    """2*LCS / (|a| + |b|), or None when neither side has a line -- undefined, not 1.0."""
    if not a and not b:
        return None
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


def mean_or_none(xs):
    xs = [x for x in xs if x is not None]
    return round(statistics.mean(xs), 4) if xs else None


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--tokenize", action="store_true",
                    help="compute S_body via the serving tokenizer (needs llama-server)")
    ap.add_argument("--base-url", default="http://127.0.0.1:8080")
    args = ap.parse_args()
    receipts.force_utf8()

    roots = {}
    for line in (ROOT / "data/roots.jsonl").open(encoding="utf-8"):
        r = json.loads(line)
        roots[r["root_id"]] = r
    prior = {d.name: (d / "raw_completion.txt").read_text(encoding="utf-8")
             for d in sorted((ROOT / "artifacts/roots").iterdir()) if d.is_dir()}
    print(f"[1/5] {len(prior)} prior attempts, {len(roots)} roots")

    token_S = {}
    for r in csv.DictReader(ANCHOR.open(encoding="utf-8")):
        token_S[(r["cohort"], r["root_id"], r["arm"])] = float(r["anchoring_S"])

    con = sqlite3.connect(f"file:{DB}?mode=ro", uri=True)
    rows = list(con.execute(
        "SELECT cohort, root_id, arm, verified, completion FROM branches "
        "WHERE status='done' ORDER BY cohort, root_id, arm"))
    con.close()
    print(f"[2/5] {len(rows)} done branches")

    print("[3/5] extracting proof bodies")
    out, bodies = [], {}
    for cohort, rid, arm, verified, completion in rows:
        thm = roots[rid]["theorem_text"]
        pbody, pstat = proof_body(prior[rid], thm)
        bbody, bstat = proof_body(completion or "", thm)
        covered = pstat == "ok" and bstat == "ok"
        pt, bt = tactic_lines(pbody), tactic_lines(bbody)
        rec = {
            "cohort": cohort, "root_id": rid, "arm": arm, "verified": verified,
            "token_S": token_S.get((cohort, rid, arm)),
            "prior_extract": pstat, "branch_extract": bstat, "covered": int(covered),
            "prior_body_chars": len(pbody), "branch_body_chars": len(bbody),
            "prior_tactic_lines": len(pt), "branch_tactic_lines": len(bt),
            "lcs_tactic": lcs_ratio(pt, bt),
            "S_body": None,
            # Byte identity is a stronger and simpler claim than "S = 1.0", which only
            # says token-identical after line-ending and trailing-whitespace
            # normalisation. Where it holds it should be the reported claim.
            "byte_identical": int((completion or "") == prior[rid]),
        }
        out.append(rec)
        if covered:
            bodies[(cohort, rid, arm)] = (pbody, bbody)

    n_cov = sum(r["covered"] for r in out)
    print(f"      extraction coverage: {n_cov}/{len(out)} branches "
          f"({100 * n_cov / len(out):.1f}%) yield a body on both sides")
    for side in ("prior_extract", "branch_extract"):
        fail = {}
        for r in out:
            if r[side] != "ok":
                fail[r[side]] = fail.get(r[side], 0) + 1
        print(f"      {side:15}: " + (", ".join(f"{k} {v}" for k, v in sorted(fail.items()))
                                      or "all ok"))
    n_undef = sum(1 for r in out if r["lcs_tactic"] is None)
    n_onesided = sum(1 for r in out
                     if r["lcs_tactic"] == 0.0
                     and (r["prior_tactic_lines"] == 0) != (r["branch_tactic_lines"] == 0))
    print(f"      tactic LCS undefined (no detected tactic on EITHER side): {n_undef}"
          f" -- excluded, not scored 1.0")
    print(f"      tactic LCS one-sided zero: {n_onesided}")

    if args.tokenize:
        print("[4/5] S_body via the serving tokenizer")
        tok = anch.ServerTokenizer(args.base_url)
        ok, detail = tok.probe()
        if not ok:
            print(f"      tokenizer unreachable: {detail}")
            print("      re-run with --tokenize once llama-server is free.")
            return 2
        print(f"      {detail}")
        for i, rec in enumerate(out, 1):
            key = (rec["cohort"], rec["root_id"], rec["arm"])
            if key in bodies:
                pb, bb = bodies[key]
                # proof_body() already applied anch.normalize, so declare it: the
                # tokenizer must see exactly the string the similarity is defined over.
                rec["S_body"] = round(anch.similarity(tok.tokens(pb, normalized=True),
                                                     tok.tokens(bb, normalized=True)), 6)
            if i % 100 == 0 or i == len(out):
                print(f"      {i}/{len(out)}")
    else:
        print("[4/5] S_body skipped (--tokenize not given; needs the serving tokenizer)")

    with OUT_CSV.open("w", encoding="utf-8", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(out[0].keys()))
        w.writeheader()
        w.writerows(out)

    print("\n[5/5] summary  (S over the whole completion; S_body and LCS over the body)")
    summary = []
    for cohort in ("primary_eval", "eval_block2", "full_pool_dev"):
        sub_c = [r for r in out if r["cohort"] == cohort]
        if not sub_c:
            continue
        print(f"\n  {cohort}")
        print(f"    {'arm':4} {'n':>3} {'cov':>4}  {'S':>7} {'S_body':>7} "
              f"{'LCS_tac':>8} {'n_def':>6}")
        for arm in "ABCDE":
            sub = [r for r in sub_c if r["arm"] == arm]
            if not sub:
                continue
            cov = [r for r in sub if r["covered"]]
            defined = [r for r in sub if r["lcs_tactic"] is not None]
            row = {
                "cohort": cohort, "arm": arm, "n": len(sub), "n_covered": len(cov),
                "coverage": round(len(cov) / len(sub), 4),
                "mean_S": mean_or_none(r["token_S"] for r in sub),
                "mean_S_body": mean_or_none(r["S_body"] for r in cov),
                "mean_lcs_tactic_defined": mean_or_none(
                    r["lcs_tactic"] for r in defined),
                "n_lcs_defined": len(defined),
                "n_lcs_undefined": len(sub) - len(defined),
            }
            summary.append(row)
            sb = f"{row['mean_S_body']:7.4f}" if row["mean_S_body"] is not None else "      -"
            print(f"    {arm:4} {len(sub):3d} {len(cov):4d}  {row['mean_S'] or 0:7.4f} "
                  f"{sb} {row['mean_lcs_tactic_defined'] or 0:8.4f} "
                  f"{row['n_lcs_defined']:6d}")

    # ---- paired contrasts on the SAME metric, roots as the resampling unit -------------
    print("\n  paired within-root contrasts (bootstrap over roots)")
    contrasts = []
    for cohort in ("primary_eval", "eval_block2", "full_pool_dev"):
        by = {}
        for r in out:
            if r["cohort"] == cohort:
                by.setdefault(r["root_id"], {})[r["arm"]] = r
        for x, y in (("C", "A"), ("D", "B")):
            for metric in ("S_body", "lcs_tactic", "token_S"):
                diffs = []
                for rid, arms in by.items():
                    if x in arms and y in arms:
                        a, b = arms[x][metric], arms[y][metric]
                        if a is not None and b is not None:
                            diffs.append(a - b)
                if len(diffs) < 5:
                    continue
                lo, hi = st.bootstrap_ci(diffs)
                # Marginal means are computed over every branch with a defined value;
                # the paired difference is computed over roots where BOTH arms are
                # defined. Those are different samples, so the marginals do not subtract
                # to the difference. Report the paired-subset means as well, so prose can
                # quote a triple that is internally consistent.
                px = [arms[x][metric] for arms in by.values()
                      if x in arms and y in arms
                      and arms[x][metric] is not None and arms[y][metric] is not None]
                py = [arms[y][metric] for arms in by.values()
                      if x in arms and y in arms
                      and arms[x][metric] is not None and arms[y][metric] is not None]
                rec = {"cohort": cohort, "contrast": f"{x}-{y}", "metric": metric,
                       "n_pairs": len(diffs), "mean_diff": round(statistics.mean(diffs), 4),
                       "ci95": [round(lo, 4), round(hi, 4)],
                       "paired_mean_x": round(statistics.mean(px), 4),
                       "paired_mean_y": round(statistics.mean(py), 4)}
                contrasts.append(rec)
                print(f"    {cohort:14} {x}-{y}  {metric:11} n={len(diffs):3d}  "
                      f"{rec['mean_diff']:+.4f}  [{lo:+.4f}, {hi:+.4f}]")

    # ---- near-verbatim, reported per cohort and arm -----------------------------------
    # The published sentence mixed a block-1 arm-C percentage with a tactic figure pooled
    # over every cohort, implying both described the same four branches. Keep them apart.
    NV = 0.90
    near = []
    for cohort in ("primary_eval", "eval_block2", "full_pool_dev"):
        for arm in "ABCDE":
            sub_a = [r for r in out if r["cohort"] == cohort and r["arm"] == arm
                     and r["token_S"] is not None]
            if not sub_a:
                continue
            nv = [r for r in sub_a if r["token_S"] >= NV]
            defined = [r["lcs_tactic"] for r in nv if r["lcs_tactic"] is not None]
            near.append({
                "cohort": cohort, "arm": arm, "n": len(sub_a), "near_verbatim": len(nv),
                "pct": round(100 * len(nv) / len(sub_a), 1),
                "max_S": round(max(r["token_S"] for r in sub_a), 4),
                "byte_identical": sum(r["byte_identical"] for r in nv),
                "n_lcs_defined": len(defined),
                "mean_lcs_tactic": mean_or_none(defined),
                "roots": sorted(r["root_id"] for r in nv),
            })
    pooled_nv = [r for r in out if r["arm"] == "C" and r["token_S"] is not None
                 and r["token_S"] >= NV]
    pooled_def = [r["lcs_tactic"] for r in pooled_nv if r["lcs_tactic"] is not None]

    # The fresh-generation ceiling. Arms A and B carry no prior attempt, so their
    # similarity to it is the null this comparison rests on. It must be the maximum over
    # BOTH fresh arms and ALL cohorts, not over arm A of one cohort.
    fresh = [r for r in out if r["arm"] in ("A", "B") and r["token_S"] is not None]
    top = max(fresh, key=lambda r: r["token_S"])
    print(f"\n  fresh-generation ceiling: max S over arms A and B, all cohorts = "
          f"{top['token_S']:.4f}  ({top['cohort']} {top['arm']} {top['root_id']})")
    print(f"  near-verbatim threshold {NV}; pooled arm-C near-verbatim {len(pooled_nv)}, "
          f"{len(pooled_def)} with a defined tactic ratio, "
          f"{sum(r['byte_identical'] for r in pooled_nv)} byte-identical")

    # ---- S and S_body on the SAME roots ------------------------------------------------
    # Same metric, two domains, one sample: the only comparison of the two that is fair.
    print("\n  localization: S vs S_body on the identical root set")
    localization = []
    for cohort in ("primary_eval", "eval_block2", "full_pool_dev"):
        by = {}
        for r in out:
            if r["cohort"] == cohort:
                by.setdefault(r["root_id"], {})[r["arm"]] = r
        d_whole, d_body, gap = [], [], []
        for rid, arms in by.items():
            if "A" not in arms or "C" not in arms:
                continue
            a, c = arms["A"], arms["C"]
            if None in (a["S_body"], c["S_body"], a["token_S"], c["token_S"]):
                continue
            dw = c["token_S"] - a["token_S"]
            db = c["S_body"] - a["S_body"]
            d_whole.append(dw)
            d_body.append(db)
            gap.append(db - dw)
        if len(gap) < 5:
            continue
        glo, ghi = st.bootstrap_ci(gap)
        rec = {"cohort": cohort, "n": len(gap),
               "mean_diff_whole": round(statistics.mean(d_whole), 4),
               "mean_diff_body": round(statistics.mean(d_body), 4),
               "mean_gap": round(statistics.mean(gap), 4),
               "gap_ci95": [round(glo, 4), round(ghi, 4)],
               "n_gap_positive": sum(1 for g in gap if g > 0)}
        localization.append(rec)
        print(f"    {cohort:14} n={rec['n']:3d}  whole {rec['mean_diff_whole']:+.3f}  "
              f"body {rec['mean_diff_body']:+.3f}  gap {rec['mean_gap']:+.3f} "
              f"[{glo:+.3f}, {ghi:+.3f}]  positive {rec['n_gap_positive']}/{rec['n']}")

    payload = {
        "coverage": {"n_branches": len(out), "n_covered": n_cov,
                     "fraction": round(n_cov / len(out), 4),
                     "lcs_undefined": n_undef, "lcs_one_sided_zero": n_onesided},
        "summary": summary,
        "contrasts": contrasts,
        "near_verbatim": {"threshold": NV, "rows": near,
                          "pooled_C": {"n": len(pooled_nv),
                                       "n_lcs_defined": len(pooled_def),
                                       "mean_lcs_tactic": mean_or_none(pooled_def),
                                       "byte_identical": sum(r["byte_identical"]
                                                             for r in pooled_nv)}},
        "localization": localization,
        "fresh_ceiling": {"max_S": round(top["token_S"], 4), "cohort": top["cohort"],
                          "arm": top["arm"], "root_id": top["root_id"]},
        "tokenized": bool(args.tokenize),
    }
    OUT_JSON.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n",
                        encoding="utf-8")
    print(f"\nwrote {OUT_CSV.relative_to(ROOT).as_posix()} and "
          f"{OUT_JSON.relative_to(ROOT).as_posix()}")
    if not args.tokenize:
        print("S_body is still empty. Re-run with --tokenize when the GPU slot is free.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
