"""Step s26 -- decompose the verification deficit: worse proofs, or more malformed output?

    python scripts\\s26_outcome_decomposition.py       # CPU only, no server

THE QUESTION. Verification is monotone in prompt length in both evaluation blocks
(9 > 4 > 2 > 1 and 9 > 6 > 1 > 1). Two very different accounts predict that:

  (a) prior access produces WORSE PROOFS -- branches reach the Lean kernel and are
      rejected on their mathematics;
  (b) prior access produces MORE MALFORMED OUTPUT -- branches exhaust the token budget or
      emit unusable text and never reach the kernel at all.

(b) would make the headline a statement about generation length, not about reasoning.
Nothing in the paper separated them. This script does.

The harness already records the distinction, so no new measurement is needed. Every done
branch is in exactly one terminal state:

    verified      reached the kernel and was accepted
    lean_failed   reached the kernel and was rejected  -> account (a)
    truncated     never reached the kernel              -> account (b)

The decisive quantity is the verification rate CONDITIONAL ON REACHING THE KERNEL. If
account (b) were driving the deficit, that conditional rate would be flat across arms and
only the truncation rate would move.

THE DEDUCTIVE CHAIN. Separately, a branch that reproduces its root's rejected attempt
byte-for-byte cannot verify: the kernel is deterministic and already rejected that exact
input. For those branches the link from prior access to failure is deductive rather than
statistical. This script identifies them, confirms none was rejected under a
nondeterministic class such as a timeout, and reports what share of the C-A deficit they
account for.
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
import stats as st  # noqa: E402
import s17_statistical_tests as pair  # noqa: E402

DB = ROOT / "data/runs.sqlite"
BODY = ROOT / "audit/proof_body_similarity.csv"
OUT_JSON = ROOT / "audit/outcome_decomposition.json"
OUT_CSV = ROOT / "audit/outcome_decomposition.csv"

COHORTS = ("primary_eval", "eval_block2", "full_pool_dev")
# Error classes that are not a deterministic function of the input. A byte-identical
# resubmission rejected under one of these could in principle behave differently on a
# rerun, so it cannot support a deductive claim.
NONDETERMINISTIC = {"timeout"}


def main() -> int:
    receipts.force_utf8()
    con = sqlite3.connect(f"file:{DB}?mode=ro", uri=True)

    # ---------------------------------------------------------------- 1. state table
    print("[1/4] terminal state by arm\n")
    print(f"  {'cohort':14} {'arm':3} {'n':>3} {'verified':>8} {'lean_failed':>11} "
          f"{'truncated':>9} | {'reached':>7} {'ver|reached':>11}")
    rows, table = [], {}
    for cohort in COHORTS:
        for arm in "ABCDE":
            d = dict(con.execute(
                "SELECT outcome_state, count(*) FROM branches WHERE cohort=? AND arm=? "
                "AND status='done' GROUP BY outcome_state", (cohort, arm)))
            if not d:
                continue
            v, lf = d.get("verified", 0), d.get("lean_failed", 0)
            tr, n = d.get("truncated", 0), sum(d.values())
            reached = v + lf
            rec = {"cohort": cohort, "arm": arm, "n": n, "verified": v,
                   "lean_failed": lf, "truncated": tr, "reached": reached,
                   "trunc_rate": round(tr / n, 4),
                   "ver_given_reached": round(v / reached, 4) if reached else None}
            rows.append(rec)
            table[(cohort, arm)] = rec
            print(f"  {cohort:14} {arm:3} {n:3d} {v:8d} {lf:11d} {tr:9d} | "
                  f"{reached:7d} {rec['ver_given_reached'] or 0:11.3f}")
        print()

    # ------------------------------------------------- 2. paired tests on both channels
    print("[2/4] paired within-root contrasts, both channels\n")
    print("  Truncation is the malformed-output channel; verification given reach is the")
    print("  proof-quality channel. If the deficit were malformed output, truncation would")
    print("  rise with prompt length and the conditional rate would stay flat.\n")
    contrasts = []
    for cohort in COHORTS:
        for x, y in (("C", "A"), ("D", "B")):
            got = {}
            for arm in (x, y):
                got[arm] = {r[0]: r[1] for r in con.execute(
                    "SELECT root_id, outcome_state FROM branches WHERE cohort=? AND arm=? "
                    "AND status='done'", (cohort, arm))}
            shared = sorted(set(got[x]) & set(got[y]))
            if not shared:
                continue
            # truncation, paired
            tb = sum(1 for r in shared
                     if got[x][r] == "truncated" and got[y][r] != "truncated")
            tc = sum(1 for r in shared
                     if got[x][r] != "truncated" and got[y][r] == "truncated")
            p_tr = pair.mcnemar_exact(tb, tc)
            lo, hi = st.bootstrap_ci(
                [(got[x][r] == "truncated") - (got[y][r] == "truncated")
                 for r in shared])
            # verification among roots where BOTH arms reached the kernel
            both = [r for r in shared
                    if got[x][r] != "truncated" and got[y][r] != "truncated"]
            vb = sum(1 for r in both
                     if got[x][r] == "verified" and got[y][r] != "verified")
            vc = sum(1 for r in both
                     if got[x][r] != "verified" and got[y][r] == "verified")
            p_v = pair.mcnemar_exact(vb, vc) if both else float("nan")
            rec = {"cohort": cohort, "contrast": f"{x}-{y}", "n_pairs": len(shared),
                   "trunc_x_only": tb, "trunc_y_only": tc,
                   "trunc_effect": round((tb - tc) / len(shared), 4),
                   "trunc_ci95": [round(lo, 4), round(hi, 4)],
                   "trunc_p": round(p_tr, 6),
                   "n_both_reached": len(both),
                   "ver_x_only": vb, "ver_y_only": vc,
                   "ver_p_given_both_reached": round(p_v, 6) if both else None}
            contrasts.append(rec)
            print(f"  {cohort:14} {x}-{y}  truncation {tb:2d} vs {tc:2d} "
                  f"({rec['trunc_effect']:+.3f} [{lo:+.3f},{hi:+.3f}], p={p_tr:.4f})")
            print(f"  {'':14}       among the {len(both):2d} roots where both reached "
                  f"the kernel: {x}-only {vb}, {y}-only {vc}, p={p_v:.4f}")
        print()

    # ---------------------------------------------------- 3. error classes among failures
    print("[3/4] error class among branches that reached the kernel and failed\n")
    classes = sorted({r[0] for r in con.execute(
        "SELECT DISTINCT error_class FROM branches WHERE outcome_state='lean_failed'")})
    err = {}
    for cohort in COHORTS:
        for arm in "ABCDE":
            d = dict(con.execute(
                "SELECT error_class, count(*) FROM branches WHERE cohort=? AND arm=? "
                "AND outcome_state='lean_failed' GROUP BY error_class", (cohort, arm)))
            if d:
                err[f"{cohort}.{arm}"] = d
    hdr = "  " + f"{'cohort':14} {'arm':3} " + " ".join(f"{c[:9]:>9}" for c in classes)
    print(hdr)
    for cohort in COHORTS:
        for arm in "ABCDE":
            d = err.get(f"{cohort}.{arm}")
            if d:
                print(f"  {cohort:14} {arm:3} " +
                      " ".join(f"{d.get(c, 0):9d}" for c in classes))
        print()

    # ------------------------------------------------------- 4. the deductive chain
    print("[4/4] byte-identical resubmissions: a deductive link to failure\n")
    ded = []
    if BODY.exists():
        for r in csv.DictReader(BODY.open(encoding="utf-8")):
            if r["byte_identical"] != "1":
                continue
            st_, ec, ver = con.execute(
                "SELECT outcome_state, error_class, verified FROM branches "
                "WHERE cohort=? AND arm=? AND root_id=?",
                (r["cohort"], r["arm"], r["root_id"])).fetchone()
            ded.append({"cohort": r["cohort"], "arm": r["arm"], "root_id": r["root_id"],
                        "branch_outcome": st_, "branch_error_class": ec,
                        "verified": ver,
                        "nondeterministic_class": ec in NONDETERMINISTIC})
    for r in ded:
        print(f"  {r['cohort']:14} {r['arm']:2} {r['root_id'][:40]:40} "
              f"{r['branch_outcome']}/{r['branch_error_class']}")
    assert all(r["verified"] == 0 for r in ded), \
        "a byte-identical resubmission verified -- the kernel is not deterministic"
    nd = [r for r in ded if r["nondeterministic_class"]]
    print(f"\n  {len(ded)} byte-identical branches, all rejected, "
          f"{len(nd)} under a nondeterministic class")
    if not nd:
        print("  -> every one failed under a deterministic class, so the resubmission")
        print("     could not have verified. The link is deductive, not statistical.")

    # Share of the C-A deficit these account for. This must be an OVERLAP, not a ratio
    # of two independently counted things: a byte-identical C branch only explains a lost
    # rescue if arm A actually verified THAT root. Dividing the byte-identical count by
    # the deficit overstates it -- in block 1 it gives 3/7 when the answer is 2/7, because
    # one of the three roots (amc12_2001_p21) was not rescued by A either.
    print()
    share = {}
    for cohort in COHORTS:
        rows_ac = con.execute(
            "SELECT root_id, max(CASE WHEN arm='A' THEN verified END), "
            "       max(CASE WHEN arm='C' THEN verified END) FROM branches "
            "WHERE cohort=? AND status='done' AND arm IN ('A','C') "
            "GROUP BY root_id HAVING count(*)=2", (cohort,)).fetchall()
        a_only = {r for r, a, c in rows_ac if a == 1 and c == 0}
        bi_c = {r["root_id"] for r in ded
                if r["cohort"] == cohort and r["arm"] == "C"}
        both = a_only & bi_c
        share[cohort] = {
            "a_only_discordant": len(a_only),
            "byte_identical_C": len(bi_c),
            "byte_identical_among_a_only": len(both),
            "roots": sorted(both),
            "share_of_lost_rescues": round(len(both) / len(a_only), 4) if a_only else None}
        if a_only:
            print(f"  {cohort:14} {len(a_only)} lost rescues (A verified, C did not); "
                  f"{len(both)} of them are roots whose C branch reproduced the rejected "
                  f"attempt byte-for-byte")
            if len(bi_c) > len(both):
                print(f"  {'':14} ({len(bi_c) - len(both)} further byte-identical C "
                      f"branch(es) sit on roots A did not verify either, so they are not "
                      f"part of the deficit)")

    con.close()
    with OUT_CSV.open("w", encoding="utf-8", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)
    OUT_JSON.write_text(json.dumps(
        {"states": rows, "contrasts": contrasts, "error_classes": err,
         "deductive": ded, "deficit_share": share}, indent=2, sort_keys=True) + "\n",
        encoding="utf-8")
    print(f"\nwrote {OUT_CSV.relative_to(ROOT).as_posix()} and "
          f"{OUT_JSON.relative_to(ROOT).as_posix()}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
