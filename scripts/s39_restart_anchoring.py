"""Step s39 -- anchoring and proof-body similarity for the restart-permissive arms.

    python scripts\\s39_restart_anchoring.py       (needs the tokenizer on :8080)

EXPLORATORY, like everything about the restart arms (spec/RESTART_SPEC.md section 0).
Descriptive throughout; no test, no family, no p-value.

THE QUESTION. s38 shows trajectory-specific harm survives when the model is explicitly told
it may abandon the attempt. This asks the mechanism question underneath it: does restart
permission change how much of the prior attempt the model actually REPRODUCES? Three
readings, and the arms separate them:

    S(C-R, own) ~ S(C, own)     permission does not reduce copying -- the model retains the
                                trajectory whether or not it is told it may leave it
    S(C-R, own) <  S(C, own)    permission reduces copying, yet s38 shows the verification
                                deficit persists -- so retention and harm come apart, and
                                copying is not the whole mechanism
    S(C'-R, donor) near null    the model does not copy whatever occupies the slot, which
                                is the same tautology answer C' gives under commit

Two metrics, the same pair of domains as the main paper:
    S       token-level similarity over the whole completion (src/anchoring.py)
    S_body  the same metric on the extracted Lean proof body (scripts/s25 proof_body)
Because only the domain changes, S and S_body are directly comparable.
"""

from __future__ import annotations

import csv
import json
import sqlite3
import statistics
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT / "src"))
sys.path.insert(0, str(HERE))

import anchoring as anch  # noqa: E402
import receipts  # noqa: E402
import s25_proof_body_similarity as body_mod  # noqa: E402

RESTART_DB = ROOT / "data/restart.sqlite"
CPRIME_DB = ROOT / "data/cprime.sqlite"
RUNS_DB = ROOT / "data/runs.sqlite"
PAIRING = ROOT / "audit/cprime_pairing.csv"
OUT = ROOT / "audit/restart_anchoring.json"
BASE_URL = "http://127.0.0.1:8080"

# arm -> (reference text for "own", reference text for "donor" or None)
ARMS = ["A", "C", "Cp", "AR", "CR", "CpR"]


def main() -> int:
    receipts.force_utf8()
    tok = anch.ServerTokenizer(BASE_URL)
    live, detail = tok.probe()
    if not live:
        print(f"tokenizer unavailable ({detail}); start the server and re-run")
        return 2
    print(f"[1/4] tokenizer: {detail}")

    roots_meta = {}
    for line in (ROOT / "data/roots.jsonl").open(encoding="utf-8"):
        r = json.loads(line)
        roots_meta[r["root_id"]] = r
    prior = {d.name: (d / "raw_completion.txt").read_text(encoding="utf-8")
             for d in sorted((ROOT / "artifacts/roots").iterdir()) if d.is_dir()}
    donor = {r["root_id"]: r["donor_root_id"]
             for r in csv.DictReader(PAIRING.open(encoding="utf-8"))}

    # ---- completions for all six arms over the block-1 roots
    comp: dict = {}
    con = sqlite3.connect(f"file:{RUNS_DB}?mode=ro", uri=True)
    for root, arm, c in con.execute(
            "SELECT root_id, arm, completion FROM branches WHERE cohort='primary_eval' "
            "AND status='done' AND arm IN ('A','C')"):
        comp.setdefault(arm, {})[root] = c or ""
    con.close()
    con = sqlite3.connect(f"file:{CPRIME_DB}?mode=ro", uri=True)
    for root, c in con.execute(
            "SELECT root_id, completion FROM branches WHERE cohort='eval_cprime' "
            "AND status='done'"):
        comp.setdefault("Cp", {})[root] = c or ""
    con.close()
    con = sqlite3.connect(f"file:{RESTART_DB}?mode=ro", uri=True)
    for root, arm, c in con.execute(
            "SELECT root_id, arm, completion FROM branches WHERE status='done'"):
        comp.setdefault(arm, {})[root] = c or ""
    con.close()

    roots = sorted(set.intersection(*(set(comp[a]) for a in ARMS)))
    print(f"[2/4] {len(roots)} roots across {len(ARMS)} arms")

    # ---- tokenize the reference texts once
    print("[3/4] tokenizing prior attempts and completions")
    prior_tok = {r: tok.tokens(prior[r]) for r in roots}
    prior_body_tok = {}
    for r in roots:
        b, _ = body_mod.proof_body(prior[r], roots_meta[r]["theorem_text"])
        prior_body_tok[r] = tok.tokens(b) if b else []

    results: dict = {"n": len(roots), "confirmatory": False,
                     "registration": "exploratory; spec/RESTART_SPEC.md section 0",
                     "arms": {}}
    band = json.loads((ROOT / "audit/receipts/s04.json").read_text(
        encoding="utf-8"))["stats"]
    results["null_band"] = {k: band[k] for k in band if k.startswith("null_band")}

    print("\n[4/4] similarity (descriptive; no test)")
    print(f"      null band (unrelated roots): p50 {band['null_band_p50']:.3f}, "
          f"p95 {band['null_band_p95']:.3f}, max {band['null_band_max']:.3f}\n")
    print(f"      {'arm':5} {'S(own)':>8} {'S_body(own)':>12} {'S(donor)':>10} "
          f"{'S_body(donor)':>14}   reference shown")
    for arm in ARMS:
        s_own, sb_own, s_don, sb_don = [], [], [], []
        for r in roots:
            t = tok.tokens(comp[arm][r])
            b, _ = body_mod.proof_body(comp[arm][r], roots_meta[r]["theorem_text"])
            tb = tok.tokens(b) if b else []
            s_own.append(anch.similarity(t, prior_tok[r]))
            sb_own.append(anch.similarity(tb, prior_body_tok[r]) if tb else 0.0)
            d = donor.get(r)
            if d and d in prior_tok:
                s_don.append(anch.similarity(t, prior_tok[d]))
                bd, _ = body_mod.proof_body(prior[d], roots_meta[d]["theorem_text"])
                sb_don.append(anch.similarity(tb, tok.tokens(bd)) if tb and bd else 0.0)
        shown = {"A": "nothing", "C": "own prior", "Cp": "donor prior",
                 "AR": "nothing", "CR": "own prior", "CpR": "donor prior"}[arm]
        rec = {"mean_S_own": round(statistics.mean(s_own), 4),
               "mean_S_body_own": round(statistics.mean(sb_own), 4),
               "mean_S_donor": round(statistics.mean(s_don), 4) if s_don else None,
               "mean_S_body_donor": round(statistics.mean(sb_don), 4) if sb_don else None,
               "reference_shown": shown, "n": len(roots)}
        results["arms"][arm] = rec
        print(f"      {arm:5} {rec['mean_S_own']:8.4f} {rec['mean_S_body_own']:12.4f} "
              f"{(rec['mean_S_donor'] if rec['mean_S_donor'] is not None else float('nan')):10.4f} "
              f"{(rec['mean_S_body_donor'] if rec['mean_S_body_donor'] is not None else float('nan')):14.4f}"
              f"   {shown}")

    a = results["arms"]
    print("\n      restart permission vs commit, on what the model actually reproduced:")
    for orig, rst, what in (("C", "CR", "own prior"), ("Cp", "CpR", "donor prior"),
                            ("A", "AR", "nothing shown")):
        d_s = a[rst]["mean_S_own"] - a[orig]["mean_S_own"]
        d_b = a[rst]["mean_S_body_own"] - a[orig]["mean_S_body_own"]
        print(f"        {rst:4} - {orig:3}  dS {d_s:+.4f}   dS_body {d_b:+.4f}   ({what})")
        results.setdefault("restart_deltas", {})[f"{rst}-{orig}"] = {
            "delta_S_own": round(d_s, 4), "delta_S_body_own": round(d_b, 4)}

    OUT.write_text(json.dumps(results, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"\nwrote {OUT.relative_to(ROOT).as_posix()}")
    print("Descriptive and exploratory. No test, no family, no equivalence claim.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
