"""Step s14 -- W1 co-primary A: the prior-attempt textual anchoring proxy.

    S(branch, root) = 1 - lev(model_tokens(branch), model_tokens(root))
                          / max(len_branch, len_root)
    T0 = mean[ S(C,root) - S(A,root) ]
    T1 = mean[ S(D,root) - S(B,root) ]

Computed against the frozen definition in src/anchoring.py and the null band frozen at
s04 -- the distribution of S between prior attempts of DIFFERENT roots, which is what
makes a T0 of 0.04 interpretable rather than just small.

Every contrast is PAIRED within root: S(C,root) and S(A,root) come from the same theorem
and the same seed, so the difference is not contaminated by which theorems are easy.

INTERPRETATION RULE, from v7 `02` Sec.6 and non-negotiable:
positive T0/T1 evidences textual retention; near-zero does NOT prove the model ignored
the prior attempt. A model can read prior context and rewrite completely. Report this as
"prior-attempt textual anchoring", never as "artifact use".
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

import anchoring  # noqa: E402
import receipts  # noqa: E402

DB = ROOT / "data/runs.sqlite"
BASE_URL = "http://127.0.0.1:8080"
OUT = ROOT / "audit/anchoring_results.csv"


def main() -> int:
    receipts.force_utf8()
    tok = anchoring.ServerTokenizer(BASE_URL)
    live, detail = tok.probe()
    if not live:
        print(f"server unavailable: {detail}")
        return 2
    print(f"[1/4] {detail}")

    spec_sha = (ROOT / "spec/frozen_spec.sha256").read_text(encoding="utf-8").split()[0]
    band = json.loads((ROOT / "audit/receipts/s04.json").read_text(encoding="utf-8"))["stats"]
    print(f"      spec {spec_sha[:16]}  null band p50={band['null_band_p50']} "
          f"p95={band['null_band_p95']}")

    print("\n[2/4] tokenizing the 83 prior attempts")
    prior: dict[str, list[int]] = {}
    for d in sorted((ROOT / "artifacts/roots").iterdir()):
        if d.is_dir():
            prior[d.name] = tok.tokens((d / "raw_completion.txt").read_text(encoding="utf-8"))
    print(f"      {len(prior)} roots")

    print("\n[3/4] scoring every completed branch")
    con = sqlite3.connect(f"file:{DB}?mode=ro", uri=True)
    rows = list(con.execute(
        "SELECT branch_key, cohort, root_id, arm, seed_block, verified, outcome_state, "
        "completion FROM branches WHERE status='done' ORDER BY branch_key"))
    con.close()

    out: list[dict] = []
    for i, (key, cohort, rid, arm, block, verified, state, completion) in enumerate(rows, 1):
        s = anchoring.similarity(tok.tokens(completion or ""), prior[rid])
        out.append({"branch_key": key, "cohort": cohort, "root_id": rid, "arm": arm,
                    "seed_block": block, "verified": verified, "outcome_state": state,
                    "anchoring_S": round(s, 6)})
        if i % 100 == 0 or i == len(rows):
            print(f"      {i}/{len(rows)} ({100 * i // len(rows)}%)")

    with OUT.open("w", encoding="utf-8", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(out[0].keys()))
        w.writeheader()
        w.writerows(out)

    print("\n[4/4] contrasts")
    by = {}
    for r in out:
        by.setdefault((r["cohort"], r["root_id"]), {})[r["arm"]] = r["anchoring_S"]

    def contrast(cohort: str, x: str, y: str) -> dict | None:
        pairs = [(v[x], v[y]) for (co, _), v in by.items()
                 if co == cohort and x in v and y in v]
        if not pairs:
            return None
        diffs = [a - b for a, b in pairs]
        n = len(diffs)
        mean = statistics.mean(diffs)
        sd = statistics.stdev(diffs) if n > 1 else 0.0
        return {"cohort": cohort, "contrast": f"{x}-{y}", "n": n,
                "mean_S_x": round(statistics.mean(a for a, _ in pairs), 4),
                "mean_S_y": round(statistics.mean(b for _, b in pairs), 4),
                "mean_diff": round(mean, 4), "sd": round(sd, 4),
                "se": round(sd / (n ** 0.5), 4) if n > 1 else 0.0,
                "positive": sum(1 for d in diffs if d > 0), "n_pairs": n}

    results = []
    for cohort, label in (("primary_eval", "eval-40 block 1 (PRE-REGISTERED)"),
                          ("eval_block2", "eval-40 block 2 (replication)"),
                          ("full_pool_dev", "dev-43 (descriptive)")):
        print(f"\n  {label}")
        for x, y, name in (("C", "A", "T0"), ("D", "B", "T1"), ("E", "A", "E-A")):
            r = contrast(cohort, x, y)
            if not r:
                continue
            r["label"] = name
            results.append(r)
            print(f"    {name:4} {x}-{y}  n={r['n']:3d}  "
                  f"S({x})={r['mean_S_x']:.4f}  S({y})={r['mean_S_y']:.4f}  "
                  f"diff={r['mean_diff']:+.4f} (se {r['se']:.4f})  "
                  f"{r['positive']}/{r['n']} positive")

    print(f"\n  reference: unrelated-root null band p50 {band['null_band_p50']}, "
          f"p95 {band['null_band_p95']}, max {band['null_band_max']}")
    print("\n  Interpretation: positive = the prior attempt increases textual retention.")
    print("  Near-zero does NOT prove the model ignored it -- a model can read prior")
    print("  context and rewrite completely. Report as textual anchoring, not artifact use.")

    (ROOT / "audit/anchoring_contrasts.json").write_text(
        json.dumps({"spec_sha256": spec_sha, "null_band": {
            k: v for k, v in band.items() if k.startswith("null_band")},
            "contrasts": results}, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"\n  wrote {OUT.relative_to(ROOT).as_posix()} and audit/anchoring_contrasts.json")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
