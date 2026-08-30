"""Step s07 -- how long the run actually takes, and what dominates.

Not a gate. It exists because the submission deadline is a hard constraint and the
answer to "can we run 181 branches tonight" has to come from measurements, not hope.

Inputs, all measured rather than assumed:
  decode / prefill rates      audit/determinism.json      (this GPU, this config)
  prefill tokens per branch   audit/context_capacity.csv  (all 376, exact)
  completion-token prior      CoLM cascade stage-two completions
  verifier latency prior      CoLM lean_latency_seconds

The completion-token prior comes from CoLM's cascade retries rather than from its stage
one, because a retry on an already-failed theorem is the closest available analogue to
what these arms do. It is still a prior from a different arm set -- treat the projection
as an order-of-magnitude planning number, not a promise.

The thing this step is really for is the split between GPU time and verifier time. The
Lean REPL runs at one worker with a 180 s timeout, and a timeout costs the full 180 s
while producing almost no tokens. If verification dominates, the fix is more REPL workers
rather than anything to do with the model, and that is worth knowing BEFORE the run
rather than at 3am.
"""

from __future__ import annotations

import csv
import json
import statistics
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT / "src"))
sys.path.insert(0, str(HERE))

import pipeline  # noqa: E402
import receipts  # noqa: E402

STEP = pipeline.BY_ID["s07"]
COLM = ROOT.parent / "CoLM_Jul2026_MoSpe_Navi"
CASCADE = COLM / "runs/epp_confirmatory_202/evaluation/cascade_attempts.jsonl"
MAX_TOKENS = 12288
LEAN_TIMEOUT = 180


def read_jsonl(path: Path) -> list[dict]:
    with path.open(encoding="utf-8") as fh:
        return [json.loads(line) for line in fh if line.strip()]


def pct(xs: list[float], p: float) -> float:
    xs = sorted(xs)
    return xs[min(len(xs) - 1, int(p * len(xs)))]


def fmt_hms(seconds: float) -> str:
    h, rem = divmod(int(seconds), 3600)
    m, s = divmod(rem, 60)
    return f"{h:d}h{m:02d}m{s:02d}s"


def main() -> int:
    receipts.force_utf8()

    print("[1/4] measured rates")
    det = json.loads((ROOT / "audit/determinism.json").read_text(encoding="utf-8"))
    reps = [c for c in det["checks"] if c["check"] == "repeat_same_seed"]
    decode_tps = statistics.median(c["decode_tok_per_s"] for c in reps)
    prefill_tps = statistics.median(c["prefill_tok_per_s"] for c in reps)
    print(f"      decode  {decode_tps:8.1f} tok/s")
    print(f"      prefill {prefill_tps:8.1f} tok/s   ({prefill_tps / decode_tps:.0f}x decode)")

    print("\n[2/4] priors from the CoLM cascade")
    cascade = read_jsonl(CASCADE)
    comp = [r["response"]["usage"]["completion_tokens"] for r in cascade
            if r.get("response", {}).get("usage")]
    lean = [r["lean_latency_seconds"] for r in cascade
            if r.get("lean_latency_seconds") is not None]
    ran_lean = sum(1 for r in cascade if r.get("lean_latency_seconds") is not None)
    print(f"      completion tokens over {len(comp)} retries: "
          f"p50 {pct(comp, .5):.0f}  mean {statistics.mean(comp):.0f}  "
          f"p90 {pct(comp, .9):.0f}  max {max(comp)}")
    print(f"      lean latency over {len(lean)} runs:        "
          f"p50 {pct(lean, .5):.1f}s  mean {statistics.mean(lean):.1f}s  "
          f"p90 {pct(lean, .9):.1f}s  max {max(lean):.1f}s")
    print(f"      reached the verifier: {ran_lean}/{len(cascade)} "
          f"({100 * ran_lean / len(cascade):.0f}%)")

    print("\n[3/4] prefill per branch")
    cap = list(csv.DictReader((ROOT / "audit/context_capacity.csv").open(encoding="utf-8")))
    prefill_by_key = {r["branch_key"]: int(r["prompt_tokens"]) for r in cap}
    cohorts = {
        "primary_eval_181": [r for r in cap if r["split"] == "held_out"],
        "full_pool_353": [r for r in cap
                          if r["arm"] in "ABCD" or r["split"] == "held_out"],
    }
    for name, rows in cohorts.items():
        print(f"      {name:18} {len(rows):3d} branches, "
              f"{sum(prefill_by_key[r['branch_key']] for r in rows):,} prefill tokens")

    print("\n[4/4] projection")
    scenarios = {
        "p50_completion": pct(comp, .50),
        "mean_completion": statistics.mean(comp),
        "p90_completion": pct(comp, .90),
        "worst_all_capped": MAX_TOKENS,
    }
    lean_rate = ran_lean / len(cascade)
    lean_scen = {
        "p50_lean": pct(lean, .50),
        "mean_lean": statistics.mean(lean),
        "p90_lean": pct(lean, .90),
        "worst_all_timeout": LEAN_TIMEOUT,
    }

    out_rows = []
    for cname, rows in cohorts.items():
        n = len(rows)
        prefill_tokens = sum(prefill_by_key[r["branch_key"]] for r in rows)
        prefill_s = prefill_tokens / prefill_tps
        for sname, ctoks in scenarios.items():
            decode_s = n * ctoks / decode_tps
            for lname, lsec in lean_scen.items():
                # a capped (truncated) generation never reaches the verifier
                reach = 1.0 if sname != "worst_all_capped" else 0.0
                verify_s = n * lean_rate * lsec if sname != "worst_all_capped" else 0.0
                total = prefill_s + decode_s + verify_s
                out_rows.append({
                    "cohort": cname,
                    "branches": n,
                    "completion_scenario": sname,
                    "completion_tokens_each": round(ctoks),
                    "lean_scenario": lname,
                    "lean_seconds_each": round(lsec, 1),
                    "verifier_reach_rate": round(lean_rate if reach else 0.0, 3),
                    "prefill_seconds": round(prefill_s, 1),
                    "decode_seconds": round(decode_s, 1),
                    "verifier_seconds": round(verify_s, 1),
                    "total_seconds": round(total, 1),
                    "total_hms": fmt_hms(total),
                    "decode_share": round(decode_s / total, 3) if total else 0,
                    "verifier_share": round(verify_s / total, 3) if total else 0,
                })

    with (ROOT / "audit/runtime_projection.csv").open("w", encoding="utf-8", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(out_rows[0].keys()))
        w.writeheader()
        w.writerows(out_rows)

    print(f"      {'cohort':18} {'completion':16} {'lean':18} {'total':>10}  "
          f"{'decode':>7} {'verify':>7}")
    for r in out_rows:
        if r["lean_scenario"] in ("mean_lean", "p90_lean") or \
                r["completion_scenario"] == "worst_all_capped":
            print(f"      {r['cohort']:18} {r['completion_scenario']:16} "
                  f"{r['lean_scenario']:18} {r['total_hms']:>10}  "
                  f"{r['decode_share']:>7.0%} {r['verifier_share']:>7.0%}")

    def pick(cohort, cs, ls):
        return next(r for r in out_rows if r["cohort"] == cohort
                    and r["completion_scenario"] == cs and r["lean_scenario"] == ls)

    central = pick("primary_eval_181", "mean_completion", "mean_lean")
    pessim = pick("primary_eval_181", "p90_completion", "p90_lean")
    full = pick("full_pool_353", "mean_completion", "mean_lean")

    print(f"\n      primary 181, central    {central['total_hms']}  "
          f"(decode {fmt_hms(central['decode_seconds'])}, "
          f"verify {fmt_hms(central['verifier_seconds'])})")
    print(f"      primary 181, p90/p90    {pessim['total_hms']}")
    print(f"      full pool 353, central  {full['total_hms']}")

    stats = {
        "decode_tokens_per_second": round(decode_tps, 1),
        "prefill_tokens_per_second": round(prefill_tps, 1),
        "prefill_to_decode_ratio": round(prefill_tps / decode_tps, 1),
        "completion_token_prior": {"p50": round(pct(comp, .5)),
                                   "mean": round(statistics.mean(comp)),
                                   "p90": round(pct(comp, .9)),
                                   "n": len(comp)},
        "lean_latency_prior_seconds": {"p50": round(pct(lean, .5), 1),
                                       "mean": round(statistics.mean(lean), 1),
                                       "p90": round(pct(lean, .9), 1),
                                       "n": len(lean)},
        "verifier_reach_rate": round(lean_rate, 3),
        "primary_181_central_hms": central["total_hms"],
        "primary_181_p90_hms": pessim["total_hms"],
        "full_pool_353_central_hms": full["total_hms"],
        "primary_181_decode_share": central["decode_share"],
        "primary_181_verifier_share": central["verifier_share"],
        "lean_workers_assumed": 1,
    }
    receipts.write(STEP["id"], STEP["title"], STEP["inputs"], STEP["outputs"], stats)
    print("\n  s07 done.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
