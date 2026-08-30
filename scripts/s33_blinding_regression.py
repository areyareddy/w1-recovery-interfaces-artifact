"""Step s33 -- regression test: a blinded cohort must not leak an outcome into a log.

    python scripts\\s33_blinding_regression.py

WHY THIS EXISTS. spec/ALLOCATION_SPEC.md section 7 forbids opening an eval cohort's
outcomes before the analysis that reads them is frozen. scripts/overnight_status.py was
written to honour that and queries only status. But scripts/overnight_queue.py redirects
scripts/s12_run.py's stdout into audit/overnight/<job>.log, and s12 was not blinded: it
printed an OK marker and outcome_state per branch, an outcomes dict, a per-arm outcome
table, and "arm X: verified v/n". On 2026-08-29 that wrote the allocation eval outcomes
to a plaintext log at generation time. The guard was on the front door; the queue drove
around the back.

The fix is s12's --blind flag and overnight_queue's BLIND_COHORTS set. This script is what
stops the fix from silently rotting: it checks the contract three ways and fails loudly.

    1. SCANNER SELF-TEST. The leak detector is shown to flag a real unblinded s12 sample
       and to pass a real blinded one. A detector nobody has tested against a known
       positive is not evidence.
    2. CONTRACT. s12 still exposes --blind, and overnight_queue still passes it for every
       cohort in BLIND_COHORTS. Either half alone is useless.
    3. LOG SCAN. Every blinded cohort's log is scanned. A new leak fails the run. The two
       logs contaminated before the fix are quarantined by name, with a reason, and are
       reported as a known breach rather than being quietly tolerated.

This script never prints the offending content -- only file names, line numbers and
counts. A regression test for a blinding rule must not itself unblind anything.

Exit codes: 0 all checks pass (known breaches reported), 1 a new leak or a broken
contract.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(HERE))

LOGDIR = ROOT / "audit/overnight"

# The three outcome_state values plus the word the per-arm summary uses. Any of these,
# as a whole word, in a blinded cohort's log is a leak.
OUTCOME_WORDS = re.compile(r"\b(verified|lean_failed|truncated)\b")

# The blinded build prints two lines that legitimately name what it is NOT showing.
ALLOW = "WITHHELD"

# Logs written before the fix. Quarantined, not excused: they are why this file exists.
QUARANTINE = {
    "alloc_split2_eval.log":
        "generated 2026-08-29 08:23-09:22Z by the unblinded queue; per-arm verified "
        "counts present. Voided section 7 for the router baseline, which is withdrawn.",
    "alloc_split3_eval.log":
        "generated 2026-08-29 09:22-10:18Z by the unblinded queue; same breach.",
}

# A real unblinded s12 sample and a real blinded one, for the self-test.
SAMPLE_LEAKY = """      [3/3] summary
       12/80 ( 15%) OK  aime_1984_p1|S2|d1                    verified      3120tok
      A  lean_failed      22
      arm A: verified 9/40 (22.5%)
      outcomes: {'lean_failed': 22, 'truncated': 7, 'verified': 11}
"""
SAMPLE_BLIND = """      [3/3] summary
       12/80 ( 15%) aime_1984_p1|S2|d1                    ETA 0h41m02s
      80 branch(es) done across 1 arm(s)
      per-arm outcome table and verified counts: WITHHELD (--blind)
      outcomes: WITHHELD (--blind)
"""


def scan(text: str) -> list[int]:
    """1-indexed line numbers that leak an outcome. Content is never returned."""
    return [i for i, line in enumerate(text.splitlines(), 1)
            if OUTCOME_WORDS.search(line) and ALLOW not in line]


def main() -> int:
    failures: list[str] = []

    # ---------------------------------------------------------- 1. scanner self-test
    print("[1/3] scanner self-test")
    leaky = scan(SAMPLE_LEAKY)
    blind = scan(SAMPLE_BLIND)
    if len(leaky) != 4:
        failures.append(f"scanner missed a known leak: flagged {len(leaky)}/4 lines")
        print(f"      FAIL  known-bad sample: flagged {len(leaky)} of 4 lines")
    else:
        print(f"      ok    known-bad sample: all 4 leaking lines flagged")
    if blind:
        failures.append(f"scanner false-positives on blinded output: lines {blind}")
        print(f"      FAIL  known-good sample: {len(blind)} false positive(s)")
    else:
        print("      ok    known-good sample: clean, WITHHELD lines not flagged")

    # ------------------------------------------------------------------ 2. contract
    print("\n[2/3] contract between s12 and the queue")
    s12 = (HERE / "s12_run.py").read_text(encoding="utf-8")
    if '"--blind"' in s12 and "args.blind" in s12:
        print("      ok    s12_run.py exposes --blind and branches on it")
    else:
        failures.append("s12_run.py no longer implements --blind")
        print("      FAIL  s12_run.py does not implement --blind")

    q = (HERE / "overnight_queue.py").read_text(encoding="utf-8")
    if "BLIND_COHORTS" in q and 'cmd += ["--blind"]' in q:
        print("      ok    overnight_queue.py passes --blind for BLIND_COHORTS")
    else:
        failures.append("overnight_queue.py no longer passes --blind")
        print("      FAIL  overnight_queue.py does not pass --blind")

    try:
        import overnight_queue as oq  # noqa: E402
        blind_cohorts = set(oq.BLIND_COHORTS)
        job_cohorts = {j[3] for j in oq.JOBS}
        print(f"      ok    BLIND_COHORTS = {sorted(blind_cohorts) or 'EMPTY'}")
        stale = blind_cohorts - job_cohorts
        if stale:
            print(f"      note  listed but not in JOBS (harmless): {sorted(stale)}")
    except Exception as exc:  # noqa: BLE001
        blind_cohorts = set(QUARANTINE and {"alloc_split2_eval", "alloc_split3_eval"})
        failures.append(f"could not import overnight_queue: {exc}")
        print(f"      FAIL  could not import overnight_queue: {exc}")

    # ------------------------------------------------------------------ 3. log scan
    print("\n[3/3] blinded-cohort log scan")
    if not LOGDIR.exists():
        print(f"      no {LOGDIR.relative_to(ROOT).as_posix()}/ -- nothing to scan")
    else:
        scanned = 0
        for cohort in sorted(blind_cohorts):
            log = LOGDIR / f"{cohort}.log"
            if not log.exists():
                print(f"      --    {cohort}.log absent")
                continue
            scanned += 1
            hits = scan(log.read_text(encoding="utf-8", errors="replace"))
            if not hits:
                print(f"      ok    {cohort}.log clean")
            elif log.name in QUARANTINE:
                print(f"      KNOWN BREACH  {log.name}: {len(hits)} leaking line(s), "
                      f"first at line {hits[0]}")
                print(f"                    {QUARANTINE[log.name]}")
            else:
                failures.append(
                    f"NEW LEAK in {log.name}: {len(hits)} line(s), first at {hits[0]}")
                print(f"      FAIL  {log.name}: {len(hits)} leaking line(s), "
                      f"first at line {hits[0]} -- NOT quarantined")
        if not scanned:
            print("      no blinded-cohort logs on disk yet")

    # --------------------------------------------------------------------- verdict
    print("\n" + "=" * 74)
    if failures:
        print(f"FAIL -- {len(failures)} problem(s):")
        for f in failures:
            print(f"  - {f}")
        return 1
    known = [n for n in QUARANTINE if (LOGDIR / n).exists()]
    print("PASS -- blinding contract holds; no new outcome leakage.")
    if known:
        print(f"        {len(known)} historical log(s) quarantined as a known breach; "
              "see spec/ALLOCATION_SPEC.md section 6.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
