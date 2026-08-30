"""Step s21 -- build arm C' (mismatched prior attempt). CPU only. Does NOT touch runs.sqlite.

WHY THIS ARM EXISTS. Arm C shows the prior attempt and verification drops. Three accounts
survive the current design and it cannot separate them:

  (a) commitment to the SPECIFIC rejected trajectory
  (b) generic long-context degradation
  (c) an off-distribution prompt format for a model trained on a native correction schema

C' holds (b) and (c) fixed and removes only (a): identical wrapper, identical theorem,
identical seed, a prior attempt of near-identical length -- but from a DIFFERENT root.

    C  = WRAPPER(own failed attempt)     + OFFICIAL(theorem)
    C' = WRAPPER(another root's attempt) + OFFICIAL(theorem)

    C' - A   isolates generic long-context / non-native-format cost
    C  - C'  isolates commitment to the specific rejected trajectory

DONOR ASSIGNMENT is deterministic, STRATIFIED, and length-matched within stratum.

A global length sort (the first version of this script) matched lengths well but let 18 of
40 donors cross the coarse failure groups and 2 cross the incomplete/complete boundary. The
second of those is the one that is visible in the stimulus: a truncated attempt ends
mid-proof with no closing structure, a complete-but-wrong attempt does not, so a recipient
whose own attempt was truncated would have been shown a donor of a different surface kind.
That weakens exactly the comparison C' exists to support.

The rule is therefore: partition the 40 eval roots into INCOMPLETE (truncated) and
COMPLETE, sort each stratum by the token length of its own prior attempt, and swap adjacent
pairs inside the stratum. Odd strata rotate one triple, and the triple's position is chosen
to minimise (max delta, sum delta) over the admissible positions rather than being fixed at
the end.

The stratum is binary rather than the full three-way coarse_failure_group because exactly
two donor properties reach the model through the prompt:

    1. whether the donor is a finished proof or a truncated fragment
    2. how much context it adds

Both are matched by this rule. The localized/diffuse distinction is a property of the
original compiler diagnosis, and the C' wrapper carries no error text, so it is invisible in
the stimulus. Stratifying on it as well would buy nothing the model can see and would cost a
4520-token (46%) mismatch on one pair, because localized_complete holds only 10 roots
spanning 1852..9899 and its longest root would have no acceptable partner inside the group.
That trade weakens C' as a long-context control, which is the arm's whole purpose.

Under the binary rule the incomplete stratum matches exactly -- all 15 truncated attempts
are 12288 tokens -- and the complete stratum reaches a worst-case gap of 2001 tokens, which
is the smallest achievable worst case for any one-to-one derangement of those 25 lengths.
The 2001 is forced by the length distribution, not by the pairing rule. Median delta 87.

Localized/diffuse balance is reported in audit/cprime_pairing.csv and treated as a
DESCRIPTIVE SENSITIVITY ANALYSIS, not part of the primary C' estimand.

The assignment is reproducible from the sort alone -- there is no random assignment to
disclose or re-seed.

SEPARATE DATABASE, on purpose. runs.sqlite holds the pre-registered cohorts under a frozen
spec hash; C' is a disclosed POST-HOC addition and must be visibly separate. It also keeps
the timing replay's source fingerprint stable while that run is in flight.
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

import policy  # noqa: E402
import prompts  # noqa: E402
import receipts  # noqa: E402
import s08_init_db  # noqa: E402

RUNS_DB = ROOT / "data/runs.sqlite"
CPRIME_DB = ROOT / "data/cprime.sqlite"
CPRIME_PROMPTS = ROOT / "data/cprime_prompts.jsonl"
PAIRING_CSV = ROOT / "audit/cprime_pairing.csv"
COHORT = "eval_cprime"
ARM = "Cp"
LENGTH_TOLERANCE = 0.25   # relative delta above which a pair is flagged in the audit


def completion_class(rec: dict) -> str:
    """The one donor property that is visible in the C' stimulus.

    A truncated attempt ends mid-proof with no closing structure; a complete-but-wrong
    attempt does not. Everything finer in coarse_failure_group describes the compiler's
    diagnosis, which C' never shows the model.
    """
    return "incomplete" if rec["coarse_failure_group"] == "incomplete" else "complete"


def TOK(roots: dict, rid: str) -> int:
    return roots[rid]["raw_prior_completion_tokens"]


def derange_sorted(order, length):
    """Adjacent-swap derangement of a length-sorted list.

    Adjacent pairing minimises the total within-pair length difference on a sorted line.
    An odd list needs one 3-cycle; rather than fixing it at the end we place it at the
    position that minimises (max delta, sum delta), which is deterministic and strictly
    better than the fixed choice.
    """
    n = len(order)
    positions = [0] if n % 2 == 0 else list(range(0, n - 2, 2))
    best = None
    for k in positions:
        d, i = {}, 0
        while i < n:
            if n % 2 and i == k:
                a, b, c = order[i], order[i + 1], order[i + 2]
                d[a], d[b], d[c] = b, c, a
                i += 3
            else:
                a, b = order[i], order[i + 1]
                d[a], d[b] = b, a
                i += 2
        deltas = [abs(length(r) - length(d[r])) for r in d]
        key = (max(deltas), sum(deltas))
        if best is None or key < best[0]:
            best = (key, d)
    return best[1]


def main() -> int:
    receipts.force_utf8()

    print("[1/5] loading the evaluation roots")
    roots = {}
    for line in (ROOT / "data/roots.jsonl").open(encoding="utf-8"):
        r = json.loads(line)
        if r["split"] == "held_out":
            roots[r["root_id"]] = r
    assert len(roots) == 40, f"expected 40 eval roots, got {len(roots)}"

    # seeds come from the frozen store, read-only, so C-C' stays paired within root
    con = sqlite3.connect(f"file:{RUNS_DB}?mode=ro", uri=True)
    seeds = dict(con.execute(
        "SELECT root_id, seed FROM branches WHERE cohort='primary_eval' "
        "AND seed_block=1 AND arm='A'"))
    con.close()
    assert all(rid in seeds for rid in roots), "missing a block-1 seed"
    print(f"      {len(roots)} roots, seeds {min(seeds.values())}..{max(seeds.values())}")

    print("\n[2/5] stratified, length-matched donor assignment")
    print("      stratum = truncated fragment vs finished proof (the two donor properties")
    print("      that reach the model: surface form, and how much context it adds)")
    donor: dict[str, str] = {}
    for stratum in ("incomplete", "complete"):
        members = sorted(
            (rid for rid in roots if completion_class(roots[rid]) == stratum),
            key=lambda rid: (roots[rid]["raw_prior_completion_tokens"], rid))
        assert len(members) >= 3, f"{stratum}: too small to derange ({len(members)})"
        part = derange_sorted(members, lambda rid: TOK(roots, rid))
        donor.update(part)
        d = sorted(abs(TOK(roots, r) - TOK(roots, part[r])) for r in part)
        lens = [TOK(roots, r) for r in members]
        print(f"      {stratum:20} n={len(members):2d}  lengths {min(lens):5d}..{max(lens):5d}"
              f"  |delta| median {statistics.median(d):5.0f}  max {d[-1]:5d}")

    assert all(donor[r] != r for r in donor), "a root was assigned its own attempt"
    assert len(set(donor.values())) == len(donor), "donor assignment is not a bijection"
    assert set(donor) == set(roots), "not every root received a donor"
    assert all(completion_class(roots[r]) == completion_class(roots[donor[r]])
               for r in donor), "a donor crossed the incomplete/complete boundary"

    deltas = sorted(abs(TOK(roots, r) - TOK(roots, donor[r])) for r in donor)
    own = sorted(TOK(roots, r) for r in roots)
    n_fine_cross = sum(1 for r in donor if roots[r]["fine_failure_class"]
                       != roots[donor[r]]["fine_failure_class"])
    n_coarse_cross = sum(1 for r in donor if roots[r]["coarse_failure_group"]
                         != roots[donor[r]]["coarse_failure_group"])
    print("      " + " " * 20 + " ----")
    print(f"      own-attempt lengths      : {own[0]}..{own[-1]} tokens, "
          f"median {statistics.median(own):.0f}")
    print(f"      |donor - own| token delta: median {statistics.median(deltas):.0f}, "
          f"p90 {deltas[int(0.9 * len(deltas))]}, max {deltas[-1]}")
    print("      donors crossing incomplete/complete: 0/40 by construction (asserted)")
    print(f"      donors crossing localized/diffuse  : {n_coarse_cross}/40 "
          "(descriptive sensitivity; not visible in the stimulus)")
    print(f"      donors crossing a fine class       : {n_fine_cross}/40 "
          "(descriptive; no error text is shown in C')")

    print("\n[3/5] building prompts and gating them")
    records, rows = [], []
    wrapper_sha = receipts.sha_text(prompts.NEUTRAL_PRIOR_ATTEMPT_WRAPPER)
    for rid in sorted(roots):
        rec, d = roots[rid], donor[rid]
        theorem = rec["theorem_text"]
        own_raw = (ROOT / "artifacts/roots" / rid / "raw_completion.txt").read_text(
            encoding="utf-8")
        donor_raw = (ROOT / "artifacts/roots" / d / "raw_completion.txt").read_text(
            encoding="utf-8")

        base = policy.official_prompt(theorem)
        prompt_c = prompts.wrapper_block(own_raw) + base
        prompt_cp = prompts.wrapper_block(donor_raw) + base

        # --- gate: C' differs from C ONLY in the wrapper payload -------------------
        assert prompt_cp.endswith(base), f"{rid}: C' does not end with OFFICIAL(theorem)"
        assert prompt_c.endswith(base), f"{rid}: C does not end with OFFICIAL(theorem)"
        head = prompts.NEUTRAL_PRIOR_ATTEMPT_WRAPPER.split("{prior_attempt}")[0]
        tail = prompts.NEUTRAL_PRIOR_ATTEMPT_WRAPPER.split("{prior_attempt}")[1]
        assert prompt_cp.startswith(head), f"{rid}: wrapper header differs"
        assert prompt_c.startswith(head), f"{rid}: wrapper header differs in C"
        assert donor_raw in prompt_cp, f"{rid}: donor attempt missing from C'"
        assert own_raw not in prompt_cp, \
            f"{rid}: the root's OWN attempt leaked into its C' prompt"
        assert prompt_cp == head + donor_raw + tail + base, \
            f"{rid}: C' is not exactly head+donor+tail+base"

        messages = [{"role": "user", "content": prompt_cp}]
        records.append({
            "branch_key": f"{rid}|{ARM}",
            "root_id": rid, "split": "held_out", "arm": ARM, "cohort": COHORT,
            "seed": seeds[rid],
            "donor_root_id": d,
            "own_prior_tokens": rec["raw_prior_completion_tokens"],
            "donor_prior_tokens": roots[d]["raw_prior_completion_tokens"],
            "messages": messages,
            "conversation_turns": 1,
            "payload_chars": len(prompt_cp),
            "payload_sha256": receipts.sha_text(
                json.dumps(messages, ensure_ascii=False, sort_keys=True)),
            "wrapper_sha256": wrapper_sha,
            "base_prompt_sha256": receipts.sha_text(base),
            "donor_attempt_sha256": receipts.sha_text(donor_raw),
            "own_attempt_sha256": receipts.sha_text(own_raw),
            "theorem_text": theorem,
            "fine_failure_class": rec["fine_failure_class"],
            "coarse_failure_group": rec["coarse_failure_group"],
            "donor_coarse_failure_group": roots[d]["coarse_failure_group"],
            "donor_fine_failure_class": roots[d]["fine_failure_class"],
            "abs_token_delta": abs(rec["raw_prior_completion_tokens"]
                                   - roots[d]["raw_prior_completion_tokens"]),
            "rel_token_delta": round(
                abs(rec["raw_prior_completion_tokens"]
                    - roots[d]["raw_prior_completion_tokens"])
                / max(rec["raw_prior_completion_tokens"],
                      roots[d]["raw_prior_completion_tokens"]), 4),
            "completion_class": completion_class(rec),
            "donor_completion_class": completion_class(roots[d]),
            "same_completion_class": int(completion_class(roots[d])
                                         == completion_class(rec)),
            "same_coarse_group": int(roots[d]["coarse_failure_group"]
                                     == rec["coarse_failure_group"]),
            "same_fine_class": int(roots[d]["fine_failure_class"]
                                   == rec["fine_failure_class"]),
            "length_match_flagged": int(
                abs(rec["raw_prior_completion_tokens"]
                    - roots[d]["raw_prior_completion_tokens"])
                / max(rec["raw_prior_completion_tokens"],
                      roots[d]["raw_prior_completion_tokens"]) > LENGTH_TOLERANCE),
        })
        rows.append({k: v for k, v in records[-1].items()
                     if k not in ("messages", "theorem_text")})
    print(f"      {len(records)} C' prompts built; all gates pass")

    print("\n[4/5] writing prompts and pairing audit")
    with CPRIME_PROMPTS.open("w", encoding="utf-8", newline="\n") as fh:
        for r in records:
            fh.write(json.dumps(r, ensure_ascii=False, sort_keys=True) + "\n")
    with PAIRING_CSV.open("w", encoding="utf-8", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)

    print("\n[5/5] staging the job store (separate database)")
    # A previous build may have staged 40 rows under the OLD pairing. INSERT OR IGNORE
    # keys on branch_key, which is unchanged, so it would silently keep the stale
    # payload_sha256 and the store would no longer match cprime_prompts.jsonl. Rebuild
    # from empty instead -- but only if nothing has been generated yet.
    if CPRIME_DB.exists():
        chk = sqlite3.connect(f"file:{CPRIME_DB}?mode=ro", uri=True)
        done = chk.execute(
            "SELECT count(*) FROM branches WHERE status != 'pending'").fetchone()[0]
        chk.close()
        assert done == 0, (
            f"{CPRIME_DB.name} already holds {done} non-pending branches. Refusing to "
            "rebuild: that would discard generated data. Move it aside deliberately.")
        stamp = __import__("time").strftime("%Y%m%dT%H%M%S")
        moved = ROOT / "Backup" / f"cprime.sqlite.{stamp}.prerebuild"
        CPRIME_DB.replace(moved)
        for suffix in ("-wal", "-shm"):
            side = CPRIME_DB.with_name(CPRIME_DB.name + suffix)
            if side.exists():
                side.unlink()
        print(f"      previous empty store moved to Backup/{moved.name}")

    con = sqlite3.connect(CPRIME_DB)
    con.execute("PRAGMA journal_mode=WAL")
    con.executescript(s08_init_db.SCHEMA)
    for r in records:
        con.execute(
            "INSERT OR IGNORE INTO branches (branch_key, root_id, split, arm, cohort, "
            "seed_block, seed, payload_sha256, conversation_turns, fine_failure_class, "
            "coarse_failure_group) VALUES (?,?,?,?,?,1,?,?,?,?,?)",
            (r["branch_key"], r["root_id"], r["split"], r["arm"], COHORT, r["seed"],
             r["payload_sha256"], r["conversation_turns"], r["fine_failure_class"],
             r["coarse_failure_group"]))
    con.commit()
    n = con.execute("SELECT count(*) FROM branches").fetchone()[0]
    con.close()
    assert n == 40, f"expected 40 staged branches, got {n}"

    print(f"      {CPRIME_DB.relative_to(ROOT).as_posix()}: {n} branches pending")
    print(f"      {CPRIME_PROMPTS.relative_to(ROOT).as_posix()}")
    print(f"      {PAIRING_CSV.relative_to(ROOT).as_posix()}")

    # This digest covers the CANONICAL DONOR MAP -- the sorted "root->donor" lines --
    # and NOT the bytes of audit/cprime_pairing.csv. The CSV carries descriptive columns
    # whose formatting may change without the pairing changing, so hashing it would make
    # the frozen identity brittle. An auditor running sha256sum on the CSV therefore gets
    # a different value; both are printed so neither is mistaken for the other.
    pairing_sha = receipts.sha_text(
        "\n".join(f"{r}->{donor[r]}" for r in sorted(donor)))
    prompts_sha = receipts.sha_file(CPRIME_PROMPTS)
    pairing_csv_sha = receipts.sha_file(PAIRING_CSV)
    print(f"\n      canonical donor-map sha256 : {pairing_sha}")
    print(f"        (sorted 'root->donor' lines; NOT the CSV file digest)")
    print(f"      prompts sha256             : {prompts_sha}")
    print(f"      cprime_pairing.csv sha256  : {pairing_csv_sha}")
    print(f"        (descriptive audit file; not part of the frozen identity)")
    print("      Record both in docs/CPRIME_SPEC.md before generating.")
    print("\n  runs.sqlite was NOT modified -- its content fingerprint is unchanged, so")
    print("  the timing replay can still resume against the same run identity.")
    print("\n  To generate (AFTER the replay finishes -- one GPU slot):")
    print("     python scripts\\s12_run.py --db data/cprime.sqlite \\")
    print("            --prompts data/cprime_prompts.jsonl --cohort eval_cprime")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
