"""Step 1 -- freeze the root set.

Emits data/roots.jsonl + artifacts/roots/<root_id>/ for the 83 stage-one baseline
failures, plus the Step-1 R2 and E-eligibility audits.

Frozen decisions encoded here (MASTER_CORRECTION.md overrides V7):

  * artifact  = the EXACT raw stage-one assistant completion, for every root,
                regardless of class. Never extracted Lean. (v6 00 Sec.2)
  * guidance  = R2 (error-conditioned, cascade_guidance()). No R1/R3 switching.
                Truncated roots take R1/nav2's list shortened to its first 3 entries.
  * E arm     = only where a real native <error> block exists. Placeholder
                feedback is never synthesised. (v6 01 Sec.6 / 05 Gate 3)

Everything read here is READ-ONLY from the CoLM tree.
"""
from __future__ import annotations

import csv
import hashlib
import importlib.util
import json
import sys
from collections import Counter
from pathlib import Path

HERE = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(HERE / "src"))

sys.path.insert(0, str(HERE / "scripts"))

import goedel_native  # noqa: E402
import pipeline  # noqa: E402
import policy  # noqa: E402
import receipts  # noqa: E402

COLM = HERE.parent / "CoLM_Jul2026_MoSpe_Navi"
RUN = COLM / "runs/epp_confirmatory_202"
MATCHED = COLM / "runs/epp_confirmatory_202_matched_seeds"
SUPPLEMENT = COLM / "anon_supplement_repo"
SUPPLEMENT_COMMIT = "ba676343d7a407bf71d6f2fb7e148bccbb38f473"
RENDERER_SOURCE = "src/mospe_navi.py::concrete_guidance_prompt"
R2_POLICY_ID = "R2_error_conditioned"

# W1/W2-DEFINED coarse grouping. NOT inherited from CoLM -- CoLM has no such
# mapping. Disclose as ours. Partitions the fine classes exactly.
COARSE = {
    "truncated": "incomplete",
    "linarith_failed": "localized_complete",
    "nlinarith_failed": "localized_complete",
    "unknown_identifier": "localized_complete",
    "simp_failed": "localized_complete",
    "type_mismatch": "localized_complete",
    "unsolved_goals": "diffuse_complete",
    "other": "diffuse_complete",
    "timeout": "diffuse_complete",
}


def sha(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


def sha_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write_exact(path: Path, text: str) -> None:
    """Write canonical UTF-8 bytes with no platform newline translation."""
    path.write_bytes(text.encode("utf-8"))
    assert sha_file(path) == sha(text), f"byte serialization drift: {path}"


def read_jsonl(path: Path) -> list[dict]:
    with path.open(encoding="utf-8") as fh:
        return [json.loads(line) for line in fh if line.strip()]


def load_mospe(path: Path, name: str):
    """Load a historical source snapshot read-only for byte-parity assertions."""
    sys.path.insert(0, str(COLM / "src"))
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def git_head(repo: Path) -> str:
    """Resolve a normal Git HEAD without invoking Git (keeps the freeze hermetic)."""
    head = (repo / ".git/HEAD").read_text(encoding="ascii").strip()
    if head.startswith("ref: "):
        ref = repo / ".git" / head[5:]
        assert ref.exists(), f"packed Git ref is unsupported for freeze: {head}"
        head = ref.read_text(encoding="ascii").strip()
    return head


STEP = pipeline.BY_ID["s00"]


def main() -> int:
    assert git_head(SUPPLEMENT) == SUPPLEMENT_COMMIT, "supplement commit drift"
    historical = load_mospe(COLM / "src/mospe_navi.py", "historical_mospe_navi")
    supplement = load_mospe(SUPPLEMENT / "src/mospe_navi.py", "supplement_mospe_navi")

    receipts.force_utf8()
    problems = {r["name"]: r for r in read_jsonl(COLM / "data/minif2f_test.jsonl")}
    split = json.loads((COLM / "data/scheduler_split.json").read_text(encoding="utf-8"))
    split_of = {pid: "held_out" for pid in split["held_out"]}
    split_of.update({pid: "dev" for pid in split["dev"]})

    attempts = read_jsonl(RUN / "evaluation/attempts.jsonl")
    roots = [r for r in attempts if r.get("arm") == "baseline" and not r.get("verified")]
    assert len(roots) == 83, f"expected 83 stage-one failures, got {len(roots)}"

    cascade = read_jsonl(RUN / "evaluation/cascade_attempts.jsonl")
    guid: dict[str, dict] = {}
    s1class: dict[str, str] = {}
    for row in cascade:
        guid.setdefault(row["problem_id"], {})[row["arm"]] = row["guidance"]
        s1class[row["problem_id"]] = row["stage1_error_class"]

    # byte-stability of the guidance we are about to freeze
    mguid: dict[str, dict] = {}
    for row in read_jsonl(MATCHED / "evaluation/cascade_attempts.jsonl"):
        mguid.setdefault(row["problem_id"], {})[row["arm"]] = row["guidance"]

    out_dir = HERE / "artifacts/roots"
    out_dir.mkdir(parents=True, exist_ok=True)
    (HERE / "data").mkdir(exist_ok=True)
    (HERE / "audit").mkdir(exist_ok=True)

    records: list[dict] = []
    elig: list[dict] = []
    r2_audit: list[dict] = []
    seen: set[str] = set()

    for rec in sorted(roots, key=lambda r: r["problem_id"]):
        pid = rec["problem_id"]
        assert pid not in seen, f"duplicate root {pid}"
        seen.add(pid)

        raw = rec["response"]["choices"][0]["message"]["content"]
        state = rec["outcome_state"]
        stdout = rec.get("lean_stdout")
        stderr = rec.get("lean_stderr")

        # authoritative class = the one R2 guidance was actually conditioned on
        fine = s1class[pid]
        recomputed = policy.error_class(state, stdout, stderr)
        assert fine == recomputed, (
            f"{pid}: recorded stage1_error_class {fine!r} != policy.error_class "
            f"{recomputed!r}; guidance conditioning would be mislabelled"
        )

        g2 = guid[pid]["R2"]
        assert g2 is not None, f"{pid}: R2 guidance is None"
        assert g2 == mguid[pid]["R2"], f"{pid}: R2 guidance not byte-stable across runs"

        r2_block = policy.guidance_block(g2)
        rendered = policy.concrete_guidance_prompt(prob_stmt := problems[pid]["formal_statement"], g2)
        assert rendered == r2_block + policy.official_prompt(prob_stmt)
        assert rendered == historical.concrete_guidance_prompt(prob_stmt, g2), (
            f"{pid}: local R2 renderer differs from historical working snapshot"
        )
        assert rendered == supplement.concrete_guidance_prompt(prob_stmt, g2), (
            f"{pid}: local R2 renderer differs from supplement commit"
        )

        errors = goedel_native.repl_errors(stdout)
        kind = goedel_native.feedback_kind(state, errors, stdout)
        native_ok = kind == "native_error"

        # extracted Lean is stored for SECONDARY analysis only; never the artifact
        proof_rel = rec.get("proof_path")
        extracted = None
        if proof_rel:
            p = COLM / str(proof_rel).replace("\\", "/")
            if p.exists():
                extracted = p.read_text(encoding="utf-8", errors="replace")

        d = out_dir / pid
        d.mkdir(exist_ok=True)
        write_exact(d / "raw_completion.txt", raw)
        write_exact(d / "r2_guidance.txt", r2_block)
        if extracted is not None:
            write_exact(d / "extracted_prior.lean", extracted)
        if stdout:
            write_exact(d / "lean_stdout.json", stdout)

        native_text = None
        native_sha = None
        if native_ok:
            code = goedel_native.submitted_code(extracted or "")
            native_text = goedel_native.get_error_str(code, errors)
            native_sha = sha(native_text)
            write_exact(d / "native_error.txt", native_text)

        prob = problems[pid]
        records.append({
            "root_id": pid,
            "split": split_of[pid],
            "theorem_text": prob["formal_statement"],
            "theorem_header": prob["header"],
            "theorem_sha256": sha(prob["formal_statement"]),
            "raw_prior_assistant_completion_sha256": sha(raw),
            "raw_prior_assistant_chars": len(raw),
            "raw_prior_completion_tokens": rec["response"]["usage"]["completion_tokens"],
            "stage1_prompt_tokens": rec["response"]["usage"]["prompt_tokens"],
            "stage1_seed": rec.get("seed"),
            "outcome_state": state,
            "fine_failure_class": fine,
            "coarse_failure_group": COARSE[fine],
            "extracted_prior_lean_available": extracted is not None,
            "extracted_prior_lean_sha256": sha(extracted) if extracted is not None else None,
            "guidance_policy_id": R2_POLICY_ID,
            "guidance_renderer_source": RENDERER_SOURCE,
            "guidance_renderer_git_commit": SUPPLEMENT_COMMIT,
            "guidance_renderer_snapshot_sha256": sha_file(
                SUPPLEMENT / "src/mospe_navi.py"
            ),
            "guidance_template_sha256": sha(policy.GUIDANCE_TEMPLATE),
            "r2_guidance_tactics": g2,
            "r2_guidance_text": r2_block,
            "r2_guidance_sha256": sha(r2_block),
            "r2_historical_full_prompt_sha256": sha(rendered),
            "native_feedback_available": native_ok,
            "native_feedback_kind": kind,
            "native_error_count": len(errors),
            "native_feedback_sha256": native_sha,
            "original_root_run": "epp_confirmatory_202",
        })
        elig.append({
            "root_id": pid,
            "split": split_of[pid],
            "fine_failure_class": fine,
            "coarse_failure_group": COARSE[fine],
            "outcome_state": state,
            "native_feedback_kind": kind,
            "native_error_count": len(errors),
            "e_eligible": native_ok,
        })
        branch = (
            "truncation_top3_retrieval"
            if fine == "truncated"
            else "other_retrieval_fallback"
            if fine == "other"
            else "error_class_pool"
        )
        r2_audit.append({
            "root_id": pid,
            "split": split_of[pid],
            "stage1_error_class": fine,
            "r2_conditioning_branch": branch,
            "r2_tactic_count": len(g2),
            "r2_guidance_sha256": sha(r2_block),
            "r2_full_prompt_sha256": sha(rendered),
            "matched_seed_tactics_identical": True,
            "working_renderer_identical": True,
            "supplement_renderer_identical": True,
        })

    with (HERE / "data/roots.jsonl").open("w", encoding="utf-8", newline="\n") as fh:
        for r in records:
            fh.write(json.dumps(r, ensure_ascii=False, sort_keys=True) + "\n")

    with (HERE / "audit/e_eligibility.csv").open(
            "w", encoding="utf-8", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(elig[0].keys()))
        w.writeheader()
        w.writerows(elig)

    with (HERE / "audit/r2_guidance_audit.csv").open(
            "w", encoding="utf-8", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(r2_audit[0].keys()))
        w.writeheader()
        w.writerows(r2_audit)

    ev = [r for r in records if r["split"] == "held_out"]
    n_e_eval = sum(1 for r in ev if r["native_feedback_available"])
    eval_kinds = Counter(r["native_feedback_kind"] for r in ev)
    dev_kinds = Counter(r["native_feedback_kind"] for r in records if r["split"] == "dev")
    assert eval_kinds == Counter({
        "native_error": 21,
        "budget_exhausted": 15,
        "verifier_timeout": 3,
        "stdout_unparseable": 1,
    }), f"corrected eval E-eligibility drift: {dict(eval_kinds)}"
    assert dev_kinds == Counter({
        "native_error": 23,
        "budget_exhausted": 17,
        "verifier_timeout": 3,
    }), f"corrected dev E-eligibility drift: {dict(dev_kinds)}"
    r2_branches = Counter(r["r2_conditioning_branch"] for r in r2_audit)
    assert sum(v for k, v in r2_branches.items() if k != "truncation_top3_retrieval") == 51
    assert r2_branches["truncation_top3_retrieval"] == 32

    roots_body = (HERE / "data/roots.jsonl").read_text(encoding="utf-8")
    freeze = {
        "status": "PASS",
        "authoritative_correction": "MASTER_CORRECTION.md",
        "root_count": len(records),
        "split_counts": {"dev": 43, "eval": 40},
        "guidance_policy_id": R2_POLICY_ID,
        "guidance_renderer_source": RENDERER_SOURCE,
        "guidance_renderer_git_commit": SUPPLEMENT_COMMIT,
        "guidance_template_sha256": sha(policy.GUIDANCE_TEMPLATE),
        "r2_branch_counts": dict(sorted(r2_branches.items())),
        "r2_nontruncation_dispatch_count": 51,
        "r2_truncation_top3_count": 32,
        "r2_all83_matched_seed_identical": True,
        "r2_all83_renderer_byte_identical": True,
        "e_eligible": {"all83": 44, "dev43": 23, "eval40": 21},
        "eval_feedback_kind_counts": dict(sorted(eval_kinds.items())),
        "canonical_generation_totals": {
            "eval_block1_abcd_plus_e": 181,
            "all83_abcd_plus_eval_e": 353,
        },
        "roots_jsonl_sha256": sha(roots_body),
        "open_decisions_not_frozen": [
            "seed_block_2_derivation",
            "plain_draw_descriptive_variance_band",
        ],
    }
    (HERE / "audit/step1_freeze.json").write_text(
        json.dumps(freeze, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    print(f"roots            : {len(records)}  (dev {len(records) - len(ev)} / eval {len(ev)})")
    print(f"E-eligible total : {sum(1 for r in records if r['native_feedback_available'])}")
    print(f"E-eligible eval  : {n_e_eval}")
    print("fine  :", dict(Counter(r["fine_failure_class"] for r in records)))
    print("coarse:", dict(Counter(r["coarse_failure_group"] for r in records)))
    print("E kinds eval     :", dict(eval_kinds))
    print("R2 branches      :", dict(r2_branches))
    print(f"roots.jsonl sha256: {sha(roots_body)}")
    receipts.write(STEP["id"], STEP["title"], STEP["inputs"], STEP["outputs"], {
        "roots": len(records),
        "dev": len(records) - len(ev),
        "eval": len(ev),
        "e_eligible_total": sum(1 for r in records if r["native_feedback_available"]),
        "e_eligible_eval": n_e_eval,
        "fine": dict(Counter(r["fine_failure_class"] for r in records)),
        "coarse": dict(Counter(r["coarse_failure_group"] for r in records)),
        "feedback_kind": dict(Counter(r["native_feedback_kind"] for r in records)),
        "roots_jsonl_sha256": sha(roots_body),
    })
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
