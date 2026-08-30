"""Build paper-facing W1 statistics and vector figures from frozen artifacts.

This script reads the experiment database and anchoring CSV read-only. It does not touch
the live timing replay. All bootstrap resampling uses roots as the independent unit.
"""

from __future__ import annotations

import csv
import json
import math
import random
import re
import sqlite3
import statistics
import sys
from collections import defaultdict
from pathlib import Path

from reportlab.lib.colors import Color, HexColor, black, white
from reportlab.pdfbase.pdfmetrics import stringWidth
from reportlab.pdfgen import canvas


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
DRAFT = ROOT / "paper_results"
sys.path.insert(0, str(ROOT / "src"))

import policy  # noqa: E402

DB = ROOT / "data" / "runs.sqlite"
CPRIME_B1_DB = ROOT / "data" / "cprime.sqlite"
CPRIME_B2_DB = ROOT / "data" / "cprime_b2.sqlite"
ANCHORING = ROOT / "audit" / "anchoring_results.csv"
OUT = DRAFT / "computed_results.json"
FIG = DRAFT / "figures"
FIG.mkdir(parents=True, exist_ok=True)

BLUE = HexColor("#2C6AA6")
BLUE2 = HexColor("#76A5D4")
ORANGE = HexColor("#D87832")
ORANGE2 = HexColor("#F0B37E")
GREEN = HexColor("#3B8C6E")
GRAY = HexColor("#606873")
LIGHT = HexColor("#E8EDF2")
DARK = HexColor("#17212B")

# Deliberately frozen to the broad detector already used by s24/s25.  The new analysis
# uses only command heads, never arguments, so it measures strategy-level overlap rather
# than rewarding whitespace or copied theorem scaffolding.
TACTIC_HEAD = re.compile(
    r"\b(nlinarith|linarith|norm_num|simp|ring_nf|ring|omega|decide|field_simp|"
    r"positivity|polyrith|intro|intros|induction|cases|rcases|obtain|use|refine|exact|"
    r"apply|constructor|rfl|subst|rw|unfold|have|calc|interval_cases|push_cast|"
    r"norm_cast|linear_combination|aesop|tauto|contrapose|by_contra)\b")


def percentile(xs: list[float], p: float) -> float:
    ys = sorted(xs)
    if not ys:
        return float("nan")
    x = (len(ys) - 1) * p
    lo, hi = int(math.floor(x)), int(math.ceil(x))
    if lo == hi:
        return ys[lo]
    return ys[lo] * (hi - x) + ys[hi] * (x - lo)


def bootstrap_mean(values: list[float], seed: int, reps: int = 50000) -> tuple[float, float]:
    rng = random.Random(seed)
    n = len(values)
    sims = [sum(values[rng.randrange(n)] for _ in range(n)) / n for _ in range(reps)]
    return percentile(sims, .025), percentile(sims, .975)


def wilson(k: int, n: int, z: float = 1.959963984540054) -> tuple[float, float]:
    if n == 0:
        return float("nan"), float("nan")
    p = k / n
    den = 1 + z * z / n
    center = (p + z * z / (2 * n)) / den
    half = z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / den
    return center - half, center + half


def exact_mcnemar(x_only: int, y_only: int) -> float:
    """Two-sided exact McNemar test, i.e. an exact Binomial(n, 1/2) tail."""
    n = x_only + y_only
    if n == 0:
        return 1.0
    k = min(x_only, y_only)
    tail = sum(math.comb(n, i) for i in range(k + 1)) / (2 ** n)
    return min(1.0, 2.0 * tail)


def load() -> tuple[dict, dict, dict]:
    anch: dict[tuple[str, str], dict[str, float]] = defaultdict(dict)
    with ANCHORING.open(encoding="utf-8", newline="") as fh:
        for r in csv.DictReader(fh):
            anch[(r["cohort"], r["root_id"])][r["arm"]] = float(r["anchoring_S"])

    con = sqlite3.connect(f"file:{DB}?mode=ro", uri=True)
    cols = ["branch_key", "cohort", "root_id", "arm", "seed_block", "verified",
            "outcome_state", "completion_tokens", "prefill_tokens", "total_tokens",
            "finish_reason", "coarse_failure_group", "fine_failure_class"]
    cols.insert(6, "completion")
    branches: dict[tuple[str, str], dict[str, dict]] = defaultdict(dict)
    for row in con.execute("SELECT " + ",".join(cols) +
                           " FROM branches WHERE status='done'"):
        rec = dict(zip(cols, row))
        branches[(rec["cohort"], rec["root_id"])][rec["arm"]] = rec
    con.close()

    roots = {}
    with (ROOT / "data" / "roots.jsonl").open(encoding="utf-8") as fh:
        for line in fh:
            r = json.loads(line)
            roots[r["root_id"]] = r
    return anch, branches, roots


def contrast(anch: dict, cohort: str, x: str, y: str, eligible: set[str] | None = None,
             seed: int = 1) -> dict:
    rows = []
    for (co, rid), arms in anch.items():
        if co == cohort and x in arms and y in arms and (eligible is None or rid in eligible):
            rows.append((rid, arms[x], arms[y], arms[x] - arms[y]))
    diffs = [r[3] for r in rows]
    lo, hi = bootstrap_mean(diffs, 20260828 + seed)
    return {
        "contrast": f"{x}-{y}", "n": len(diffs),
        "mean_x": statistics.mean(r[1] for r in rows),
        "mean_y": statistics.mean(r[2] for r in rows),
        "mean_diff": statistics.mean(diffs), "median_diff": statistics.median(diffs),
        "ci95": [lo, hi], "positive": sum(d > 0 for d in diffs),
        "diffs": [{"root_id": rid, "diff": d} for rid, _, _, d in rows],
    }


def verification_summary(branches: dict, cohort: str) -> dict:
    roots = {rid: arms for (co, rid), arms in branches.items() if co == cohort}
    out = {"rates": {}, "pairwise": {}, "interaction": {}}
    for arm in "ABCDE":
        vals = [int(a[arm]["verified"] or 0) for a in roots.values() if arm in a]
        if vals:
            k, n = sum(vals), len(vals)
            out["rates"][arm] = {"k": k, "n": n, "rate": k / n,
                                   "wilson95": list(wilson(k, n))}
    for idx, (x, y) in enumerate((("C", "A"), ("D", "B"), ("B", "A"),
                                  ("D", "C"), ("E", "A"))):
        pairs = [(int(a[x]["verified"] or 0), int(a[y]["verified"] or 0))
                 for a in roots.values() if x in a and y in a]
        if not pairs:
            continue
        diffs = [u - v for u, v in pairs]
        lo, hi = bootstrap_mean(diffs, 20261000 + idx)
        out["pairwise"][f"{x}-{y}"] = {
            "n": len(pairs), "effect": statistics.mean(diffs), "ci95": [lo, hi],
            "x_only": sum(u == 1 and v == 0 for u, v in pairs),
            "y_only": sum(u == 0 and v == 1 for u, v in pairs),
        }
    d = []
    for a in roots.values():
        if all(x in a for x in "ABCD"):
            y = {x: int(a[x]["verified"] or 0) for x in "ABCD"}
            d.append((y["D"] - y["C"]) - (y["B"] - y["A"]))
    lo, hi = bootstrap_mean(d, 20261111)
    out["interaction"] = {"n": len(d), "effect": statistics.mean(d), "ci95": [lo, hi]}
    return out


def fixed_root_multiseed(anch: dict, branches: dict) -> dict:
    result = {}
    for x, y, name in (("C", "A", "T0"), ("D", "B", "T1")):
        per_root = defaultdict(list)
        for cohort in ("primary_eval", "eval_block2"):
            for (co, rid), arms in anch.items():
                if co == cohort and x in arms and y in arms:
                    per_root[rid].append(arms[x] - arms[y])
        vals = [statistics.mean(v) for v in per_root.values()]
        result[name] = {"n_roots": len(vals), "mean": statistics.mean(vals),
                        "median": statistics.median(vals),
                        "ci95": list(bootstrap_mean(vals, 20261200 + ord(x)))}
    per_root_v = defaultdict(list)
    for cohort in ("primary_eval", "eval_block2"):
        for (co, rid), arms in branches.items():
            if co == cohort and "A" in arms and "C" in arms:
                per_root_v[rid].append(int(arms["C"]["verified"] or 0) -
                                       int(arms["A"]["verified"] or 0))
    vals = [statistics.mean(v) for v in per_root_v.values()]
    result["C-A_verification"] = {
        "n_roots": len(vals), "mean": statistics.mean(vals),
        "ci95": list(bootstrap_mean(vals, 20261313))}
    return result


def native_subset(anch: dict, branches: dict, cohort: str) -> dict:
    eligible = {rid for (co, rid), arms in branches.items() if co == cohort and "E" in arms}
    out = {"n": len(eligible), "anchoring": {}, "verification": {}}
    for idx, (x, y) in enumerate((("C", "A"), ("D", "B"), ("E", "A"))):
        out["anchoring"][f"{x}-{y}"] = contrast(
            anch, cohort, x, y, eligible, seed=300 + idx)
    for x, y in (("C", "A"), ("D", "B"), ("E", "A")):
        pairs = []
        # Set iteration depends on Python's randomized hash seed.  Sort before the
        # finite bootstrap so repeated artifact builds are byte-identical.
        for rid in sorted(eligible):
            a = branches[(cohort, rid)]
            pairs.append((int(a[x]["verified"] or 0), int(a[y]["verified"] or 0)))
        diffs = [u-v for u, v in pairs]
        out["verification"][f"{x}-{y}"] = {
            "effect": statistics.mean(diffs),
            "x_only": sum(u == 1 and v == 0 for u, v in pairs),
            "y_only": sum(u == 0 and v == 1 for u, v in pairs),
            "ci95": list(bootstrap_mean(diffs, 20261414 + ord(x))),
        }
    return out


def mechanism(branches: dict, anch: dict) -> dict:
    groups = ("incomplete", "localized_complete", "diffuse_complete")
    out = {}
    for group in groups:
        rows = []
        for cohort in ("primary_eval", "eval_block2"):
            for (co, rid), arms in branches.items():
                if co != cohort or "A" not in arms or "C" not in arms:
                    continue
                if arms["A"]["coarse_failure_group"] != group:
                    continue
                av, cv = int(arms["A"]["verified"] or 0), int(arms["C"]["verified"] or 0)
                rows.append({
                    "root_id": rid, "cohort": cohort, "A_verified": av, "C_verified": cv,
                    "A_tokens": arms["A"]["completion_tokens"],
                    "C_tokens": arms["C"]["completion_tokens"],
                    "A_trunc": arms["A"]["outcome_state"] == "truncated",
                    "C_trunc": arms["C"]["outcome_state"] == "truncated",
                    "anchoring_diff": anch[(cohort, rid)]["C"] - anch[(cohort, rid)]["A"],
                })
        out[group] = {
            "n_root_seed": len(rows),
            "A_only": sum(r["A_verified"] == 1 and r["C_verified"] == 0 for r in rows),
            "C_only": sum(r["A_verified"] == 0 and r["C_verified"] == 1 for r in rows),
            "A_mean_tokens": statistics.mean(r["A_tokens"] for r in rows),
            "C_mean_tokens": statistics.mean(r["C_tokens"] for r in rows),
            "A_trunc_rate": statistics.mean(r["A_trunc"] for r in rows),
            "C_trunc_rate": statistics.mean(r["C_trunc"] for r in rows),
            "mean_anchoring_diff": statistics.mean(r["anchoring_diff"] for r in rows),
        }
    return out


def extracted_lean(text: str, theorem_text: str) -> str:
    """Return normalized Lean code only; plans and Markdown prose are excluded."""
    lean = policy.extract_lean(text or "", theorem_text)
    return policy.strip_lean_comments(lean or "").replace("\r\n", "\n")


def tactic_sequence(text: str, theorem_text: str) -> list[str]:
    """Tactic command heads in source order.

    This deliberately ignores arguments.  `simp [h]` and `simp only [h]` share a head,
    while `simp` and `nlinarith` do not.  Multiple commands joined by `<;>` remain
    separate observations in source order.
    """
    lean = extracted_lean(text, theorem_text)
    return [m.group(1) for m in TACTIC_HEAD.finditer(lean)]


def sequence_lcs(a: list[str], b: list[str]) -> float | None:
    """2*LCS/(|a|+|b|), undefined only when both sequences are empty."""
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


def trajectory_diversity(branches: dict, roots: dict) -> dict:
    """Directly compare each arm's two seed-block trajectories on the same 40 roots.

    A--D come from the registered database.  C' is loaded read-only from its two
    post-hoc control databases.  The root-set equality assertions prevent a partial C'
    run from silently changing any denominator.
    """
    b1 = {rid: arms for (co, rid), arms in branches.items() if co == "primary_eval"}
    b2 = {rid: arms for (co, rid), arms in branches.items() if co == "eval_block2"}
    shared = sorted(set(b1) & set(b2))
    cp = {}
    for label, path in (("block1", CPRIME_B1_DB), ("block2", CPRIME_B2_DB)):
        con = sqlite3.connect(f"file:{path}?mode=ro", uri=True)
        got = {rid: completion or "" for rid, completion in con.execute(
            "SELECT root_id, completion FROM branches "
            "WHERE status='done' AND arm='Cp' ORDER BY root_id")}
        con.close()
        if set(got) != set(shared):
            missing = sorted(set(shared) - set(got))
            extra = sorted(set(got) - set(shared))
            raise AssertionError(
                f"C' {label} root set differs from the 40-root evaluation set: "
                f"missing={missing}, extra={extra}")
        cp[label] = got

    per_arm, rows = {}, []
    for arm in ("A", "B", "C", "D", "Cp"):
        lcs, first_defined, first_same, prefix3_same = [], 0, 0, 0
        for rid in shared:
            theorem = roots[rid]["theorem_text"]
            if arm == "Cp":
                s1 = tactic_sequence(cp["block1"][rid], theorem)
                s2 = tactic_sequence(cp["block2"][rid], theorem)
            else:
                s1 = tactic_sequence(b1[rid][arm]["completion"] or "", theorem)
                s2 = tactic_sequence(b2[rid][arm]["completion"] or "", theorem)
            sim = sequence_lcs(s1, s2)
            if sim is not None:
                lcs.append(sim)
            both_first = bool(s1) and bool(s2)
            if both_first:
                first_defined += 1
                first_same += int(s1[0] == s2[0])
                prefix3_same += int(tuple(s1[:3]) == tuple(s2[:3]))
            rows.append({
                "root_id": rid, "arm": arm, "n_tactics_block1": len(s1),
                "n_tactics_block2": len(s2), "first_block1": s1[0] if s1 else None,
                "first_block2": s2[0] if s2 else None,
                "first_same": int(s1[0] == s2[0]) if both_first else None,
                "prefix3_same": int(tuple(s1[:3]) == tuple(s2[:3])) if both_first else None,
                "sequence_lcs": sim,
            })
        per_arm[arm] = {
            "n_roots": len(shared), "n_lcs_defined": len(lcs),
            "mean_sequence_lcs": statistics.mean(lcs),
            "n_first_defined": first_defined, "first_same": first_same,
            "first_different": first_defined - first_same,
            "first_same_rate": first_same / first_defined,
            "prefix3_same": prefix3_same,
            "prefix3_same_rate": prefix3_same / first_defined,
        }

    by = defaultdict(dict)
    for r in rows:
        by[r["root_id"]][r["arm"]] = r
    paired = {}
    for x, y in (("C", "A"), ("D", "B"), ("Cp", "A"), ("C", "Cp")):
        diffs = [arms[x]["sequence_lcs"] - arms[y]["sequence_lcs"]
                 for arms in by.values()
                 if arms[x]["sequence_lcs"] is not None
                 and arms[y]["sequence_lcs"] is not None]
        seed = 20260830 + sum((i + 1) * ord(ch) for i, ch in enumerate(x + y))
        lo, hi = bootstrap_mean(diffs, seed)
        paired[f"{x}-{y}"] = {
            "n": len(diffs), "mean_lcs_difference": statistics.mean(diffs),
            "ci95": [lo, hi], "positive": sum(d > 0 for d in diffs),
        }
    return {"shared_roots": len(shared), "arms": per_arm, "paired": paired,
            "rows": rows}


def normalize_code_line(line: str) -> str:
    return re.sub(r"\s+", " ", line.strip().lstrip("· ")).strip()


def failure_step_reuse(branches: dict, roots: dict) -> dict:
    """Does a recovery branch retain the exact source line the checker rejected?

    The source location comes from the root's frozen Lean JSON receipt.  This is restricted
    to roots with an in-range deterministic error location and reported separately by seed
    block; the two blocks are repeat draws over the same theorems, never 42 independent
    roots.
    """
    located = {}
    for rid, root in roots.items():
        receipt = ROOT / "artifacts" / "roots" / rid / "lean_stdout.json"
        source = ROOT / "artifacts" / "roots" / rid / "extracted_prior.lean"
        if not receipt.exists() or not source.exists():
            continue
        try:
            obj = json.loads(receipt.read_text(encoding="utf-8"))
        except json.JSONDecodeError:
            # One frozen root is explicitly ineligible because its stdout was clipped;
            # an unparsable receipt cannot supply a trustworthy source location.
            continue
        messages = [m for m in obj.get("messages", [])
                    if m.get("severity") == "error" and m.get("pos", {}).get("line")]
        if not messages:
            continue
        lines = source.read_text(encoding="utf-8").replace("\r\n", "\n").split("\n")
        line_no = int(messages[0]["pos"]["line"])
        if not (1 <= line_no <= len(lines)):
            continue
        failed_line = normalize_code_line(lines[line_no - 1])
        if not failed_line:
            continue
        msg = str(messages[0].get("data", ""))
        mt = re.search(r"tactic ['`]([^'`]+)['`]", msg)
        mh = TACTIC_HEAD.search(failed_line)
        head = mt.group(1) if mt else (mh.group(1) if mh else None)
        located[rid] = {"line": failed_line, "line_no": line_no, "tactic_head": head}

    cohorts = ("primary_eval", "eval_block2")
    summary, rows = {}, []
    for cohort in cohorts:
        available = {rid: arms for (co, rid), arms in branches.items()
                     if co == cohort and rid in located}
        block = {"n": len(available), "arms": {}, "contrasts": {}}
        for arm in "ABCD":
            exact, head = 0, 0
            for rid, arms in available.items():
                lean = extracted_lean(arms[arm]["completion"] or "", roots[rid]["theorem_text"])
                norm_lines = {normalize_code_line(x) for x in lean.split("\n") if x.strip()}
                seq = tactic_sequence(arms[arm]["completion"] or "", roots[rid]["theorem_text"])
                ex = located[rid]["line"] in norm_lines
                hd = located[rid]["tactic_head"] in seq if located[rid]["tactic_head"] else None
                exact += int(ex)
                head += int(bool(hd))
                rows.append({"cohort": cohort, "root_id": rid, "arm": arm,
                             "exact_failed_line_reused": int(ex),
                             "failed_tactic_head_reused": int(bool(hd)) if hd is not None else None,
                             "failed_tactic_head": located[rid]["tactic_head"],
                             "failed_line": located[rid]["line"]})
            block["arms"][arm] = {"exact_line": exact, "tactic_head": head}
        by = defaultdict(dict)
        for r in rows:
            if r["cohort"] == cohort:
                by[r["root_id"]][r["arm"]] = r
        for x, y in (("C", "A"), ("D", "B")):
            for metric in ("exact_failed_line_reused", "failed_tactic_head_reused"):
                pairs = [(a[x][metric], a[y][metric]) for a in by.values()
                         if x in a and y in a and a[x][metric] is not None and a[y][metric] is not None]
                block["contrasts"][f"{x}-{y}:{metric}"] = {
                    "n": len(pairs), "x_only": sum(u == 1 and v == 0 for u, v in pairs),
                    "y_only": sum(u == 0 and v == 1 for u, v in pairs),
                    "both": sum(u == 1 and v == 1 for u, v in pairs),
                    "neither": sum(u == 0 and v == 0 for u, v in pairs),
                }
                rec = block["contrasts"][f"{x}-{y}:{metric}"]
                diffs = [u - v for u, v in pairs]
                seed = (20260831 + (0 if cohort == "primary_eval" else 1000)
                        + (0 if x == "C" else 100)
                        + (0 if metric == "exact_failed_line_reused" else 10))
                lo, hi = bootstrap_mean(diffs, seed)
                rec.update({
                    "effect": statistics.mean(diffs),
                    "ci95": [lo, hi],
                    "p_exact_mcnemar": exact_mcnemar(rec["x_only"], rec["y_only"]),
                })
        summary[cohort] = block
    return {"located_unique_roots": len(located), "blocks": summary, "rows": rows}


def verification_pairs(branches: dict) -> dict:
    out = {}
    for cohort in ("primary_eval", "eval_block2"):
        roots = {rid: arms for (co, rid), arms in branches.items()
                 if co == cohort and "A" in arms and "C" in arms}
        rows = []
        for idx, (rid, arms) in enumerate(sorted(roots.items()), 1):
            av, cv = int(arms["A"]["verified"] or 0), int(arms["C"]["verified"] or 0)
            state = ("both" if av and cv else "A_only" if av else
                     "C_only" if cv else "neither")
            rows.append({"index": idx, "root_id": rid, "A": av, "C": cv,
                         "state": state})
        out[cohort] = rows
    return out


def arm_rows(c: canvas.Canvas, x: float, y: float, w: float, h: float,
             label: str, title: str, detail: str, fill: Color) -> None:
    c.setFillColor(fill)
    c.setStrokeColor(DARK)
    c.roundRect(x, y, w, h, 6, fill=1, stroke=1)
    c.setFillColor(white if fill != LIGHT else DARK)
    c.setFont("Helvetica-Bold", 10)
    c.drawString(x + 8, y + h - 14, f"{label}  {title}")
    c.setFont("Helvetica", 7.5)
    c.drawString(x + 8, y + 8, detail)


def fig_design() -> None:
    W, H = 520, 192
    c = canvas.Canvas(str(FIG / "fig1_design.pdf"), pagesize=(W, H))
    c.setTitle("W1 factorial design")
    c.setFillColor(DARK); c.setFont("Helvetica-Bold", 11)
    c.drawString(16, 174, "Controlled recovery interfaces on the same failed root")
    c.setFont("Helvetica", 7.5); c.setFillColor(GRAY)
    c.drawRightString(505, 174, "same theorem, seed, sampler, and 12,288-token cap")
    c.setFillColor(GRAY); c.setFont("Helvetica-Bold", 7.5)
    c.drawCentredString(167, 160, "Guidance absent")
    c.drawCentredString(389, 160, "Guidance present")
    c.saveState(); c.translate(12, 126); c.rotate(90); c.drawCentredString(0, 0, "Prior absent"); c.restoreState()
    c.saveState(); c.translate(12, 61); c.rotate(90); c.drawCentredString(0, 0, "Prior present"); c.restoreState()
    arm_rows(c, 56, 104, 190, 45, "A", "Plain fresh", "BASE(theorem)", LIGHT)
    arm_rows(c, 278, 104, 220, 45, "B", "R2-guided fresh", "R2 + BASE(theorem)", BLUE)
    arm_rows(c, 56, 42, 190, 45, "C", "Prior attempt", "WRAPPER(attempt) + BASE(theorem)", ORANGE)
    arm_rows(c, 278, 42, 220, 45, "D", "R2-guided prior", "R2 + WRAPPER(attempt) + BASE(theorem)", GREEN)
    c.setStrokeColor(GRAY); c.setLineWidth(1)
    c.line(252, 45, 252, 153)
    c.setFillColor(GRAY); c.setFont("Helvetica-Bold", 7.5)
    c.setFillColor(DARK); c.setFont("Helvetica", 7)
    c.drawString(16, 10, "E (native format control, n=21): theorem turn / prior assistant completion / genuine Lean <error> correction turn")
    c.showPage(); c.save()


def forest(c: canvas.Canvas, x0: float, x1: float, y: float, lo: float, mean: float,
           hi: float, xmin: float, xmax: float, color: Color, marker: str = "circle") -> None:
    sx = lambda v: x0 + (v - xmin) / (xmax - xmin) * (x1 - x0)
    c.setStrokeColor(color); c.setFillColor(color); c.setLineWidth(2)
    c.line(sx(lo), y, sx(hi), y)
    c.line(sx(lo), y-3, sx(lo), y+3); c.line(sx(hi), y-3, sx(hi), y+3)
    if marker == "square":
        c.rect(sx(mean)-3.2, y-3.2, 6.4, 6.4, fill=1, stroke=0)
    else:
        c.circle(sx(mean), y, 3.4, fill=1, stroke=0)


def fig_anchoring(results: dict) -> None:
    W, H = 520, 245
    c = canvas.Canvas(str(FIG / "fig2_anchoring.pdf"), pagesize=(W, H))
    c.setTitle("Replicated prior-attempt textual anchoring")
    c.setFillColor(DARK); c.setFont("Helvetica-Bold", 11)
    c.drawString(16, 226, "Prior-attempt access strongly increases textual anchoring")
    x0, x1, xmin, xmax = 215, 420, -0.05, 0.43
    sx = lambda v: x0 + (v - xmin)/(xmax-xmin)*(x1-x0)
    c.setStrokeColor(LIGHT); c.setLineWidth(.6)
    for t in (0, .1, .2, .3, .4):
        c.line(sx(t), 34, sx(t), 209)
        c.setFillColor(GRAY); c.setFont("Helvetica", 7)
        c.drawCentredString(sx(t), 22, f"{t:.1f}")
    c.setStrokeColor(DARK); c.setLineWidth(1); c.line(sx(0), 34, sx(0), 209)
    rows = [
        ("Block 1 (registered)", "T0", results["anchoring"]["primary_eval"]["C-A"], ORANGE),
        ("", "T1", results["anchoring"]["primary_eval"]["D-B"], GREEN),
        ("Block 2 (seed replication)", "T0", results["anchoring"]["eval_block2"]["C-A"], ORANGE),
        ("", "T1", results["anchoring"]["eval_block2"]["D-B"], GREEN),
        ("Dev-43 (descriptive)", "T0", results["anchoring"]["full_pool_dev"]["C-A"], ORANGE),
        ("", "T1", results["anchoring"]["full_pool_dev"]["D-B"], GREEN),
    ]
    ys = [192, 169, 137, 114, 82, 59]
    for (group, tag, r, color), y in zip(rows, ys):
        c.setFillColor(DARK); c.setFont("Helvetica-Bold" if group else "Helvetica", 7.5)
        if group: c.drawString(16, y-2, group)
        c.setFont("Helvetica-Bold", 8); c.setFillColor(color); c.drawString(156, y-2, tag)
        lo, hi = r["ci95"]
        forest(c, x0, x1, y, lo, r["mean_diff"], hi, xmin, xmax, color,
               "square" if tag == "T1" else "circle")
        c.setFillColor(DARK); c.setFont("Helvetica", 7)
        c.drawRightString(510, y-2, f"{r['mean_diff']:+.3f}  [{lo:+.3f}, {hi:+.3f}]")
    c.setFillColor(DARK); c.setFont("Helvetica", 7.5)
    c.drawCentredString((x0+x1)/2, 8, "paired mean difference in anchoring S (root-bootstrap 95% CI)")
    c.setFillColor(ORANGE); c.circle(25, 35, 3, fill=1, stroke=0)
    c.setFillColor(DARK); c.drawString(32, 32, "T0 = C-A")
    c.setFillColor(GREEN); c.rect(90, 32, 6, 6, fill=1, stroke=0)
    c.setFillColor(DARK); c.drawString(101, 32, "T1 = D-B")
    c.showPage(); c.save()


def fig_verification(results: dict) -> None:
    W, H = 520, 245
    c = canvas.Canvas(str(FIG / "fig3_verification.pdf"), pagesize=(W, H))
    c.setTitle("Paired verification outcomes and registered interaction")
    c.setFillColor(DARK); c.setFont("Helvetica-Bold", 11)
    c.drawString(16, 226, "The same roots expose one-directional A/C discordance under both seeds")

    state_color = {"A_only": BLUE, "C_only": ORANGE, "both": GREEN, "neither": LIGHT}
    x0, cell, gap = 72, 7.65, .45
    for row, cohort in enumerate(("primary_eval", "eval_block2")):
        y = 170 - row * 64
        label = "Block 1" if row == 0 else "Block 2"
        c.setFillColor(DARK); c.setFont("Helvetica-Bold", 8)
        c.drawRightString(x0 - 8, y + 2, label)
        pairs = results["verification_pairs"][cohort]
        for i, rec in enumerate(pairs):
            x = x0 + i * (cell + gap)
            c.setFillColor(state_color[rec["state"]])
            c.setStrokeColor(DARK if rec["state"] != "neither" else GRAY)
            c.rect(x, y, cell, 19, fill=1, stroke=1)
        counts = {s: sum(r["state"] == s for r in pairs) for s in state_color}
        c.setFillColor(DARK); c.setFont("Helvetica", 6.6)
        c.drawString(x0, y - 12,
                     f"A-only {counts['A_only']}   C-only {counts['C_only']}   "
                     f"both {counts['both']}   neither {counts['neither']}")
        for tick in (1, 10, 20, 30, 40):
            x = x0 + (tick - 1) * (cell + gap) + cell / 2
            c.setFillColor(GRAY); c.setFont("Helvetica", 5.5)
            c.drawCentredString(x, y + 23, str(tick))

    c.setFont("Helvetica", 6.2)
    lx = x0
    for state, label in (("A_only", "A only"), ("C_only", "C only"),
                         ("both", "both"), ("neither", "neither")):
        c.setFillColor(state_color[state]); c.setStrokeColor(DARK if state != "neither" else GRAY)
        c.rect(lx, 48, 7, 7, fill=1, stroke=1)
        c.setFillColor(DARK); c.drawString(lx + 10, 48, label)
        lx += 58

    # Keep the registered interaction visible, but subordinate to the paired root display.
    c.setStrokeColor(LIGHT); c.line(405, 35, 405, 205)
    c.setFillColor(DARK); c.setFont("Helvetica-Bold", 8)
    c.drawString(420, 201, "Registered interaction")
    for y, cohort, label in ((160, "primary_eval", "Block 1"),
                             (118, "eval_block2", "Block 2"),
                             (76, "full_pool_dev", "Dev-43")):
        r = results["verification"][cohort]["interaction"]
        lo, hi = r["ci95"]
        c.setFillColor(DARK); c.setFont("Helvetica", 7); c.drawString(420, y+9, label)
        forest(c, 420, 505, y, lo, r["effect"], hi, -.15, .25, GREEN)
        c.setFont("Helvetica", 6.2); c.drawString(420, y-12, f"I={r['effect']:+.3f} [{lo:+.3f},{hi:+.3f}]")
    c.setFillColor(GRAY); c.setFont("Helvetica", 6.5)
    c.drawString(16, 22, "Each tile is one held-out theorem; the horizontal order is identical across seed blocks.")
    c.drawString(420, 42, "I=(D-C)-(B-A)")
    c.showPage(); c.save()


def fig_mechanism(results: dict) -> None:
    # Drawn at the width the paper actually displays it at (\linewidth), so
    # \includegraphics[width=\linewidth] is a 1:1 inclusion and the annotation type
    # renders at its nominal size. The previous 520pt canvas was downscaled to about
    # 0.76, which put the 6.5pt labels near 5pt.
    W, H = 397, 176
    c = canvas.Canvas(str(FIG / "fig4_mechanism.pdf"), pagesize=(W, H))
    c.setTitle("Descriptive failure-group mechanism")
    # The title and the descriptive caveat live in the LaTeX caption, not on the canvas:
    # printing them twice cost about 40pt of a nine-page budget.
    groups = [("incomplete", "Incomplete"), ("localized_complete", "Localized complete"),
              ("diffuse_complete", "Diffuse complete")]
    for i, (key, label) in enumerate(groups):
        x = 12 + i * 126
        r = results["mechanism"][key]
        c.setFillColor(DARK); c.setFont("Helvetica-Bold", 8)
        c.drawCentredString(x+60, 163, label)
        maxd = 8
        c.setFillColor(BLUE); c.rect(x+30, 48, 26, r["A_only"] / maxd * 92, fill=1, stroke=0)
        c.setFillColor(ORANGE); c.rect(x+66, 48, 26, r["C_only"] / maxd * 92, fill=1, stroke=0)
        c.setFillColor(DARK); c.setFont("Helvetica-Bold", 8.5)
        c.drawCentredString(x+43, 53 + r["A_only"] / maxd * 92, str(r["A_only"]))
        c.drawCentredString(x+79, 53 + r["C_only"] / maxd * 92, str(r["C_only"]))
        c.setFont("Helvetica", 7.5)
        c.drawCentredString(x+43, 37, "A-only")
        c.drawCentredString(x+79, 37, "C-only")
        c.setFont("Helvetica", 7); c.setFillColor(GRAY)
        c.drawCentredString(x+60, 24, f"tokens A/C {r['A_mean_tokens']:.0f}/{r['C_mean_tokens']:.0f}")
        c.drawCentredString(x+60, 14, f"anchoring C-A {r['mean_anchoring_diff']:+.3f}")
        c.drawCentredString(x+60, 4, f"n={r['n_root_seed']} root-seed obs.")

    c.showPage(); c.save()


def main() -> int:
    anch, branches, roots = load()
    cohorts = ("primary_eval", "eval_block2", "full_pool_dev")
    results = {
        "source": {
            "spec_sha256": (ROOT / "spec/frozen_spec.sha256").read_text(encoding="utf-8").split()[0],
            "branches": sum(len(v) for v in branches.values()),
            "roots": len(roots),
            "bootstrap_reps": 50000,
            "independent_unit": "root",
        },
        "anchoring": {}, "verification": {},
    }
    for ci, cohort in enumerate(cohorts):
        results["anchoring"][cohort] = {
            "C-A": contrast(anch, cohort, "C", "A", seed=10+ci),
            "D-B": contrast(anch, cohort, "D", "B", seed=20+ci),
        }
        results["verification"][cohort] = verification_summary(branches, cohort)
    results["native_primary"] = native_subset(anch, branches, "primary_eval")
    results["native_dev"] = native_subset(anch, branches, "full_pool_dev")
    results["fixed_root_multiseed"] = fixed_root_multiseed(anch, branches)
    results["mechanism"] = mechanism(branches, anch)
    results["trajectory_diversity"] = trajectory_diversity(branches, roots)
    results["failure_step_reuse"] = failure_step_reuse(branches, roots)
    results["verification_pairs"] = verification_pairs(branches)

    # Root-level rows are useful for plotting but make the paper-facing JSON noisy.
    clean = json.loads(json.dumps(results))
    for cohort in clean["anchoring"].values():
        for r in cohort.values():
            r.pop("diffs", None)
    for subset in (clean["native_primary"], clean["native_dev"]):
        for r in subset["anchoring"].values():
            r.pop("diffs", None)
    OUT.write_text(json.dumps(clean, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    fig_design()
    fig_anchoring(results)
    fig_verification(results)
    fig_mechanism(results)
    print(f"wrote {OUT}")
    for p in sorted(FIG.glob("*.pdf")):
        print(f"wrote {p}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
