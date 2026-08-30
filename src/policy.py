"""Frozen policy surface, copied VERBATIM from the CoLM harness
(CoLM_Jul2026_MoSpe_Navi/src/mospe_navi.py) on 2026-08-27.

These are not free parameters. The 83 first-failure roots were produced under exactly
this prompt and exactly this extractor, so any drift here silently changes what a
"root" means and breaks the paired A/B comparison. Copied rather than imported so the
NeurIPS run is hermetic and hashable on its own.

NOTE the prompt is NOT the official Goedel-Prover-V2 eval prompt -- it carries the
5-line-plan / commit-to-first-derivation addendum. That is a disclosed policy
component inherited from CoLM. Arm B is therefore "Goedel's native correction format
layered on a disclosed custom initial policy", never "the official protocol".

Regenerate with: python scripts/sync_policy.py  (verifies byte-identity upstream)
"""

from __future__ import annotations

import re

OFFICIAL_PROMPT = """Complete the following Lean 4 code:

```lean4
{}
```
Before producing the Lean 4 code, give a proof plan in at most five lines, then immediately provide the complete Lean 4 code. Do not restate or re-derive the plan in prose once you begin the code block. Commit to your first derivation -- do not restart the analysis or re-derive earlier steps if you notice a possible error; fix it in place and proceed directly to the Lean 4 code."""

PROMPT_ADDENDUM = ""

def official_prompt(formal_statement: str) -> str:
    base = OFFICIAL_PROMPT.format(formal_statement)
    return base + ("\n" + PROMPT_ADDENDUM if PROMPT_ADDENDUM else "")

# VERBATIM text from mospe_navi.py::concrete_guidance_prompt (line 978). Keeping the
# theorem-independent block explicit lets the factorial harness add exactly this text in
# B/D and hash it independently of the theorem-bearing base prompt.
GUIDANCE_TEMPLATE = """Similar Lean-verified proofs commonly used:
{listed}

These are optional suggestions; use only when applicable, and select exact tactics and arguments from the current theorem.

"""


def guidance_block(tactics: list[str] | None) -> str:
    """Render only R2BLOCK. Empty guidance contributes no bytes."""
    if not tactics:
        return ""
    listed = "\n".join(f"- {tactic}" for tactic in tactics)
    return GUIDANCE_TEMPLATE.format(listed=listed)


# This is the ONE full-prompt renderer the historical CoLM cascade used. Guidance is
# outermost: OFFICIAL(theorem) is an inseparable unit and R2BLOCK is prepended to it.
# See MASTER_CORRECTION.md Sec.3 -- any other ordering fails Gate 5.
def concrete_guidance_prompt(formal_statement: str, tactics: list[str] | None) -> str:
    """Prompt-parity note: this is the ONE template used by nav1/nav2/nav3 -- arms differ
    only in which tactics get passed in and their order, never in template wording or
    verbosity, so a downstream comparison can't be confounded by framing differences."""
    base = official_prompt(formal_statement)
    if not tactics:
        return base
    listed = "\n".join(f"- {tactic}" for tactic in tactics)
    return f"""Similar Lean-verified proofs commonly used:
{listed}

These are optional suggestions; use only when applicable, and select exact tactics and arguments from the current theorem.

{base}"""


def _extract_lean_legacy(text: str, formal_statement: str) -> str:
    """Original fence-pairing extraction. Kept as the PRIMARY path: it doesn't care what
    name the model gives its theorem, which turns out to matter -- Goedel occasionally
    echoes a hallucinated name from training-data leakage (e.g. `lean_workbook_plus_127`
    for `mathd_numbertheory_127`) while still writing a complete, correct proof of the
    same statement. Verified against real data (2026-07-17): every one of Goedel's and
    DeepSeek's already-recorded, already-Lean-verified results reproduces byte-identically
    through this path -- do not replace it, only repair its specific failure cases (see
    extract_lean)."""
    fenced = re.findall(r"```(?:lean4|lean)?\s*(.*?)```", text, flags=re.DOTALL | re.IGNORECASE)
    candidates = [block.strip() for block in fenced if "theorem " in block or "import Mathlib" in block]
    if candidates:
        candidate = candidates[-1]
        if "import " not in candidate:
            theorem_pos = formal_statement.find("theorem ")
            if theorem_pos >= 0:
                candidate = formal_statement[:theorem_pos] + candidate
        return candidate.rstrip() + "\n"
    by_match = re.search(r"\bby\b[\s\S]*", text)
    if by_match:
        prefix = formal_statement.rstrip()
        if prefix.endswith("by"):
            prefix = prefix[:-2].rstrip()
        return prefix + " " + by_match.group(0).strip() + "\n"
    return text.strip() + "\n"

def _extract_lean_anchored(text: str, formal_statement: str) -> str | None:
    """Repair path for when the legacy extractor fails: anchor on the theorem's own
    declared NAME (from formal_statement, authoritative) and take the LAST such
    declaration in the raw text, grafting only the proof body onto our own header --
    never trusting a model-restated signature. Fixes Kimina's habit of echoing the
    prompt's theorem statement inside a comment (sometimes inside a second, nested ```
    fence) before its real proof, which breaks naive fence-pairing. Also means the
    extracted code never contains the model's echoed prompt text, so a downstream
    sorry/admit safety check can't false-positive on the model quoting an instruction
    that mentions those words. Returns None if no anchored occurrence is found (caller
    falls back further)."""
    prefix = formal_statement.rstrip()
    if prefix.endswith("by"):
        prefix = prefix[:-2].rstrip()

    def take_body(raw: str) -> str | None:
        # Lean 4 tactic blocks are indentation-sensitive: a blanket .strip() destroys the
        # body's relative indentation (its first line loses leading whitespace while
        # nested/sibling lines keep theirs), which silently turns a genuinely-valid proof
        # into an "unexpected identifier; expected command" parse error at the point
        # indentation becomes inconsistent. Found via a real Kimina reparse (2026-07-17):
        # mathd_algebra_484's tactics were untouched but this bug alone flipped a verified
        # proof to lean_failed. Fix: trim only whole leading/trailing BLANK lines and a
        # leading "by" TOKEN (not the line's whitespace), preserving every other line's
        # indentation exactly as the model wrote it.
        lines = raw.splitlines()
        while lines and not lines[0].strip():
            lines.pop(0)
        while lines and not lines[-1].strip():
            lines.pop()
        if not lines:
            return None
        first_match = re.match(r"^(\s*)by\b(\s*)(.*)$", lines[0], flags=re.IGNORECASE)
        if first_match:
            rest = first_match.group(3)
            lines[0] = rest if rest else None
            if lines[0] is None:
                lines.pop(0)
        while lines and not lines[0].strip():
            lines.pop(0)
        return "\n".join(lines) if lines else None

    def bounded(chunk: str) -> str:
        fence_end = chunk.find("```")
        return chunk[:fence_end] if fence_end != -1 else chunk

    body = None
    name_match = re.search(r"\b(?:theorem|lemma)\s+(\S+)", formal_statement)
    if name_match:
        name = re.escape(name_match.group(1))
        occurrences = list(re.finditer(rf"\b(?:theorem|lemma)\s+{name}\b", text))
        if occurrences:
            start = occurrences[-1].start()
            marker = re.search(r":=", text[start:])
            if marker:
                body = take_body(bounded(text[start + marker.end():]))

    if body is None:
        return None
    return (prefix + " by\n" + body).rstrip() + "\n"

def extract_lean(text: str, formal_statement: str) -> str:
    """Extract Lean 4 code from a raw model response. Tries the proven legacy
    fence-pairing extraction first -- byte-identical to what already produced Goedel's
    and DeepSeek's finalized, Lean-verified results, confirmed by direct comparison
    against every recorded row (2026-07-17); do not disturb it. Only falls back to
    name-anchored extraction when the legacy path fails outright (no usable 'theorem' in
    its result) -- specifically Kimina's failure mode (nested/echoed fences), which the
    legacy path already correctly flags as unusable, so the fallback only ever activates
    on cases that would otherwise be a hard failure. See _extract_lean_legacy and
    _extract_lean_anchored for why each exists."""
    legacy = _extract_lean_legacy(text, formal_statement)
    # "succeeds" means generation_prefilter would accept it: has a real theorem AND isn't
    # carrying an echoed instruction that merely mentions sorry/admit (found via Kimina's
    # mathd_algebra_24, 2026-07-17: legacy's fenced match technically contained
    # "theorem ", but also verbatim-included our own prompt_addendum text warning against
    # sorry/admit, which then false-triggered generation_prefilter's own safety regex).
    legacy_ok = "theorem " in legacy and not re.search(r"\b(?:sorry|admit)\b", legacy)
    if legacy_ok:
        return legacy
    anchored = _extract_lean_anchored(text, formal_statement)
    return anchored if anchored is not None else legacy

def strip_lean_comments(code: str) -> str:
    """Remove -- line comments and nested /- -/ block comments before tactic scanning.
    Without this, English prose inside a comment (e.g. "instead use trivial") gets
    misread as a real tactic invocation -- several Lean tactic names (use, apply, show,
    change, decide, ...) are also ordinary English words. Confirmed empirically: 47%
    of real calibration proofs contain comments, so this isn't an edge case. Does not
    attempt to respect string literals -- string literals containing -- or /- are rare
    in generated tactic proofs, not worth the added complexity here."""
    result = []
    i, depth, n = 0, 0, len(code)
    while i < n:
        if code[i:i + 2] == "/-":
            depth += 1
            i += 2
            continue
        if depth > 0 and code[i:i + 2] == "-/":
            depth -= 1
            i += 2
            continue
        if depth > 0:
            i += 1
            continue
        if code[i:i + 2] == "--":
            newline = code.find("\n", i)
            if newline == -1:
                break
            i = newline
            continue
        result.append(code[i])
        i += 1
    return "".join(result)


# VERBATIM from mospe_navi.py. These two decide outcome_state, which is the
# dependent variable in W1 and the cost unit in W2: 'truncated' means the model hit
# the token budget and Lean never ran, 'format_error' means no usable Lean was
# produced, and only what survives both reaches the verifier. Re-deriving them here
# would silently redefine what a failure is, and the 83 roots were classified under
# exactly this logic.
def has_disallowed_placeholder(code: str) -> bool:
    """Whole-word sorry/admit check over CODE WITH COMMENTS STRIPPED. A naive raw-text
    regex would false-positive on a model's own comment merely mentioning the words
    (e.g. `-- do not use sorry here`) exactly as it did on an echoed prompt instruction
    before extract_lean's grafting fix -- stripping comments first (same helper
    tactic_families already uses) closes that class of false positive everywhere the
    check is made, not just for the one echo case that happened to be found."""
    return bool(re.search(r"\b(?:sorry|admit)\b", strip_lean_comments(code)))


def generation_prefilter(response: dict[str, Any], code: str) -> str | None:
    """Return a terminal non-Lean outcome, or None when Lean should check the proof."""
    choice = response["choices"][0]
    if choice.get("finish_reason") == "length":
        return "truncated"
    if has_disallowed_placeholder(code):
        return "format_error"
    content = choice["message"]["content"]
    fenced = re.findall(r"```(?:lean4|lean)?\s*(.*?)```", content, flags=re.DOTALL | re.IGNORECASE)
    if not any("theorem " in block or "import Mathlib" in block for block in fenced):
        return "format_error"
    if "theorem " not in code:
        return "format_error"
    return None


def error_class(state: str, lean_stdout: str | None, lean_stderr: str | None) -> str:
    """Coarse failure taxonomy over a failed attempt's outcome + Lean output. Order
    matters: linarith/nlinarith messages also contain 'unsolved goals', so tactic-
    specific classes are checked first. Truncation is a generation failure (no Lean
    output at all), classified from state alone."""
    if state == "truncated":
        return "truncated"
    text = (lean_stdout or "") + (lean_stderr or "")
    # 'nlinarith failed' contains 'linarith failed' as a substring -- longer match first
    if "nlinarith failed" in text:
        return "nlinarith_failed"
    if "linarith failed" in text:
        return "linarith_failed"
    if "unknown constant" in text or "unknown identifier" in text:
        return "unknown_identifier"
    if "type mismatch" in text:
        return "type_mismatch"
    if "timeout" in text.lower() or "deterministic" in text:
        return "timeout"
    if "unsolved goals" in text:
        return "unsolved_goals"
    if "simp" in text and "failed" in text:
        return "simp_failed"
    return "other"
