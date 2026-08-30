"""Goedel-Prover-V2 native self-correction format, ported from the official repo
(vendor/Goedel-Prover-V2/src/utils.py, functions get_error_str and
DeepSeekCoTHandler.generate_correction_prompt) on 2026-08-27.

This resolves gate G1: the native format did not need to be guessed from the model
card, it is in the vendored official inference code.

Two disclosed deviations from the official code, both forced by our harness:

  1. Error positions. The official pipeline compiles the FULL file (imports included)
     so REPL message line numbers are relative to that file. Our REPL wrapper strips
     import lines before submitting, so positions are relative to the import-stripped
     body. We therefore build the <error> block against exactly the string that was
     submitted to the REPL (see submitted_code), which keeps the markers correct.

  2. Roots with no usable structured compiler errors. 39 of the 83 primary roots have
     none: 32 truncated, 6 verifier timeouts, and 1 clipped/unparseable stdout record
     (imo_1974_p3). For those the native <error> representation does not exist. See
     feedback_kind below. The eval-40 E-eligible count is therefore 21, not 22.
"""

from __future__ import annotations

import json
import re
from typing import Any


# ---------------------------------------------------------------- official port


def get_error_str(code: str, errors: list[dict[str, Any]], error_thres: bool = True) -> str:
    """VERBATIM port of vendor/Goedel-Prover-V2/src/utils.py::get_error_str.
    error_thres=True matches the official default (inference.py --error_thres)."""
    err_str = ""
    code_lines = code.split('\n')
    token_lengths = [len(line) + 1 for line in code_lines]

    error_num_thres = 8 if error_thres else len(errors)

    for i, error in enumerate(errors[:error_num_thres]):
        start_line = error['pos']['line'] - 1
        start_col = error['pos']['column']

        if error['endPos'] is None:
            end_line = start_line
            end_col = len(code_lines[start_line])
        else:
            end_line = error['endPos']['line'] - 1
            end_col = error['endPos']['column']

        err_str += f"\nError {i + 1}:\n"
        err_str += f"\nCorresponding Code:\n```lean4\n"

        error_code = ""
        for ii in range(-4, 0):
            if start_line + ii >= 0:
                error_code += f"{code_lines[start_line + ii]}\n"
        if start_line != end_line:
            error_code += code_lines[start_line][:start_col] + "<error>" + code_lines[start_line][start_col:] + "\n"

            if not error_thres:
                for j in range(start_line + 1, end_line):
                    error_code += f"{code_lines[j]}\n"
            else:
                show_line = 6
                for j in range(start_line + 1, min(end_line, start_line + show_line)):
                    error_code += f"{code_lines[j]}\n"
                if end_line > start_line + show_line:
                    leading_spaces = len(code_lines[j]) - len(code_lines[j].lstrip(' '))
                    error_code += "\n" + " " * leading_spaces + "... --[Truncated]-- ...\n"

            error_code += code_lines[end_line][:end_col] + "</error>" + code_lines[end_line][end_col:] + "\n"
        else:
            error_code += code_lines[start_line][:start_col] + "<error>" + code_lines[start_line][start_col:end_col] + "</error>" + code_lines[start_line][end_col:] + "\n"
        if end_line + 1 < len(code_lines):
            error_code += f"{code_lines[end_line + 1]}\n"

        err_str += error_code
        err_str += f"\n```\n"
        err_str += f"\nError Message: {error['data']}\n"

    if len(errors) > error_num_thres:
        err_str += f"\n... [Omitted {len(errors) - error_num_thres} more errors] ...\n"

    return err_str


# The official correction turn, verbatim from generate_correction_prompt.
CORRECTION_TURN = (
    "The proof (Round {prev_round}) is not correct. Following is the compilation error "
    "message, where we use <error></error> to signal the position of the error.\n\n{errors}"
    "\n\nBefore producing the Lean 4 code to formally prove the given theorem, provide a "
    "detailed analysis of the error message."
)


# ------------------------------------------------- roots with no compiler errors
#
# PROVISIONAL -- must be frozen in spec/frozen_spec.yaml before primary generation.
# Both strings are uniform across every affected root: no per-failure-class wording,
# so treatment never varies with the grouping Analysis 3 measures.

FEEDBACK_TRUNCATED = (
    "The proof (Round {prev_round}) is not correct. The response reached the "
    "generation token budget before producing a complete Lean 4 proof, so it was "
    "never submitted to the compiler and no compilation error message is available."
    "\n\nBefore producing the Lean 4 code to formally prove the given theorem, provide a "
    "detailed analysis of why the previous attempt did not terminate."
)

FEEDBACK_VERIFIER_TIMEOUT = (
    "The proof (Round {prev_round}) is not correct. The Lean compiler did not finish "
    "checking it within the {timeout} second limit, so no compilation error message is "
    "available."
    "\n\nBefore producing the Lean 4 code to formally prove the given theorem, provide a "
    "detailed analysis of why the previous attempt was too expensive to check."
)


def feedback_kind(outcome_state: str, errors: list[dict[str, Any]],
                  lean_stdout: str | None = None) -> str:
    """Which feedback representation a root gets. Recorded on every branch record so
    the Arm E analysis can be restricted to roots with a real <error> block.

    Four kinds, and the last one is easy to lose. A root whose stored lean_stdout is
    non-empty but does not parse as REPL JSON produced REAL Lean errors that we simply
    cannot read -- imo_1974_p3 is clipped at exactly 8000 chars mid-expression, so its
    goal state destroyed the JSON envelope. Folding that into 'verifier_timeout' would
    bill a root with genuine errors as a timeout in W2's failure-state economics, and
    timeouts have very different cost physics (180 s of verifier wall time, ~0 tokens).
    It is E-ineligible either way: there is no message list to place markers from."""
    if outcome_state == "truncated":
        return "budget_exhausted"
    if errors:
        return "native_error"
    if lean_stdout:
        return "stdout_unparseable"
    return "verifier_timeout"


def build_feedback(outcome_state: str, code: str, errors: list[dict[str, Any]],
                   prev_round: int = 0, timeout: int = 180,
                   lean_stdout: str | None = None,
                   allow_placeholder: bool = False) -> tuple[str, str, str]:
    """Returns (feedback_text, error_block, kind). error_block is "" when no native
    <error> representation exists.

    The plan FORBIDS synthesising placeholder feedback for Arm E (v6 01 Sec.6, 05
    Gate 3): a placeholder-fed E is Arm C with extra words and controls for nothing.
    The FEEDBACK_TRUNCATED / FEEDBACK_VERIFIER_TIMEOUT branches below would otherwise
    make E constructible on all 40 eval roots, which is exactly the design the plan
    prohibits -- so they are locked behind allow_placeholder and must never be enabled
    for confirmatory E jobs."""
    kind = feedback_kind(outcome_state, errors, lean_stdout)
    if kind == "native_error":
        block = get_error_str(code, errors)
        return CORRECTION_TURN.format(prev_round=prev_round, errors=block), block, kind
    if not allow_placeholder:
        raise ValueError(
            f"refusing to synthesise placeholder feedback for kind={kind!r}: Arm E is "
            f"a native-feedback-only positive control (v6 01 Sec.6 / 05 Gate 3)"
        )
    if kind == "budget_exhausted":
        return FEEDBACK_TRUNCATED.format(prev_round=prev_round), "", kind
    return FEEDBACK_VERIFIER_TIMEOUT.format(prev_round=prev_round, timeout=timeout), "", kind


# ---------------------------------------------------------------- REPL adapters


def submitted_code(lean_file_text: str) -> str:
    """Reproduce exactly what wsl_lean_repl.LeanReplWorker.verify sends to the REPL,
    so error line/column positions line up with the code we show the model."""
    return re.sub(r"(?m)^\s*import\s+[^\n]+\n?", "", lean_file_text).lstrip()


def repl_errors(lean_stdout: str | None) -> list[dict[str, Any]]:
    """Pull severity=='error' messages out of a stored REPL response."""
    if not lean_stdout:
        return []
    try:
        payload = json.loads(lean_stdout)
    except json.JSONDecodeError:
        return []
    return [m for m in payload.get("messages", []) if m.get("severity") == "error"]


# ------------------------------------------------------------- arm builders: GONE
#
# The three builders that used to live here (arm_a_regenerate, arm_b_full_repair,
# arm_c_history_ablated) were written before the v6 arm scheme existed and their
# names actively mislead: arm_b_full_repair built what v6/v7 call Arm E, and
# arm_c_history_ablated built an arm v6 dropped entirely. Message assembly now lives
# in exactly one place, src/prompts.py, so the Gate 5 prompt-diff audit is auditing
# the same code path that generation uses. This module keeps only the native
# FEEDBACK TEXT (get_error_str / CORRECTION_TURN / build_feedback), which is what it
# was ported from the official repo to provide.
