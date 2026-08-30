"""The frozen prior-attempt textual anchoring proxy.  W1 co-primary A.

v7 `02` Sec.5 defines it:

    S(branch, root) = 1 - lev(model_tokens(branch), model_tokens(root))
                          / max(len(model_tokens(branch)), len(model_tokens(root)))

    T0 = mean[ S(C, root) - S(A, root) ]
    T1 = mean[ S(D, root) - S(B, root) ]

Three things the plan is explicit about, and one it leaves to us.

EXPLICIT -- do not strip comments, prose, or malformed Lean. S is computed over the
model's ENTIRE completion, not over extracted Lean. Stripping would quietly change what
"textual retention" means, and a model that keeps the prose plan but rewrites the proof
is a real and interesting case that stripping would erase.

EXPLICIT -- model_tokens means the model's OWN tokenizer, obtained from the serving
process (`POST /tokenize`), not a whitespace split and not a third-party BPE. A token is
the unit the model actually emits.

EXPLICIT -- the metric is a proxy. High S evidences anchoring. Low S does NOT prove the
model ignored the prior attempt: a model can read prior context and rewrite completely.
Report it as "prior-attempt textual anchoring", never as "artifact use".

OURS -- v7 says "after frozen line-ending and whitespace normalization" without saying
what that is. NORMALIZE_ID below pins it. It is deliberately minimal: line endings and
trailing whitespace only. Internal indentation is NOT collapsed, because indentation is
syntactically load-bearing in Lean 4 and collapsing it would make two structurally
different proofs look identical.
"""

from __future__ import annotations

import json
import urllib.error
import urllib.request
from typing import Sequence

from rapidfuzz.distance import Levenshtein

METRIC_ID = "prior_attempt_textual_anchoring_v1"
NORMALIZE_ID = "lf_endings_and_trailing_ws_v1"


def normalize(text: str) -> str:
    """FROZEN. CRLF/CR -> LF, drop trailing spaces and tabs on each line, strip the
    document's leading and trailing whitespace. Nothing else."""
    t = text.replace("\r\n", "\n").replace("\r", "\n")
    t = "\n".join(line.rstrip(" \t") for line in t.split("\n"))
    return t.strip()


def similarity(a: Sequence[int], b: Sequence[int]) -> float:
    """1 - normalized Levenshtein over token-ID sequences. Symmetric, in [0, 1].

    Two empty sequences score 1.0. That case cannot arise from a real completion, but
    leaving it as a ZeroDivisionError would turn a degenerate branch into a crash three
    hours into an analysis run."""
    n = max(len(a), len(b))
    if n == 0:
        return 1.0
    return 1.0 - Levenshtein.distance(a, b) / n


class ServerTokenizer:
    """POST /tokenize against the frozen llama.cpp serving process.

    Deliberately has no fallback. A silent switch to some other tokenizer would change
    every S in the paper while every assertion still passed."""

    def __init__(self, base_url: str = "http://127.0.0.1:8080", timeout: int = 60):
        self.base_url = base_url.rstrip("/")
        self.timeout = timeout
        self._cache: dict[str, list[int]] = {}

    def probe(self) -> tuple[bool, str]:
        """(reachable, detail). Confirms the endpoint is llama.cpp's /tokenize and not
        some unrelated process that happens to hold the port."""
        try:
            toks = self._post("probe")
        except urllib.error.HTTPError as exc:
            return False, f"HTTP {exc.code} from {self.base_url}/tokenize"
        except urllib.error.URLError as exc:
            return False, f"no listener at {self.base_url} ({exc.reason})"
        except Exception as exc:  # noqa: BLE001 -- report anything, never guess
            return False, f"{type(exc).__name__}: {exc}"
        if not toks:
            return False, "/tokenize returned no tokens"
        return True, f"/tokenize live, {len(toks)} token(s) for a probe string"

    def _post(self, content: str) -> list[int]:
        req = urllib.request.Request(
            f"{self.base_url}/tokenize",
            data=json.dumps({"content": content}).encode("utf-8"),
            headers={"Content-Type": "application/json"},
        )
        with urllib.request.urlopen(req, timeout=self.timeout) as resp:
            return json.loads(resp.read().decode("utf-8"))["tokens"]

    def tokens(self, text: str, normalized: bool = False) -> list[int]:
        """Normalizes first unless told the text already is. Cached by exact string."""
        key = text if normalized else normalize(text)
        if key not in self._cache:
            self._cache[key] = self._post(key)
        return self._cache[key]
