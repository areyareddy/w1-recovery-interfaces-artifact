"""The one generation client. Every step that calls the model goes through here.

Two reasons it exists rather than being inlined per script.

First, the seven W2 resource columns must be captured identically everywhere. llama.cpp
reports prefill and decode separately in `timings` (prompt_n/prompt_ms, predicted_n/
predicted_ms) and it is the separation that carries W2's argument -- the cost gap between
prefill and decode is the finding, and summing them into one "tokens" number erases it.
Capturing that in one place means a later script cannot quietly record six of seven.

Second, the sampler and the serving assumptions are the method. Temperature 0.7 / top_p
0.95 / top_k 40 / min_p 0.05 come from the frozen policy, and cache_prompt=False is sent
explicitly on every request even though the server is already started with
--no-cache-prompt. Belt and braces on purpose: cached and fresh prefill are NOT
bit-identical (confirmed in CoLM via cache_n=0 vs cache_n=211), so a cache hit would
silently break determinism. Every response is checked for cache_n == 0 and the call
fails loudly if the server ever serves a cached prefix.
"""

from __future__ import annotations

import json
import time
import urllib.error
import urllib.request
from dataclasses import dataclass, field
from typing import Any

# Frozen sampler -- CoLM serving policy. Not tunable per step.
SAMPLER = {
    "temperature": 0.7,
    "top_p": 0.95,
    "top_k": 40,
    "min_p": 0.05,
}
MAX_TOKENS = 12288


@dataclass
class Result:
    """One model call. The seven W2 resource fields are the first seven attributes."""
    model_calls: int
    completion_tokens: int
    total_tokens: int
    prefill_tokens: int
    decode_tokens: int
    request_wall_seconds: float
    verifier_wall_seconds: float | None  # filled by the verifier, not here

    completion: str = ""
    finish_reason: str = ""
    seed: int | None = None
    prefill_ms: float = 0.0
    decode_ms: float = 0.0
    cached_tokens: int = 0
    raw_timings: dict[str, Any] = field(default_factory=dict)

    @property
    def prefill_tokens_per_second(self) -> float:
        return 1000.0 * self.prefill_tokens / self.prefill_ms if self.prefill_ms else 0.0

    @property
    def decode_tokens_per_second(self) -> float:
        return 1000.0 * self.decode_tokens / self.decode_ms if self.decode_ms else 0.0


class Client:
    def __init__(self, base_url: str = "http://127.0.0.1:8080", timeout: int = 1800):
        self.base_url = base_url.rstrip("/")
        self.timeout = timeout

    def _post(self, path: str, body: dict) -> dict:
        req = urllib.request.Request(
            self.base_url + path, data=json.dumps(body).encode("utf-8"),
            headers={"Content-Type": "application/json"})
        with urllib.request.urlopen(req, timeout=self.timeout) as resp:
            return json.loads(resp.read().decode("utf-8"))

    def wait_until_ready(self, deadline_seconds: float = 300.0,
                         poll: float = 5.0) -> bool:
        """Poll /tokenize until the server answers. Used to ride out a restart."""
        end = time.time() + deadline_seconds
        while time.time() < end:
            try:
                self._post("/tokenize", {"content": "probe"})
                return True
            except Exception:  # noqa: BLE001
                time.sleep(poll)
        return False

    def chat(self, messages: list[dict[str, str]], seed: int,
             max_tokens: int = MAX_TOKENS, attempts: int = 5,
             backoff: float = 20.0) -> Result:
        """Retries TRANSPORT failures only, waiting for the server to come back between
        tries. A restart therefore costs a pause, not a failed branch.

        Retrying is safe for reproducibility: same prompt, same seed, and Gate 9 showed
        this configuration reproduces byte-identical completions, so a branch generated
        after a restart is the same branch. Non-transport errors -- above all the cached
        prefix guard -- are NOT retried, because repeating them would just hide them."""
        last: Exception | None = None
        for i in range(attempts):
            try:
                return self._chat_once(messages, seed, max_tokens)
            except (urllib.error.URLError, urllib.error.HTTPError, TimeoutError,
                    ConnectionError, OSError) as exc:
                last = exc
                if i == attempts - 1:
                    break
                wait = backoff * (2 ** i)
                print(f"      [generate] {type(exc).__name__}: {exc} -- waiting up to "
                      f"{wait:.0f}s for the server (try {i + 1}/{attempts})", flush=True)
                self.wait_until_ready(deadline_seconds=wait)
        raise RuntimeError(
            f"generation failed after {attempts} attempts; last: "
            f"{type(last).__name__}: {last}") from last

    def _chat_once(self, messages: list[dict[str, str]], seed: int,
                   max_tokens: int) -> Result:
        body = {
            "messages": messages,
            "seed": seed,
            "max_tokens": max_tokens,
            "stream": False,
            "cache_prompt": False,
            **SAMPLER,
        }
        t0 = time.time()
        out = self._post("/v1/chat/completions", body)
        wall = time.time() - t0

        usage = out.get("usage", {})
        timings = out.get("timings", {})
        cached = (usage.get("prompt_tokens_details") or {}).get("cached_tokens", 0)
        cache_n = timings.get("cache_n", 0)
        if cached or cache_n:
            raise RuntimeError(
                f"server reused a cached prefix (cached_tokens={cached}, "
                f"cache_n={cache_n}). Prefill caching breaks bit-identical "
                f"reproduction; restart with --no-cache-prompt."
            )

        choice = out["choices"][0]
        return Result(
            model_calls=1,
            completion_tokens=usage.get("completion_tokens", 0),
            total_tokens=usage.get("total_tokens", 0),
            prefill_tokens=timings.get("prompt_n", usage.get("prompt_tokens", 0)),
            decode_tokens=timings.get("predicted_n", usage.get("completion_tokens", 0)),
            request_wall_seconds=wall,
            verifier_wall_seconds=None,
            completion=choice["message"]["content"],
            finish_reason=choice.get("finish_reason", ""),
            seed=seed,
            prefill_ms=timings.get("prompt_ms", 0.0),
            decode_ms=timings.get("predicted_ms", 0.0),
            cached_tokens=cached,
            raw_timings=timings,
        )
