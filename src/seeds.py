"""The seed rule. Declared, not computed.

    root_index   = rank of root_id in the sorted list of the 83 root_ids (0-based)
    block 1 seed = 2_000_000 + root_index      ->  2000000 .. 2000082
    block 2 seed = 3_000_000 + root_index      ->  3000000 .. 3000082

ONE SEED PER (root, block), SHARED BY EVERY ARM OF THAT ROOT. That is the part that
matters. C - A is a paired within-root contrast only if C and A were drawn under the
same seed; give them different seeds and the contrast becomes two independent draws and
the pairing buys nothing (v7 `02` Sec.3: "same root; same seed in a block").

Why these bases. CoLM's entire seed history is a stride-1000 lattice from 100030 to
1079030 -- 782 distinct values, all ending in 030. Everything here is above 2,000,000,
so non-collision with any prior run is verifiable by inspection rather than by trusting
an offset calculation. Separate bases per block rather than block2 = block1 + offset for
the same reason: nothing to get wrong.
"""

from __future__ import annotations

BLOCK_BASE = {1: 2_000_000, 2: 3_000_000}
SEED_RULE_ID = "block_base_plus_sorted_root_index_v1"


def seed_for(root_id: str, root_ids: list[str], block: int = 1) -> int:
    """root_ids is the full canonical root list; order does not need to be pre-sorted."""
    if block not in BLOCK_BASE:
        raise ValueError(f"unknown seed block {block!r}; known: {sorted(BLOCK_BASE)}")
    ordered = sorted(root_ids)
    try:
        idx = ordered.index(root_id)
    except ValueError:
        raise ValueError(f"{root_id!r} is not in the canonical root list") from None
    return BLOCK_BASE[block] + idx


def all_seeds(root_ids: list[str], block: int = 1) -> dict[str, int]:
    ordered = sorted(root_ids)
    return {rid: BLOCK_BASE[block] + i for i, rid in enumerate(ordered)}
