#!/usr/bin/env python3
# ==============================================================================
# File: lanes.py
# Description: The initial row computed for all 256 cells at once, inside one
#   wide natural number, and checked against the specification.
#
#   Why. stepmodel.py counts where the entry's kernel work goes: the judged
#   cases ask for at most 13 steps, so the stepping is at most 117 operations
#   and the initial row is 5,348 of the 5,465. The row costs that much because
#   it evaluates a 32-bit mixing hash once per cell, 256 times, and the
#   submission note's claim that the stepping dominates is simply wrong.
#
#   The design. Give every cell a 64-bit lane inside one Nat and hold its
#   32-bit hash state there. Then the whole hash runs on all 256 cells at
#   once, because each operation it uses survives packing:
#
#     * shifting the packed number right by k shifts every lane right by k,
#       and the only damage is the low bits of lane i+1 landing in lane i's
#       upper half, which a mask clears. Each lane carries 32 live bits in a
#       64-bit field precisely so there is somewhere for that to land.
#     * multiplying the packed number by a 32-bit constant multiplies every
#       lane by it, with no carry between lanes, because a 32-bit value times
#       a 32-bit constant is below 2^64 and so stays inside its own field.
#
#   That is the same move as the partition entry: the kernel charges by the
#   operation and not by the width of the operand, so one wide operation
#   replaces 256 narrow ones.
#
#   Nothing here is submitted. This settles the algorithm, so that the Lean
#   proof is the only thing left to get right. Agreement with the
#   specification is checked exhaustively on the judged seeds and on random
#   ones, in both directions.
#
# Usage: py stage2/ca-rule110/lanes.py
# Author: Amey Thakur
# License: CC BY 4.0
# ==============================================================================

from __future__ import annotations

import json
import pathlib
import random

W = 256                 # cells, fixed by the specification
PHI = 0x9E3779B9
A1 = 0x7FEB352D
A2 = 0x846CA68B
M32 = 0xFFFFFFFF

# How wide a lane has to be, which the specification decides and not us.
#
# The hash is applied to `seed + (i+1)*PHI` WITHOUT a mask, and that is below
# 2^32 + 256*2^32 < 2^41. Its first round forms `(x ^ (x >> 16)) * A1` before
# any masking, so the widest intermediate is 41 + 32 = 73 bits. A lane must
# hold that without carrying into its neighbour, and must leave room above it
# for the bits a right shift drags in from the lane above. 128 bits does both.
LANE = 128
RAMP_BITS = 48          # ≥ 41, and ≤ 128-16 so a >>16 cannot reach it
HERE = pathlib.Path(__file__).resolve().parent

ONES = (1 << (LANE * W)) // ((1 << LANE) - 1)   # Σ 2^(128 i)
LIVE = ONES * M32                               # 32 live bits per lane
WIDE = ONES * ((1 << RAMP_BITS) - 1)            # 48 live bits per lane


# ------------------------------------------------- the locked specification --
def ca_mix32(x: int) -> int:
    x = ((x ^ (x >> 16)) * A1) & M32
    x = ((x ^ (x >> 15)) * A2) & M32
    return (x ^ (x >> 16)) & M32


def init_row_for(seed: int) -> list[bool]:
    out = []
    for i in range(W):
        if i == 0:
            out.append(True)
        elif i == 1:
            out.append(False)
        else:
            out.append(bool((ca_mix32(seed + (i + 1) * PHI) >> 31) & 1))
    return out


def encode_row(row: list[bool]) -> int:
    acc = 0
    for b in reversed(row):
        acc = 2 * acc + (1 if b else 0)
    return acc


# ------------------------------------------------------- the lane design -----
class Ops:
    """Counts Nat primitives, so the saving is measured and not asserted."""

    def __init__(self) -> None:
        self.n = 0

    def __call__(self, k: int = 1) -> None:
        self.n += k


def build_ramp(seed: int, op: Ops) -> int:
    """Σ_i (seed + (i+1)*PHI) 2^(64 i), by doubling rather than cell by cell.

    `block(k)` is the ramp for the first 2^k lanes. Doubling it appends a
    copy whose every entry is 2^k steps further along, which is one shift,
    one add and one multiply-add of the constant. Eight doublings reach 256
    lanes, so the ramp costs about 40 operations instead of 256.
    """
    ramp = seed + PHI                    # lane 0, deliberately unmasked
    ones = 1
    op(2)
    width = 1
    while width < W:
        delta = PHI * width
        # the upper copy is the lower one shifted up, plus delta in every lane
        upper = ((ramp + ones * delta) & (ones * ((1 << RAMP_BITS) - 1))) \
            << (LANE * width)
        ramp |= upper
        ones |= ones << (LANE * width)
        op(6)
        width *= 2
    return ramp & WIDE


def lane_mix32(x: int, op: Ops) -> int:
    """ca_mix32 applied to every lane of `x` at once."""
    # The first round runs on the unmasked ramp, so it is the wide one: up to
    # 41 bits in, 73 out of the multiply, masked to 32 only afterwards.
    x = (x ^ ((x >> 16) & WIDE)) & WIDE
    op(3)
    x = (x * A1) & LIVE
    op(2)
    x = (x ^ ((x >> 15) & LIVE)) & LIVE
    op(3)
    x = (x * A2) & LIVE
    op(2)
    x = (x ^ ((x >> 16) & LIVE)) & LIVE
    op(3)
    return x


def compact(bits: int, op: Ops) -> int:
    """Σ b_i 2^(64 i)  ->  Σ b_i 2^i, by halving the lane width six times."""
    # No single shift can do this, because cell i has to travel 127i places
    # and a shift moves everything equally. Merging in PAIRS can: after k
    # rounds the cells sit in groups of 2^k, packed at the bottom of a field
    # of 128*2^k bits. Merging two neighbouring groups leaves the lower one
    # exactly where it is and moves the upper one down by 128*2^k - 2^k,
    # which does not depend on which pair it is. So every round is one
    # uniform shift and two masks, and eight rounds bring 256 cells together.
    width = LANE          # field width holding one group
    held = 1              # cells already packed at the bottom of a field
    while held < W:
        shift = width - held
        bits = (bits & _low_mask(2 * width, held)) \
            | ((bits >> shift) & _high_mask(2 * width, held))
        op(4)
        width *= 2
        held *= 2
    return bits


_MASK_CACHE: dict[tuple[str, int, int], int] = {}


def _repeat(field: int, unit: int, offset: int) -> int:
    """`unit` placed at `offset` inside every `field`-bit slot of the row."""
    key = ("r", field, offset * (1 << 20) + unit.bit_length())
    m = 0
    for base in range(0, LANE * W, field):
        m |= unit << (base + offset)
    return m


def _low_mask(field: int, held: int) -> int:
    """The lower group's cells, which stay where they are."""
    key = ("lo", field, held)
    if key not in _MASK_CACHE:
        _MASK_CACHE[key] = _repeat(field, (1 << held) - 1, 0)
    return _MASK_CACHE[key]


def _high_mask(field: int, held: int) -> int:
    """Where the upper group's cells land once shifted down."""
    key = ("hi", field, held)
    if key not in _MASK_CACHE:
        _MASK_CACHE[key] = _repeat(field, (1 << held) - 1, held)
    return _MASK_CACHE[key]


def pinit_lanes(seed: int, op: Ops | None = None) -> int:
    op = op or Ops()
    x = build_ramp(seed, op)
    x = lane_mix32(x, op)
    bits = (x >> 31) & ONES              # bit 31 of each lane, at its bottom
    op(2)
    packed = compact(bits, op)
    packed = (packed | 1) & ~2           # cell 0 is true, cell 1 is false
    op(2)
    return packed & ((1 << W) - 1)


# ------------------------------------------------------------------ checks ---
def main() -> int:
    bad = []

    cases = json.loads((HERE / "cases.json").read_text(encoding="utf-8"))
    judged = sorted({c["seed"] for c in cases["cases"]})

    seeds = judged + [0, 1, 2, 3, M32, M32 - 1, PHI, A1, A2,
                      0x80000000, 0x7FFFFFFF, 0xFFFF0000, 0x0000FFFF]
    seeds += [random.Random(k).getrandbits(32) for k in range(2000)]
    seeds = list(dict.fromkeys(seeds))
    for s in seeds:
        if encode_row(init_row_for(s)) != pinit_lanes(s):
            bad.append(s)

    print(f"  judged seeds: {judged}")
    print(f"  lane-packed row vs encodeRow(initRowFor .) on {len(seeds)} "
          f"seeds: {'ok' if not bad else f'FAILED on {bad[:4]}'}")

    # every judged case end to end, row and stepping together
    cases = cases["cases"]
    end_to_end = 0
    for c in cases:
        want = c["value"]
        r = pinit_lanes(c["seed"])
        for _ in range(c["steps"]):
            m = (1 << W) - 1
            rl = ((r << 1) | (r >> (W - 1))) & m
            rr = ((r >> 1) | ((r & 1) << (W - 1))) & m
            r = (r | rr) & (m ^ (rl & r & rr))
        if r != want:
            bad.append(("case", c["n"]))
        else:
            end_to_end += 1
    print(f"  every published case reproduced end to end: "
          f"{end_to_end} of {len(cases)}")

    op = Ops()
    pinit_lanes(judged[0], op)
    print()
    print(f"  operations to build the row")
    print(f"      lane-packed        {op.n:>7,}")
    print(f"      the entry today      5,348")
    print(f"      ratio              {5348 / op.n:>7.0f}x")
    print()
    print(f"  the stepping is unchanged at nine operations a step, and the")
    print(f"  judged cases ask for at most thirteen of them.")
    return 1 if bad else 0


if __name__ == "__main__":
    raise SystemExit(main())
