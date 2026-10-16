#!/usr/bin/env python3
# ==============================================================================
# File: stepmodel.py
# Description: Where ca-rule110's kernel work actually goes, counted rather
#   than assumed.
#
#   The submission note states that the setup "costs a few hundred steps
#   against the hundreds of thousands the stepping costs", and declines to
#   optimise it on that basis. The judged cases say otherwise: they ask for
#   0, 1, 2, 4, 8 and 13 steps, so the stepping is at most 13 iterations of
#   eight Nat operations. Everything else is the initial row.
#
#   This counts both under the same model the partition work used: one step
#   per Nat primitive the kernel implements on GMP integers, one per
#   unfolding of a recursive definition, one per list constructor match.
#
# Usage: py stage2/ca-rule110/stepmodel.py
# Author: Amey Thakur
# License: CC BY 4.0
# ==============================================================================

from __future__ import annotations

import json
import pathlib

W = 256
MASK = (1 << W) - 1
HERE = pathlib.Path(__file__).resolve().parent


class Count:
    def __init__(self) -> None:
        self.n = 0

    def op(self, k: int = 1) -> None:
        self.n += k


def mix32_cost(c: Count) -> None:
    """x^(x>>16); *K; &M  twice, then x^(x>>16).

    Each of shift, xor, multiply and mask is one Nat primitive."""
    c.op(4)     # x >> 16, x ^ _, * K, & 0xFFFFFFFF
    c.op(4)     # the same again
    c.op(2)     # x >> 16, x ^ _
    c.op(1)     # the trailing & 0xFFFFFFFF


def setup_cost_spec() -> int:
    """`encodeRow (initRowFor seed)`, as the current entry computes it."""
    c = Count()
    for i in range(W):
        c.op(1)                      # one unfolding of the row builder
        if i < 2:
            c.op(1)                  # the i == 0 / i == 1 branch
        else:
            c.op(2)                  # seed + (i+1) * PHI
            mix32_cost(c)
            c.op(2)                  # >> 31, & 1
        c.op(1)                      # one cons
    for _ in range(W):
        c.op(1)                      # one unfolding of the encoder
        c.op(1)                      # one list constructor match
        c.op(2)                      # 2 * acc, + bit
    return c.n


def setup_cost_direct() -> int:
    """The same row packed straight into a Nat, with no list in between."""
    c = Count()
    for i in range(W):
        c.op(1)                      # one unfolding
        if i < 2:
            c.op(1)
        else:
            c.op(2)
            mix32_cost(c)
            c.op(2)
        c.op(2)                      # bit <<< i, ||| acc
    return c.n


def setup_cost_lanes() -> int:
    """All 256 lanes mixed at once inside one wide Nat.

    Lane j holds `seed + (j+1)*PHI` in its own 64-bit field. A shift by a
    multiple of the lane width moves whole lanes, a multiply by a scalar
    distributes over lanes because each product stays inside its field, and
    a mask clears what crosses. So the whole of mix32 is a fixed number of
    Nat operations, independent of how many lanes there are.
    """
    c = Count()
    c.op(3)                          # build the ramp seed + (j+1)*PHI, packed
    for _ in range(3):               # the three xor-shift rounds
        c.op(1)                      # >> 16 within lanes
        c.op(1)                      # & lane mask, to stop the crossing bits
        c.op(1)                      # ^
    for _ in range(2):               # the two multiplies
        c.op(1)                      # * K  (distributes over lanes)
        c.op(1)                      # & the 32-bit-per-lane mask
    c.op(2)                          # >> 31 within lanes, & 1 per lane
    c.op(6)                          # compact one bit per lane down to one bit per position
    c.op(2)                          # force bit 0 set and bit 1 clear
    return c.n


def step_cost(t: int) -> int:
    """`pStep` is eight Nat operations; `pIter` adds one unfolding each."""
    return t * 9


def main() -> int:
    cases = json.loads((HERE / "cases.json").read_text(encoding="utf-8"))
    judged = sorted({c["steps"] for c in cases["cases"]})
    print(f"  judged step counts in cases.json: {judged}")
    print(f"  the judge uses six hidden cases drawn from this range\n")

    spec, direct, lanes = (setup_cost_spec(), setup_cost_direct(),
                           setup_cost_lanes())
    print(f"  setup, via the spec's list   {spec:>8,} steps")
    print(f"  setup, packed directly       {direct:>8,} steps")
    print(f"  setup, 256 lanes at once     {lanes:>8,} steps")
    print()
    print(f"  {'steps':>6}  {'stepping':>9}  {'now':>9}  {'direct':>9}  {'lanes':>9}")
    for t in judged:
        s = step_cost(t)
        print(f"  {t:>6}  {s:>9,}  {s + spec:>9,}  {s + direct:>9,}  "
              f"{s + lanes:>9,}")

    worst = max(judged)
    tot_now = sum(step_cost(t) + spec for t in judged)
    tot_dir = sum(step_cost(t) + direct for t in judged)
    tot_lan = sum(step_cost(t) + lanes for t in judged)
    print()
    print(f"  over the six distinct step counts:")
    print(f"      now     {tot_now:>8,}")
    print(f"      direct  {tot_dir:>8,}   {tot_now / tot_dir:.2f}x better")
    print(f"      lanes   {tot_lan:>8,}   {tot_now / tot_lan:.1f}x better")
    print()
    print(f"  the stepping is {step_cost(worst)} steps at its worst, "
          f"{step_cost(worst) / (spec + step_cost(worst)) * 100:.1f}% of the "
          f"work at t={worst}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
