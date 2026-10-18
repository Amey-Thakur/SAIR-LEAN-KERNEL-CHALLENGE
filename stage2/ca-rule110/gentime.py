#!/usr/bin/env python3
# ==============================================================================
# File: gentime.py
# Description: Emits a proof-free Lean implementation of the packed initial row
#   and times the kernel reducing it, against the specification's own route.
#
#   Why before the proof. The remaining Lean work is a few hundred lines, and
#   all of it is wasted if the kernel does not actually reduce the packed form
#   faster. Two cost models have already been wrong in opposite directions on
#   this repository's problems, so the implementation is measured first and
#   proved second. Nothing here is submitted and nothing here is proved: a
#   `rfl` against a value computed in Python is the check, and the clock is the
#   result.
#
#   The lane width is 64, not the 128 that lanes.py uses. lanes.py follows the
#   specification and masks to 32 bits after each multiply, so its widest
#   intermediate is 41 + 32 = 73 bits. Masking before the multiply instead is
#   the same number, because (a % 2^m * c) % 2^m = (a * c) % 2^m, and it caps
#   the widest intermediate at 32 + 31 = 63. That halves every operand in the
#   hot path.
#
# Usage: py stage2/ca-rule110/gentime.py --emit > LaneTime.lean
#        py stage2/ca-rule110/gentime.py --check
# Author: Amey Thakur
# License: CC BY 4.0
# ==============================================================================

from __future__ import annotations

import argparse
import sys

sys.set_int_max_str_digits(200_000)

CELLS = 256
LANE = 64
PHI = 0x9E3779B9
A1 = 0x7FEB352D
A2 = 0x846CA68B


def pack(width: int, values: list[int]) -> int:
    """Sum of values[k] << (width * k). The additive packing, in Python."""
    out = 0
    for k, v in enumerate(values):
        out |= v << (width * k)
    return out


ONES = pack(LANE, [1] * CELLS)
RAMP = pack(LANE, [i + 1 for i in range(CELLS)])
M32P = pack(LANE, [0xFFFFFFFF] * CELLS)

# The eight merge masks. Round r reads lanes of width LANE*2^r holding 2^r
# bits and writes lanes of twice that width holding twice as many, so its mask
# keeps the low 2^r bits of every field of width LANE*2^(r+1).
ROUNDS = []
for r in range(8):
    width = LANE << r
    held = 1 << r
    lanes = CELLS >> (r + 1)
    ROUNDS.append({
        "shift": width,
        "mul": 1 << held,
        "mask": pack(2 * width, [(1 << held) - 1] * lanes),
    })


# ------------------------------------------------- the locked specification --
def ca_mix32(x: int) -> int:
    x = ((x ^ (x >> 16)) * A1) & 0xFFFFFFFF
    x = ((x ^ (x >> 15)) * A2) & 0xFFFFFFFF
    return (x ^ (x >> 16)) & 0xFFFFFFFF


def spec_row(seed: int) -> int:
    """encodeRow (initRowFor seed), straight from Spec.lean."""
    out = 0
    for i in range(CELLS):
        if i == 0:
            bit = 1
        elif i == 1:
            bit = 0
        else:
            bit = (ca_mix32(seed + (i + 1) * PHI) >> 31) & 1
        out |= bit << i
    return out


# ------------------------------------------------------- the packed design ---
def packed_row(seed: int) -> int:
    """The same row, computed on all 256 cells at once."""
    x = ONES * seed + RAMP * PHI
    # every mask below is lane-local, which a single literal could not be
    x = ((x ^ ((x >> 16) & M32P)) & M32P) * A1
    x = x & M32P
    x = ((x ^ ((x >> 15) & M32P)) & M32P) * A2
    x = x & M32P
    x = (x ^ ((x >> 16) & M32P)) & M32P
    bits = (x >> 31) & ONES
    for rd in ROUNDS:
        bits = (bits & rd["mask"]) \
            + (((bits >> rd["shift"]) & rd["mask"]) * rd["mul"])
    # cells 0 and 1 are fixed by the specification, to true and false
    return (bits >> 2) * 4 + 1


SEEDS = [0, 1, 2, 3, 123456789, 0x9E3779B9, 0xFFFFFFFF, 0x7FFFFFFF]

# Prefixes of the packed computation. The full row is 5.9x faster than the
# specification route, against an operation count that predicted 54x, so the
# width of the operands is being charged for and the question is which part
# pays it. These stop early and are timed separately.
PREFIX = ["ramp", "mix", "bits", "full"]


def packed_prefix(seed: int, upto: str) -> int:
    x = ONES * seed + RAMP * PHI
    if upto == "ramp":
        return x
    x = ((x ^ ((x >> 16) & M32P)) & M32P) * A1
    x = x & M32P
    x = ((x ^ ((x >> 15) & M32P)) & M32P) * A2
    x = x & M32P
    x = (x ^ ((x >> 16) & M32P)) & M32P
    if upto == "mix":
        return x
    bits = (x >> 31) & ONES
    if upto == "bits":
        return bits
    for rd in ROUNDS:
        bits = (bits & rd["mask"])             + (((bits >> rd["shift"]) & rd["mask"]) * rd["mul"])
    return (bits >> 2) * 4 + 1


def check() -> None:
    bad = 0
    import random
    rng = random.Random(20261017)
    trial = list(SEEDS) + [rng.randrange(0, 1 << 32) for _ in range(2000)]
    for s in trial:
        if packed_row(s) != spec_row(s):
            bad += 1
            if bad <= 3:
                print(f"MISMATCH seed={s}")
    print(f"checked {len(trial)} seeds, {bad} mismatches, lane width {LANE}")
    if bad:
        raise SystemExit(1)


def emit() -> None:
    p = print
    p("import Spec")
    p("")
    p("/-!")
    p("# Timing the packed initial row, with no proof at all")
    p("")
    p("This file is not the submission and proves nothing. It exists to answer")
    p("one question before the proof is written: does the kernel actually")
    p("reduce the packed form faster than the specification's own route. The")
    p("constants are literals so that building them costs nothing and the")
    p("measurement is of the arithmetic alone.")
    p("-/")
    p("")
    p("namespace LaneTime")
    p("")
    p(f"def ONES : Nat := {hex(ONES)}")
    p(f"def RAMP : Nat := {hex(RAMP)}")
    p(f"def M32P : Nat := {hex(M32P)}")
    for r, rd in enumerate(ROUNDS):
        p(f"def MK{r} : Nat := {hex(rd['mask'])}")
    p("")
    p("/-- The initial row, all 256 cells at once. -/")
    p("def packedRow (seed : Nat) : Nat :=")
    p(f"  let x := ONES * seed + RAMP * {PHI}")
    p(f"  let x := ((x ^^^ ((x >>> 16) &&& M32P)) &&& M32P) * {A1}")
    p("  let x := x &&& M32P")
    p(f"  let x := ((x ^^^ ((x >>> 15) &&& M32P)) &&& M32P) * {A2}")
    p("  let x := x &&& M32P")
    p("  let x := (x ^^^ ((x >>> 16) &&& M32P)) &&& M32P")
    p("  let b := (x >>> 31) &&& ONES")
    for r, rd in enumerate(ROUNDS):
        p(f"  let b := (b &&& MK{r}) "
          f"+ (((b >>> {rd['shift']}) &&& MK{r}) * {rd['mul']})")
    p("  (b >>> 2) * 4 + 1")
    p("")
    for up in PREFIX[:-1]:
        p(f"/-- The packed computation stopped after `{up}`. -/")
        p(f"def prefix_{up} (seed : Nat) : Nat :=")
        p(f"  let x := ONES * seed + RAMP * {PHI}")
        if up != "ramp":
            p(f"  let x := ((x ^^^ ((x >>> 16) &&& M32P)) &&& M32P) * {A1}")
            p("  let x := x &&& M32P")
            p(f"  let x := ((x ^^^ ((x >>> 15) &&& M32P)) &&& M32P) * {A2}")
            p("  let x := x &&& M32P")
            p("  let x := (x ^^^ ((x >>> 16) &&& M32P)) &&& M32P")
        if up == "bits":
            p("  (x >>> 31) &&& ONES")
        else:
            p("  x")
        p("")
    p("/-- The specification's own route, for the same row. -/")
    p("def specRow (seed : Nat) : Nat :=")
    p("  encodeRow (initRowFor seed)")
    p("")
    p("end LaneTime")


def emit_cases(which: str) -> None:
    """One self-contained file per route, so no olean has to be built and the
    two measurements differ in nothing but the function under test."""
    p = print
    if which != "none":
        emit()
    else:
        p("import Spec")
    p("set_option maxRecDepth 8000000")
    p("set_option maxHeartbeats 0")
    p("namespace Bench")
    if which == "packed":
        for i, s in enumerate(SEEDS):
            p(f"theorem b{i} : LaneTime.packedRow {s} "
              f"= {hex(spec_row(s))} := by rfl")
    elif which == "spec":
        for i, s in enumerate(SEEDS):
            p(f"theorem b{i} : LaneTime.specRow {s} "
              f"= {hex(spec_row(s))} := by rfl")
    elif which in PREFIX:
        for i, s in enumerate(SEEDS):
            p(f"theorem b{i} : LaneTime.prefix_{which} {s} "
              f"= {hex(packed_prefix(s, which))} := by rfl")
    p("end Bench")


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--emit", action="store_true")
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--cases",
                    choices=["packed", "spec", "none"] + PREFIX[:-1])
    a = ap.parse_args()
    if a.emit:
        emit()
    elif a.cases:
        emit_cases(a.cases)
    else:
        check()
