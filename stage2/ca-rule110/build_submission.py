#!/usr/bin/env python3
# ==============================================================================
# File: build_submission.py
# Description: Assembles Submission.lean from the verified lane development and
#   the existing packed stepping, with the wide constants emitted as literals.
#
#   The change to the entry is surgical. The live submission already proves the
#   packed Rule 110 step against the specification's list step; what it does
#   not do is build the initial row, which stepmodel.py counts at 5,348 of the
#   entry's 5,465 operations. Only that argument is replaced. Every lemma about
#   the rotations, the step and the iteration is carried over untouched.
#
#   The constants are literals and not computed. A mask built from the
#   recursive definition would cost operations at reduction time, and the
#   gather is already the larger half of the work; LaneProbe.lean checks that
#   the kernel can verify a literal against its packed form by `rfl`, at both
#   sizes the design needs, so the masks cost nothing where it matters.
#
# Usage: py stage2/ca-rule110/build_submission.py
# Author: Amey Thakur
# License: CC BY 4.0
# ==============================================================================

from __future__ import annotations

import pathlib
import re
import sys

sys.set_int_max_str_digits(200_000)

HERE = pathlib.Path(__file__).resolve().parent
CELLS = 256
LANE = 64
PHI = 0x9E3779B9
A1 = 0x7FEB352D
A2 = 0x846CA68B


def pack(width: int, values: list[int]) -> int:
    out = 0
    for k, v in enumerate(values):
        out |= v << (width * k)
    return out


ONES = pack(LANE, [1] * CELLS)
RAMP = pack(LANE, [i + 1 for i in range(CELLS)])
M32P = pack(LANE, [0xFFFFFFFF] * CELLS)

# Round r reads lanes of width LANE*2^r holding 2^r bits and writes lanes of
# twice that width holding twice as many.
ROUNDS = []
for r in range(8):
    ROUNDS.append({
        "r": r,
        "W": LANE << r,
        "twoW": LANE << (r + 1),
        "held": 1 << r,
        "lanes": CELLS >> (r + 1),
        "mask": pack(LANE << (r + 1), [(1 << (1 << r)) - 1] * (CELLS >> (r + 1))),
    })


def lane_development() -> str:
    """The verified lane algebra, lifted out of LaneProbe.lean.

    LaneProbe.lean is the file CI compiles on its own, so it is the only place
    these proofs have ever been checked. Copying rather than restating keeps
    the submission's proofs identical to the ones that were verified; the
    `#check` lines and the `example` blocks are probes and measurements and do
    not belong in an entry.
    """
    src = (HERE / "LaneProbe.lean").read_text(encoding="utf-8")
    body = src[src.index("namespace Lane"):src.index("end Lane")]
    body = body[len("namespace Lane"):]
    # drop the probe lines and the measured `example`s with their set_options
    body = re.sub(r"^#check .*\n", "", body, flags=re.M)
    body = re.sub(
        r"^(set_option [^\n]*\sin\n)*example [^\n]*(\n(?![\n/]).*)*\n",
        "", body, flags=re.M)
    # the mask section is about whether a measurement is possible, not about
    # the entry; its heading would dangle once the examples are gone
    body = re.sub(
        r"/-! ## Can the kernel check a mask against its packing.*?-/\n",
        "", body, flags=re.S)
    assert "#check" not in body and "\nexample" not in body
    assert "testBit_pack" in body and "merge_round" in body
    return body.strip("\n")


def carried_over() -> str:
    """The rotations, the step and the iteration, exactly as they stand."""
    src = (HERE / "Submission.lean").read_text(encoding="utf-8")
    start = src.index("/-! ## The Rule 110 table as a formula -/")
    end = src.index("theorem impl_correct")
    return src[start:end].strip("\n")


def packed_defs() -> str:
    out = []
    a = out.append
    a("/-! ## The packed initial row")
    a("")
    a("The live entry builds the initial row the specification's way, which")
    a("evaluates a 32-bit mixing hash once per cell, 256 times. stepmodel.py")
    a("counts that at 5,348 of the entry's 5,465 operations, because the")
    a("judged cases ask for at most 13 steps. This builds the same row with")
    a("every cell in its own 64-bit lane inside one natural number, so the")
    a("hash runs on all 256 cells at once.")
    a("")
    a("The constants are literals. Building a mask from the recursive")
    a("definition would cost operations at reduction time and the gather is")
    a("already the larger half of the work, so each one is written out and")
    a("related to its packed form by `rfl`, which the kernel settles once at")
    a("compile time.")
    a("-/")
    a("")
    a("/-- One in every lane. -/")
    a(f"def onesP : Nat := {hex(ONES)}")
    a("")
    a("/-- The lane index plus one, in every lane. With `onesP` this builds the")
    a("whole seeded ramp in two multiplications and one addition, because")
    a("`Lane.pack_mul` and `Lane.pack_add` carry no side conditions. -/")
    a(f"def rampP : Nat := {hex(RAMP)}")
    a("")
    a("/-- Thirty-two live bits in every lane. -/")
    a(f"def maskP : Nat := {hex(M32P)}")
    a("")
    for rd in ROUNDS:
        a(f"/-- Gather round {rd['r']}: the low {rd['held']} bit(s) of every "
          f"{rd['twoW']}-bit field. -/")
        a(f"def gmask{rd['r']} : Nat := {hex(rd['mask'])}")
    a("")
    a("theorem onesP_eq : onesP = Lane.pack 64 (fun _ => 1) 256 := by rfl")
    a("")
    a("theorem rampP_eq : rampP = Lane.pack 64 (fun i => i + 1) 256 := by rfl")
    a("")
    a("theorem maskP_eq : maskP = Lane.pack 64 (fun _ => 2 ^ 32 - 1) 256 := by")
    a("  rfl")
    a("")
    for rd in ROUNDS:
        a(f"theorem gmask{rd['r']}_eq : gmask{rd['r']}")
        a(f"    = Lane.pack {rd['twoW']} "
          f"(fun _ => 2 ^ 2 ^ {rd['r']} - 1) {rd['lanes']} := by rfl")
        a("")
    a("/-- The ramp lane, zero above the row. `Lane.pack` reads only the first")
    a("256 lanes, so this agrees with `seed + (i+1) * 0x9e3779b9` everywhere it")
    a("is read; being bounded at every index is what lets the lane lemmas,")
    a("which ask for a bound at every index, apply to it at all. -/")
    a("def rampLane (seed i : Nat) : Nat :=")
    a(f"  if i < ruleWidth then seed + (i + 1) * {PHI} else 0")
    a("")
    a("/-- The initial row, all 256 cells at once. -/")
    a("def packedRow (seed : Nat) : Nat :=")
    a("  let x := onesP * seed + rampP * " + str(PHI))
    a("  let x := (((x ^^^ ((x >>> 16) &&& maskP)) &&& maskP) * "
      f"{A1}) &&& maskP")
    a("  let x := (((x ^^^ ((x >>> 15) &&& maskP)) &&& maskP) * "
      f"{A2}) &&& maskP")
    a("  let x := (x ^^^ ((x >>> 16) &&& maskP)) &&& maskP")
    a("  let b := (x >>> 31) &&& onesP")
    for rd in ROUNDS:
        a(f"  let b := (b &&& gmask{rd['r']}) "
          f"+ (((b >>> {rd['W']}) &&& gmask{rd['r']}) * {rd['held'] and 2 ** rd['held']})")
    a("  (b >>> 2) * 4 + 1")
    return "\n".join(out)


def main() -> None:
    parts = [
        "import Spec",
        "",
        "/-!",
        "# ca-rule110 — the initial row built on all 256 cells at once",
        "",
        "The packed Rule 110 step in this file is unchanged and so is every",
        "lemma about it. What changes is the initial row.",
        "",
        "The specification derives each cell from a 32-bit mixing hash of",
        "`seed + (i+1) * 0x9e3779b9`, and the previous entry evaluated that",
        "hash 256 times, once per cell. stepmodel.py counts the cost: the",
        "judged cases ask for at most 13 steps, so the stepping is at most 117",
        "operations and the row is 5,348 of 5,465. The row, not the stepping,",
        "is where the work is.",
        "",
        "This entry gives every cell a 64-bit lane inside one natural number",
        "and runs the whole hash on all 256 cells at once. The lanes are a",
        "sum rather than a bitwise or, which is the one design decision",
        "everything else follows from: multiplication distributes over a sum,",
        "so a scalar multiplies every lane with no side condition, and the two",
        "halves of each gather round join by the same lemma. No carry argument",
        "appears anywhere below.",
        "",
        "The specification masks to 32 bits after each multiply. A packed lane",
        "cannot, because the shifted copy carries its neighbour's bits at the",
        "top of the lane and the multiply would drag them across the boundary,",
        "so this masks before the multiply instead. The two agree because",
        "`(a % 2^m * c) % 2^m = (a * c) % 2^m`, and masking first caps the",
        "widest intermediate at 63 bits, which is why a lane is 64 bits wide",
        "and not the 128 the specification's own order would need.",
        "-/",
        "",
        "namespace Submission",
        "",
        "namespace Lane",
        "",
        lane_development(),
        "",
        "end Lane",
        "",
        packed_defs(),
        "",
        "/-! ## The packed row, as the specification's own encoding -/",
        "",
        "/-! ## The packed step, unchanged -/",
        "",
        "/-- All 256 low bits set: the width the specification fixes. -/",
        "def rowMask : Nat := (1 <<< ruleWidth) - 1",
        "",
        "/-- The left neighbour of every cell at once. Bit `i` of the result is",
        "bit `i - 1` of `R`, cyclically. -/",
        "def rotL (R : Nat) : Nat :=",
        "  ((R <<< 1) ||| (R >>> (ruleWidth - 1))) &&& rowMask",
        "",
        "/-- The right neighbour of every cell at once. Bit `i` of the result is",
        "bit `i + 1` of `R`, cyclically. -/",
        "def rotR (R : Nat) : Nat :=",
        "  ((R >>> 1) ||| ((R &&& 1) <<< (ruleWidth - 1))) &&& rowMask",
        "",
        "/-- One Rule 110 step on the packed row: eight `Nat` operations,",
        "whatever the row's length. -/",
        "def pStep (R : Nat) : Nat :=",
        "  (R ||| rotR R) &&& (rowMask ^^^ (rotL R &&& R &&& rotR R))",
        "",
        "/-- `t` steps. -/",
        "def pIter : Nat → Nat → Nat",
        "  | 0,     R => R",
        "  | t + 1, R => pIter t (pStep R)",
        "",
        "/-! ## The implementation -/",
        "",
        "def impl (n : Nat) : Nat :=",
        "  pIter (caSteps n) (packedRow (caSeed n))",
        "",
        carried_over(),
        "",
        "end Submission",
    ]
    out = "\n".join(parts) + "\n"
    (HERE / "Submission.lean").write_text(out, encoding="utf-8")
    print(f"wrote Submission.lean, {len(out.splitlines())} lines, "
          f"{len(out)} bytes")


if __name__ == "__main__":
    main()
