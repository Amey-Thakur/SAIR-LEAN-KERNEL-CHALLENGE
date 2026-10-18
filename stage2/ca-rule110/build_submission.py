#!/usr/bin/env python3
# ==============================================================================
# File: build_submission.py
# Description: Assembles Submission.lean from the verified lane development,
#   the generated assembly, and the carried-over packed stepping.
#
#   The change to the entry is surgical. The live submission already proves the
#   packed Rule 110 step against the specification's list step; what it does
#   not do is build the initial row, which stepmodel.py counts at 5,348 of the
#   entry's 5,465 operations, because the judged cases ask for at most 13
#   steps. Only that one argument is replaced. Every lemma about the mask, the
#   rotations, the step and the iteration is carried over byte for byte from
#   stepping.lean.inc, which was snapshotted out of the entry that is live.
#
#   The lane proofs are lifted out of LaneProbe.lean rather than restated.
#   LaneProbe.lean is the file CI compiles on its own, so it is the only place
#   they have ever been checked, and copying keeps the submission's proofs
#   identical to the ones that were verified. The probe lines and the measured
#   examples are instrumentation and do not belong in an entry.
#
# Usage: py stage2/ca-rule110/build_submission.py
# Author: Amey Thakur
# License: CC BY 4.0
# ==============================================================================

from __future__ import annotations

import pathlib
import re

HERE = pathlib.Path(__file__).resolve().parent

HEADER = """import Spec

/-!
# ca-rule110 - the initial row built on all 256 cells at once

The packed Rule 110 step in this file is unchanged, and so is every lemma
about it. What changes is the initial row.

The specification derives each cell from a 32-bit mixing hash of
`seed + (i + 1) * 0x9e3779b9`, and the previous entry evaluated that hash 256
times, once per cell. `stepmodel.py` in the working repository counts the
cost: the judged cases ask for at most 13 steps, so the stepping is at most
117 operations and the row is 5,348 of 5,465. The row, not the stepping, is
where the work is, which is the opposite of what the previous entry's note
claimed.

This entry gives every cell a 64-bit lane inside one natural number and runs
the whole hash on all 256 cells at once. Lanes are a **sum**, not a bitwise
or, and that is the one decision everything else follows from. The `|||`
version of the central lemma is shorter, because a bit of a disjunction is a
disjunction of bits and no carry reasoning is needed at all. It is still the
wrong choice: the hash multiplies, multiplication distributes over a sum and
not over a disjunction, and core Lean has no lemma to convert between them.
Paying the no-carry argument once, in `Lane.testBit_pack`, where the lane
bound does the work, buys two lemmas that carry **no side conditions**:

* `Lane.pack_mul`, a scalar multiplies every lane;
* `Lane.pack_add`, two packings add lane by lane.

Those two are what make the design cheap. The seeded ramp across 256 lanes
becomes two multiplications and one addition against seed-independent
constants, instead of 256 of each. And in the gather, the even and odd halves
of every round are joined by `pack_add` and raised into place by `pack_mul`,
so **no carry argument appears anywhere below**.

The specification masks to 32 bits *after* each multiply. A packed lane
cannot: the shifted copy carries its neighbour's bits at the top of the lane,
and the multiply would drag them across the boundary. So this masks *before*
the multiply instead. The two agree because
`(a % 2 ^ m * c) % 2 ^ m = (a * c) % 2 ^ m`, and masking first caps the
widest intermediate at 32 + 31 = 63 bits, which is why a lane is 64 bits wide
and not the 128 the specification's own order of operations would force.

The wide constants are literals. Building a mask from the recursive
definition would cost operations at reduction time and the gather is already
the larger half of the work, so each is related to its packed form by `rfl`,
which the kernel settles once at compile time and never again while a judged
case reduces.

No precomputed answers. There is no table of rows, no hardcoded value and no
input-dependent branch carrying an answer. Every value is computed at
reduction time from the specification's own seed.
-/

namespace Submission
"""

IMPL = """/-! ## The packed step, carried over unchanged -/

/-- All 256 low bits set: the width the specification fixes. -/
def rowMask : Nat := (1 <<< ruleWidth) - 1

/-- The left neighbour of every cell at once. Bit `i` of the result is bit
`i - 1` of `R`, cyclically. -/
def rotL (R : Nat) : Nat :=
  ((R <<< 1) ||| (R >>> (ruleWidth - 1))) &&& rowMask

/-- The right neighbour of every cell at once. Bit `i` of the result is bit
`i + 1` of `R`, cyclically. -/
def rotR (R : Nat) : Nat :=
  ((R >>> 1) ||| ((R &&& 1) <<< (ruleWidth - 1))) &&& rowMask

/-- One Rule 110 step on the packed row: eight `Nat` operations, whatever the
row's length. -/
def pStep (R : Nat) : Nat :=
  (R ||| rotR R) &&& (rowMask ^^^ (rotL R &&& R &&& rotR R))

/-- `t` steps. -/
def pIter : Nat → Nat → Nat
  | 0,     R => R
  | t + 1, R => pIter t (pStep R)

/-! ## The implementation -/

def impl (n : Nat) : Nat :=
  pIter (caSteps n) (Row.packedRow (caSeed n))
"""

CORRECT = """/-- The seed is the low 32 bits of the input, which is the bound the lane
widths were chosen against. -/
theorem caSeed_lt (n : Nat) : caSeed n < 2 ^ 32 := by
  rw [caSeed]
  exact Nat.and_lt_two_pow _ (by decide)

theorem impl_correct : ∀ n, impl n = caSpecN n := by
  intro n
  show pIter (caSteps n) (Row.packedRow (caSeed n))
      = encodeRow (iterRow (caSteps n) (initRowFor (caSeed n)))
  rw [Row.packedRow_eq (caSeed_lt n)]
  exact pIter_encodeRow _ _ (length_initRowFor _)
"""


def lane_development() -> str:
    """The verified lane algebra, lifted out of LaneProbe.lean."""
    src = (HERE / "LaneProbe.lean").read_text(encoding="utf-8")
    body = src[src.index("namespace Lane") + len("namespace Lane"):
               src.index("end Lane")]
    # that section's heading is about whether a measurement is possible
    body = re.sub(
        r"/-! ## Can the kernel check a mask against its packing.*?-/\n+",
        "", body, flags=re.S)
    # The probe lines and the measured examples are instrumentation. Stripped
    # line by line rather than by pattern: an `example` may wrap onto a second
    # line, and a pattern that missed one would leave a measurement in the
    # entry.
    kept: list[str] = []
    pending: list[str] = []
    skipping = False
    for line in body.splitlines():
        if skipping:
            if line.rstrip().endswith(":= by rfl"):
                skipping = False
            continue
        if line.startswith("#check "):
            continue
        if line.startswith("set_option ") and line.rstrip().endswith(" in"):
            pending.append(line)
            continue
        if line.startswith("example "):
            pending.clear()
            skipping = not line.rstrip().endswith(":= by rfl")
            continue
        kept.extend(pending)
        pending.clear()
        kept.append(line)
    kept.extend(pending)
    body = "\n".join(kept)
    assert "#check" not in body, "probe lines left in"
    assert "\nexample" not in body, "measured examples left in"
    for name in ("testBit_pack", "pack_mul", "pack_add", "eq_of_lanes",
                 "merge_round", "mixLane_eq", "encodeRow_map_range",
                 "gather_round", "fix_two", "pack_stage"):
        assert name in body, f"missing {name}"
    return body.strip("\n")


def assembly() -> str:
    """The generated row, from LaneProbe.lean where it was checked."""
    src = (HERE / "LaneProbe.lean").read_text(encoding="utf-8")
    body = src[src.index("/-! ## Assembling the row"):]
    assert body.rstrip().endswith("end Row")
    assert "packedRow_eq" in body
    return body.strip("\n")


def main() -> None:
    stepping = (HERE / "stepping.lean.inc").read_text(encoding="utf-8")
    parts = [
        HEADER,
        "namespace Lane",
        "",
        lane_development(),
        "",
        "end Lane",
        "",
        assembly(),
        "",
        IMPL,
        stepping.strip("\n"),
        "",
        CORRECT,
        "end Submission",
    ]
    out = "\n".join(parts) + "\n"
    (HERE / "Submission.lean").write_text(out, encoding="utf-8")
    print(f"wrote Submission.lean: {len(out.splitlines())} lines, "
          f"{len(out)} bytes")


if __name__ == "__main__":
    main()
