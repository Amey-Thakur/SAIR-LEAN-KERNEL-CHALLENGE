#!/usr/bin/env python3
# ==============================================================================
# File: widthcost.py
# Description: Holds the number of kernel reduction steps FIXED and varies only
#   the width of the numbers, to measure what operand width costs per step.
#
#   Why this exists, and what is wrong with primitives.py. That script timed one
#   primitive per `lean` invocation and found every one of them flat from 2,701
#   bits to 43,216 bits. That result is real but it is much weaker than it
#   looks: a single operation costing even 183,000 instructions is about 0.06 ms,
#   and every case was measured against 0.27 s of process startup. So it proved
#   only that no primitive unfolds catastrophically -- which did kill the theory
#   that `shiftLeft` recurses on the shift amount -- and it cannot tell 2,000
#   instructions per operation from 183,000. The gap being investigated is 92x,
#   and it sits entirely inside that blind spot.
#
#   The design that fixes it. One recursive definition performs a chosen number
#   of additions, and only the width of the operand changes between runs:
#
#       iterAdd x 0       = 0
#       iterAdd x (k + 1) = x + iterAdd x k
#
#   At every width this is the same number of reduction steps, the same
#   recursion depth and the same term shape. Whatever the time does across the
#   rows is what width costs, with nothing else moving. The accumulator reaches
#   only `reps * x`, about fifteen bits more than `x`, so the width under test
#   is the width throughout.
#
#   What the answer decides. The packed `partition` entry does about 720 sweep
#   steps across the six judged sizes on 2,701-bit rows and was judged at
#   132,036,341, which is roughly 183,000 units per step. The list entry does
#   about 182,642 steps on small numbers and measures 3.63 s, which is roughly
#   8,700 units per step. The leader is at 1,429,499. Both of our designs can be
#   explained by one per-step cost curve in the width, and if that curve is
#   steep then the packed row is paying for its own width and the field width
#   should be cut; if it is flat then the only thing that matters is the step
#   count and the leader must be doing far fewer steps than either of our
#   designs. These are different repairs, so the curve has to be measured.
#
#   Reading the output. `per step` is the interesting column. Flat means width is
#   free and step count is everything. Growth proportional to the width means
#   the packed row is the wrong shape at this width.
#
# Usage: py stage2/widthcost.py [--widths 1,64,601,2701,20301] [--reps 20000]
# Author: Amey Thakur
# License: CC BY 4.0
# ==============================================================================

from __future__ import annotations

import argparse
import pathlib
import subprocess
import tempfile
import time

# `iterAdd` is structural recursion on the count, so the kernel unfolds it
# without any well-founded machinery, and the count is the step count exactly.
# The two `set_option` lines are the usual pair: a 20,000-deep reduction passes
# the elaborator's default recursion limit, and that limit has been mistaken for
# a kernel failure three times in this repository already.
PRELUDE = """set_option maxRecDepth 8000000
set_option maxHeartbeats 0

def iterAdd (x : Nat) : Nat -> Nat
  | 0     => 0
  | k + 1 => x + iterAdd x k

def iterShift (x : Nat) : Nat -> Nat
  | 0     => x
  | k + 1 => (iterShift x k) >>> 1 ||| x

def iterMod (x m : Nat) : Nat -> Nat
  | 0     => x
  | k + 1 => (iterMod x m k) % m ||| x
"""

# name -> (expression template in {W} and {R}, expected value template)
#
# Every case ends in `% 2` so the answer is one digit: the kernel still does all
# the work, but neither the parser nor the printer handles a wide literal, which
# would otherwise be charged to the operation under test.
CASES: list[tuple[str, str, str]] = [
    # reps additions, each on a W-bit operand
    ("add", "iterAdd (1 <<< {W}) {R} % 2", "0"),
    # reps shifts and ors, to confirm the shape is not specific to addition
    ("shiftRight and or", "iterShift (1 <<< {W}) {R} % 2", "0"),
    # reps reductions modulo a W-bit number, the packed row's per-row operation
    ("mod", "iterMod (1 <<< {W}) (1 <<< {W}) {R} % 2", "0"),
]


def time_src(src: str, timeout: float) -> tuple[float | None, str]:
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=".",
                                     delete=False, encoding="utf-8") as fh:
        fh.write(src)
        path = pathlib.Path(fh.name)
    try:
        t0 = time.monotonic()
        proc = subprocess.run(["lake", "env", "lean", path.name],
                              capture_output=True, text=True, timeout=timeout)
        dt = time.monotonic() - t0
    except subprocess.TimeoutExpired:
        return None, f"timeout {timeout:.0f}s"
    finally:
        path.unlink(missing_ok=True)
    if proc.returncode != 0:
        lines = (proc.stdout + proc.stderr).strip().splitlines()
        return None, (lines[0] if lines else "no output")[:80]
    return dt, "ok"


def main() -> int:
    ap = argparse.ArgumentParser()
    # 1 bit is a machine word's worth of nothing, 64 is one word, 601 and 2,701
    # are the packed row's field width and row width at n = 36, and 20,301 is
    # the row width at n = 100, where the entry is slow enough to time directly.
    ap.add_argument("--widths", default="1,64,601,2701,20301")
    ap.add_argument("--reps", type=int, default=20000)
    ap.add_argument("--timeout", type=float, default=300.0)
    args = ap.parse_args()

    widths = [int(w) for w in args.widths.split(",")]
    reps = args.reps

    # The step count is identical across widths, so the baseline only has to
    # cover process startup and the elaboration of the prelude.
    base, status = time_src(PRELUDE + "theorem b : 1 + 1 = 2 := by rfl\n",
                            args.timeout)
    if base is None:
        print(f"  baseline did not run: {status}")
        return 1
    print(f"  {reps} reduction steps per cell, identical at every width")
    print(f"  process startup {base:.2f}s, subtracted\n")

    for name, tmpl, expected in CASES:
        print(f"  {name}")
        print(f"    {'width':>8}{'net':>10}{'per step':>14}{'vs 1 bit':>10}")
        first: float | None = None
        for w in widths:
            expr = tmpl.replace("{W}", str(w)).replace("{R}", str(reps))
            src = PRELUDE + f"theorem b : {expr} = {expected} := by rfl\n"
            dt, status = time_src(src, args.timeout)
            if dt is None:
                print(f"    {w:>8}{status[:9]:>10}")
                continue
            net = max(0.0, dt - base)
            per = net / reps
            cell = f"    {w:>8}{net:>9.2f}s{per * 1e6:>11.2f}us"
            if first is None:
                first = net
            elif first > 0.01:
                cell += f"{net / first:>9.1f}x"
            print(cell)
        print()

    print("  flat per-step cost  -> width is free, only the step count matters,")
    print("                         and the leader is doing far fewer steps")
    print("  rising per-step cost -> the packed row pays for its own width and")
    print("                         the field width is the thing to cut")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
