#!/usr/bin/env python3
# ==============================================================================
# File: primitives.py
# Description: Times the Lean kernel performing ONE arithmetic primitive on a
#   large natural number, to find out which primitives the kernel accelerates
#   and which it unfolds.
#
#   Why this exists. The packed `partition` entry performs about 2,801 `Nat`
#   operations and the judge measured it at 132,036,341 units of work, which is
#   roughly 47,000 units per operation. No single operation on a 43-word number
#   should cost that. Two cost models have now been written to explain the gap
#   and both were wrong, in opposite directions: one said the packed design
#   should lose to a design measured 52x slower, the other said the reduction
#   was three quarters of the cost. A model that has been wrong twice is not
#   worth a third guess, so this measures the primitives instead.
#
#   The question it settles: whether `Nat.shiftLeft` is accelerated or unfolds
#   on the shift amount. Summed over every row, the sweep shifts by about
#   94,600 bits. If each shift unfolds into that many doublings of a 43-word
#   number, the shifts alone account for the measurement and the design is
#   wrong in a way no amount of reducing the operation COUNT can fix. If the
#   shifts are accelerated, the cost is somewhere else and this rules one
#   suspect out.
#
#   Method. Each case is one primitive applied to a number of a chosen bit
#   width, wrapped so the check itself is cheap: `% 2` against a known parity
#   rather than a literal of the full width, which would move the cost into
#   parsing and printing the answer. Every case therefore also pays for the
#   shifts that build its operands, and the `baseline` case is exactly those
#   shifts with no primitive on top, so a primitive's own cost is the
#   difference. Each case is its own file and its own `lean` invocation, for the
#   same reason `timecases.py` does that: one file would let elaboration of a
#   later case overlap an earlier one.
#
#   Reading the output. A primitive the kernel accelerates is flat in the width
#   or grows with the number of machine words, so quadrupling the width at most
#   quadruples the time. One that unfolds grows with the bit width times the
#   operand size, so quadrupling the width multiplies the time by about sixteen.
#   The growth column is the ratio to the previous width, and it is the answer.
#
# Usage: py stage2/primitives.py [--widths 2701,10804,43216] [--timeout 120]
# Author: Amey Thakur
# License: CC BY 4.0
# ==============================================================================

from __future__ import annotations

import argparse
import pathlib
import subprocess
import tempfile
import time

# Each case is (name, expression template, expected value).
#
# `N` is the bit width. Operands are built with `1 <<< N`, so every case pays
# for its shifts; `baseline` is the shifts alone. The outer `% 2` keeps the
# answer a single digit: the kernel still has to do the work, but neither the
# parser nor the pretty printer has to handle a 43-word literal, which would
# otherwise be charged to the primitive under test.
CASES: list[tuple[str, str, str]] = [
    # the shifts alone, to be subtracted from everything below
    ("baseline (one shiftLeft)", "(1 <<< {N}) % 2", "0"),
    # shiftRight, on top of one shiftLeft
    ("shiftRight", "((1 <<< {N}) >>> {N})", "1"),
    # addition of two N-bit numbers
    ("add", "((1 <<< {N}) + (1 <<< {N})) % 2", "0"),
    # multiplication, the operand the sweep would use if shifts were replaced
    ("mul", "((1 <<< {N}) * (1 <<< {N})) % 2", "0"),
    # the reduction the packed row performs once per row
    ("mod by a power of two", "((1 <<< {N}) % (1 <<< ({N} / 2)))", "0"),
    # the mask that would replace that reduction
    ("and with a mask", "(((1 <<< {N}) - 1) &&& (1 <<< ({N} / 2))) % 2", "0"),
    # exponentiation, in case it is cheaper than shifting
    ("pow", "(2 ^ {N}) % 2", "0"),
]


def time_case(expr: str, expected: str, timeout: float) -> tuple[float | None, str]:
    """Return (seconds, status) for the kernel checking `expr = expected`.

    No `import` at all: these are core `Nat` operations, so the measurement is
    not carrying the cost of loading this problem's Spec or Submission. The two
    `set_option` lines are the same ones `timecases.py` uses, and for the same
    reason: `maxRecDepth` and `maxHeartbeats` are elaborator limits, and a case
    stopped by either would look like a primitive that cannot be computed.
    """
    src = ("set_option maxRecDepth 8000000 in\n"
           "set_option maxHeartbeats 0 in\n"
           f"theorem bench : {expr} = {expected} := by rfl\n")
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
        return None, f"timeout after {timeout:.0f}s"
    finally:
        path.unlink(missing_ok=True)
    if proc.returncode != 0:
        out = (proc.stdout + proc.stderr).strip().splitlines()
        first = out[0] if out else "no output"
        return None, first[:90]
    return dt, "ok"


def main() -> int:
    ap = argparse.ArgumentParser()
    # 2701 is the packed row width at n = 36, the size the judge measures. The
    # other two are four and sixteen times it, so the growth column separates a
    # primitive that is linear in the machine words from one that unfolds.
    ap.add_argument("--widths", default="2701,10804,43216")
    ap.add_argument("--timeout", type=float, default=120.0)
    args = ap.parse_args()

    widths = [int(w) for w in args.widths.split(",")]

    print(f"  kernel cost of one primitive, by operand bit width")
    print(f"  every case includes its shifts; subtract the baseline row\n")
    head = f"{'primitive':<26}"
    for w in widths:
        head += f"{w:>12}{'x':>7}"
    print(head)
    print("  " + "-" * (26 + 19 * len(widths) - 2))

    for name, tmpl, expected in CASES:
        row = f"{name:<26}"
        prev: float | None = None
        for w in widths:
            expr = tmpl.replace("{N}", str(w))
            dt, status = time_case(expr, expected, args.timeout)
            if dt is None:
                row += f"{status[:11]:>12}{'':>7}"
                prev = None
                continue
            row += f"{dt:>11.2f}s"
            if prev is not None and prev > 0.005:
                row += f"{dt / prev:>6.1f}x"
            else:
                row += f"{'':>7}"
            prev = dt
        print(row)

    print("\n  how to read the growth column: quadrupling the width")
    print("    at most 4x   -> the kernel accelerates it, cost is in machine words")
    print("    about 16x    -> it unfolds, cost is bit width times operand size")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
