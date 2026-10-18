#!/usr/bin/env python3
# ==============================================================================
# File: bulk.py
# Description: Emits Lean files that let a change in `fib` actually be seen.
#
#   Why this exists. timecases.py times the kernel reducing
#   `impl n = <expected literal>`. At n = 150000 that literal is 31,348
#   decimal digits, and the cost of PARSING it is paid identically by every
#   candidate. If it dominates, two implementations whose computation differs
#   by a factor of ten report the same number, and the file's n-scaling says
#   it does dominate: the measured work rose 3.2x from n = 80000 to n = 150000,
#   which is the 3.5x of a quadratic decimal parse, not what the kernel's own
#   work should do.
#
#   Two fixes, both used here.
#
#   1. A right-hand side that is cheap to write down but still forces the whole
#      reduction. `impl n % M = r` makes the kernel reduce `impl n` to a
#      literal before it can apply its `Nat.mod` accelerator, so nothing is
#      skipped, while the literal in the source is sixteen hex digits instead
#      of thirty-one thousand decimal ones.
#
#   2. Many distinct inputs in one process. Lean start-up with this Mathlib
#      package is about 1.74 s, far more than one case of work, so one case
#      per process cannot resolve anything. Distinct inputs also keep the
#      kernel's cache from answering a case for free.
#
#   The expected values come from the specification's own recurrence run
#   iteratively, which shares no structure with any fast-doubling candidate.
#
# Usage: py stage2/fib/bulk.py --emit bulk [--count 16] > Bulk.lean
#        py stage2/fib/bulk.py --emit decomp --case T3 --n 150000 > T3.lean
#        py stage2/fib/bulk.py --emit prof --n 150000 > Prof.lean
# Author: Amey Thakur
# License: CC BY 4.0
# ==============================================================================

from __future__ import annotations

import argparse
import sys

sys.set_int_max_str_digits(400_000)

# 2^64 - 59. Wide enough that a wrong implementation agreeing with the right
# one here is not a thing that happens, cheap for the kernel to divide by, and
# sixteen characters of source rather than thirty-one thousand.
MOD = 0xFFFFFFFFFFFFFFC5

# The judged groups, from rules/problems/fib.md.
GROUPS = {
    "f1": (5_000, 10_000),
    "f2": (20_000, 40_000),
    "f3": (80_000, 150_000),
}

HEADER = ["import Submission",
          "set_option maxRecDepth 8000000",
          "set_option maxHeartbeats 0"]


def fib_plain(n: int) -> int:
    """The specification's recurrence, iteratively. Not fast doubling."""
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def check_reference() -> None:
    """A reference nobody checked is an assumption."""
    known = {0: 0, 1: 1, 2: 1, 3: 2, 10: 55, 20: 6765, 50: 12586269025}
    for n, v in known.items():
        if fib_plain(n) != v:
            raise SystemExit(f"reference is wrong at n={n}")
    # F(n) has floor(n*log10(phi)) + 1 digits for n >= 1; a check on the shape
    # of the big ones that does not depend on the same loop being right.
    import math
    for n in (5_000, 150_000):
        want = int(n * math.log10((1 + 5 ** 0.5) / 2)) + 1
        got = len(str(fib_plain(n)))
        if abs(got - want) > 1:
            raise SystemExit(f"F({n}) has {got} digits, expected about {want}")


def spread(lo: int, hi: int, count: int) -> list[int]:
    """`count` distinct inputs across the group, endpoints included."""
    if count < 2:
        return [hi]
    step = (hi - lo) / (count - 1)
    xs = sorted({lo + round(i * step) for i in range(count)})
    if len(xs) != count:
        raise SystemExit(f"group {lo}-{hi} cannot hold {count} distinct inputs")
    return xs


def emit_bulk(count: int, groups: list[str]) -> list[str]:
    lines = list(HEADER) + ["namespace FibBulk"]
    for g in groups:
        lo, hi = GROUPS[g]
        lines.append(f"-- group {g}: {count} distinct inputs in {lo}..{hi}")
        for i, n in enumerate(spread(lo, hi, count)):
            r = fib_plain(n) % MOD
            lines.append(f"theorem {g}_{i} : "
                         f"Submission.impl {n} % 0x{MOD:X} = {r} := by rfl")
    lines.append("end FibBulk")
    return lines


def emit_decomp(case: str, n: int) -> list[str]:
    """One file per hypothesis about where the wall-clock goes.

    T0  start-up alone: the import and nothing else.
    T1  start-up plus parsing the decimal literal, with no `impl` in sight.
    T2  the same literal in hex, so hex parsing can be priced separately.
    T3  the computation, against a right-hand side that costs nothing to read.
    T4  what timecases.py does: the computation and the decimal literal.
    T5  the computation and the literal, in hex.
    """
    v = fib_plain(n)
    r = v % MOD
    lines = list(HEADER)
    if case == "T0":
        pass
    elif case == "T1":
        lines.append(f"theorem t : ({v}) % 0x{MOD:X} = {r} := by rfl")
    elif case == "T2":
        lines.append(f"theorem t : (0x{v:X}) % 0x{MOD:X} = {r} := by rfl")
    elif case == "T3":
        lines.append(f"theorem t : Submission.impl {n} % 0x{MOD:X} = {r} "
                     f":= by rfl")
    elif case == "T4":
        lines.append(f"theorem t : Submission.impl {n} = {v} := by rfl")
    elif case == "T5":
        lines.append(f"theorem t : Submission.impl {n} = 0x{v:X} := by rfl")
    else:
        raise SystemExit(f"unknown case {case}")
    return lines


def emit_prof(n: int, count: int) -> list[str]:
    """The same forcing check under Lean's own profiler.

    `profiler true` separates elaboration from `type checking`, and type
    checking is the kernel's `addDecl` -- the only thing the judge counts.
    """
    lines = list(HEADER) + ["set_option profiler true",
                            "set_option profiler.threshold 1"]
    lo, hi = GROUPS["f3"]
    for i, m in enumerate(spread(lo, hi, count)):
        r = fib_plain(m) % MOD
        lines.append(f"theorem p{i} : "
                     f"Submission.impl {m} % 0x{MOD:X} = {r} := by rfl")
    return lines


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--emit", required=True,
                    choices=["bulk", "decomp", "prof"])
    ap.add_argument("--count", type=int, default=16)
    ap.add_argument("--groups", default="f1,f2,f3")
    ap.add_argument("--case", default="T3")
    ap.add_argument("--n", type=int, default=150_000)
    args = ap.parse_args()

    check_reference()

    if args.emit == "bulk":
        groups = [g.strip() for g in args.groups.split(",") if g.strip()]
        bad = [g for g in groups if g not in GROUPS]
        if bad:
            raise SystemExit(f"unknown groups {bad}")
        lines = emit_bulk(args.count, groups)
    elif args.emit == "decomp":
        lines = emit_decomp(args.case, args.n)
    else:
        lines = emit_prof(args.n, 4)

    print("\n".join(lines))
    return 0


if __name__ == "__main__":
    sys.exit(main())
