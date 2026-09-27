#!/usr/bin/env python3
# ==============================================================================
# File: widthcost.py
# Description: Holds the number of kernel reduction steps FIXED and varies only
#   the width of the numbers, to measure what operand width costs per step.
#
#   Why this exists, and what is wrong with primitives.py. That script timed one
#   primitive per `lean` invocation and found every one of them flat from 2,701
#   bits to 43,216 bits. The result is real but much weaker than it looks: a
#   single operation costing even 183,000 instructions is about 0.06 ms, and
#   every case was measured against 0.27 s of process startup. So it proved only
#   that no primitive unfolds catastrophically -- which did kill the theory that
#   `shiftLeft` recurses on the shift amount -- and it cannot tell 2,000
#   instructions per operation from 183,000. The gap being investigated is 92x
#   and it sits entirely inside that blind spot.
#
#   The design. One recursive definition performs a chosen number of operations
#   and only the width of the operand changes between runs:
#
#       iterAdd x 0       = 0
#       iterAdd x (k + 1) = x + iterAdd x k
#
#   At every width that is the same number of reduction steps, the same
#   recursion depth and the same term shape, so whatever the time does across a
#   row is what width costs with nothing else moving.
#
#   What the answer decides. The packed `partition` entry does about 720 sweep
#   steps across the six judged sizes on 2,701-bit rows and was judged at
#   132,036,341, roughly 183,000 units per step. The list entry does about
#   182,642 steps on small numbers and measures 3.63 s, roughly 8,700 units per
#   step. The leader is at 1,429,499. A flat curve means width is free, the step
#   count is everything, and the leader is doing far fewer steps than either of
#   our designs. A rising curve means the packed row pays for its own width and
#   the field width `2n + 1` -- loose, since p(36) needs 15 bits and gets 73 --
#   is the thing to cut. Different repairs, so the curve gets measured.
#
#   Two corrections from the first run, both worth stating because each produced
#   a plausible-looking table that meant nothing:
#
#     1. The baseline was measured cold, before any olean existed, so it came out
#        at 12.74 s and every net time clamped to 0.00 s. A warm-up invocation
#        now runs first and the baseline is the minimum of three, since the
#        minimum of repeated runs of identical work is the one robust statistic
#        on a shared runner. Raw times are printed beside the net ones so a
#        baseline that has gone wrong again is visible rather than silent.
#
#     2. Expected values were written by hand and the one for the shift case was
#        wrong: at W = 1 the recursion gives 3, which is odd, so the case could
#        only ever fail. Every expected value is now produced by simulating the
#        same recursion in Python, so the Lean side is being checked against
#        something rather than against an assumption.
#
# Usage: py stage2/widthcost.py [--widths 1,64,601,2701,20301] [--reps 20000]
# Author: Amey Thakur
# License: CC BY 4.0
# ==============================================================================

from __future__ import annotations

import argparse
import pathlib
import re
import subprocess
import tempfile
import time

NL = chr(10)

# `iterAdd`, `iterShift` and `iterMod` are structural recursion on the count, so
# the kernel unfolds them with no well-founded machinery and the count is the
# step count exactly. The two options are the usual pair: a 20,000-deep
# reduction passes the elaborator's default recursion limit, and that limit has
# already been mistaken for a kernel failure three times in this repository.
PRELUDE = NL.join([
    "set_option maxRecDepth 8000000",
    "set_option maxHeartbeats 0",
    "",
    "def iterAdd (x : Nat) : Nat -> Nat",
    "  | 0     => 0",
    "  | k + 1 => x + iterAdd x k",
    "",
    "def iterShift (x : Nat) : Nat -> Nat",
    "  | 0     => x",
    "  | k + 1 => ((iterShift x k) >>> 1) ||| x",
    "",
    "def iterMod (x m : Nat) : Nat -> Nat",
    "  | 0     => x",
    "  | k + 1 => ((iterMod x m k) % m) ||| x",
    "",
])


def sim_add(w: int, reps: int) -> int:
    x = 1 << w
    return reps * x


def sim_shift(w: int, reps: int) -> int:
    x = 1 << w
    v = x
    for _ in range(reps):
        v = (v >> 1) | x
    return v


def sim_mod(w: int, reps: int) -> int:
    x = 1 << w
    m = 1 << w
    v = x
    for _ in range(reps):
        v = (v % m) | x
    return v


# name -> (expression template in {W} and {R}, simulator)
#
# Every case ends in `% 2` so the answer is one digit: the kernel still performs
# every operation, but neither the parser nor the printer handles a wide literal,
# which would otherwise be charged to the operation under test. The expected
# parity comes from the simulator, not from a guess.
CASES = [
    ("add", "iterAdd (1 <<< {W}) {R} % 2", sim_add),
    ("shiftRight and or", "iterShift (1 <<< {W}) {R} % 2", sim_shift),
    ("mod", "iterMod (1 <<< {W}) (1 <<< {W}) {R} % 2", sim_mod),
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
        # The temp file name leads every message and is noise, and truncating
        # the message to make room for it is how the last run reported a
        # filename where an explanation belonged.
        msg = re.sub(r"tmp\w+\.lean:", "", (proc.stdout + proc.stderr).strip())
        return None, " ".join(msg.split())[:150]
    return dt, "ok"


def main() -> int:
    ap = argparse.ArgumentParser()
    # 1 bit is nothing, 64 is one machine word, 601 and 2,701 are the packed
    # row's field width and row width at n = 36, and 20,301 is the row width at
    # n = 100, where the entry is slow enough to time directly.
    ap.add_argument("--widths", default="1,64,601,2701,20301")
    ap.add_argument("--reps", type=int, default=20000)
    ap.add_argument("--timeout", type=float, default=300.0)
    args = ap.parse_args()

    widths = [int(w) for w in args.widths.split(",")]
    reps = args.reps
    trivial = PRELUDE + "theorem b : 1 + 1 = 2 := by rfl" + NL

    # Warm up first: the very first invocation in a fresh package compiles
    # oleans, and measuring that as the baseline is what made the last run
    # subtract 12.74 s from every cell.
    warm, status = time_src(trivial, args.timeout)
    if warm is None:
        print(f"  warm-up did not run: {status}")
        return 1
    samples = []
    for _ in range(3):
        dt, status = time_src(trivial, args.timeout)
        if dt is not None:
            samples.append(dt)
    if not samples:
        print(f"  baseline did not run: {status}")
        return 1
    base = min(samples)
    print(f"  {reps} reduction steps per cell, identical at every width")
    print(f"  warm-up {warm:.2f}s, baseline {base:.2f}s (min of "
          f"{len(samples)}), subtracted below")
    print(f"  raw times are shown too, so a bad baseline is visible\n")

    for name, tmpl, sim in CASES:
        print(f"  {name}")
        print(f"    {'width':>8}{'raw':>9}{'net':>9}{'per step':>12}{'vs 1 bit':>10}")
        first: float | None = None
        for w in widths:
            expected = sim(w, reps) % 2
            expr = tmpl.replace("{W}", str(w)).replace("{R}", str(reps))
            src = PRELUDE + f"theorem b : {expr} = {expected} := by rfl" + NL
            dt, status = time_src(src, args.timeout)
            if dt is None:
                print(f"    {w:>8}   failed")
                print(f"             {status}")
                continue
            net = dt - base
            cell = f"    {w:>8}{dt:>8.2f}s{net:>8.2f}s{net / reps * 1e6:>9.2f}us"
            if first is None and net > 0.02:
                first = net
            elif first is not None:
                cell += f"{net / first:>9.1f}x"
            print(cell)
        print()

    print("  flat per-step cost   -> width is free, only the step count matters,")
    print("                          and the leader is doing far fewer steps")
    print("  rising per-step cost -> the packed row pays for its own width and")
    print("                          the field width is the thing to cut")

    # Is the per-step figure above a per-step figure at all?
    #
    # The width table came out flat at about 60 us per step, which is roughly
    # 120,000 instructions for one structural recursion step. That is several
    # hundred times what such a step should cost, and it matters because the
    # whole diagnosis rests on it: the packed entry does about 720 steps, and
    # 720 steps at 60 us is 0.043 s, close to the 0.07 s it measures. But at
    # 120,000 instructions per step the leader's 1,429,499 units would buy
    # twelve steps, which cannot compute p(36). One of the two readings is wrong.
    #
    # This tells them apart. If the time is linear in the number of steps, then
    # 60 us really is the cost of a step in this harness, and the leader must be
    # measured on something narrower than wall time -- the kernel's reduction
    # alone, with elaboration and file overhead excluded. If it is superlinear,
    # the figure is an artifact of recursion DEPTH rather than step count, this
    # instrument does not measure what the name says, and the flat width table
    # above has to be re-read in that light.
    #
    # Width is fixed at one machine word throughout, since the table above
    # established that width does not matter.
    print("\n  is that a per-step cost? time against the number of steps,")
    print("  at a fixed width of 64 bits\n")
    print(f"    {'steps':>8}{'raw':>9}{'net':>9}{'per step':>12}{'vs first':>10}")
    ladder = [reps // 4, reps // 2, reps, reps * 2]
    first_net = first_reps = None
    for r in ladder:
        if r < 100:
            continue
        expected = sim_add(64, r) % 2
        expr = f"iterAdd (1 <<< 64) {r} % 2"
        src = PRELUDE + f"theorem b : {expr} = {expected} := by rfl" + NL
        dt, status = time_src(src, args.timeout)
        if dt is None:
            print(f"    {r:>8}   failed")
            print(f"             {status}")
            continue
        net = dt - base
        cell = f"    {r:>8}{dt:>8.2f}s{net:>8.2f}s{net / r * 1e6:>9.2f}us"
        if first_net is None and net > 0.02:
            first_net, first_reps = net, r
        elif first_net is not None:
            # A linear cost gives a ratio equal to the step ratio; a quadratic
            # one gives its square. Both are printed so neither has to be
            # inferred from the per-step column by eye.
            step_ratio = r / first_reps
            cell += f"{net / first_net:>9.1f}x"
            cell += f"   (steps {step_ratio:.0f}x)"
        print(cell)
    print("\n    per step flat        -> 60 us is a real per-step cost, and the")
    print("                            judge must count kernel reduction only")
    print("    per step rising      -> the cost is in recursion depth, not steps,")
    print("                            and this instrument is the wrong one")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
