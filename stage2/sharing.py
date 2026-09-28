#!/usr/bin/env python3
# ==============================================================================
# File: sharing.py
# Description: Does the Lean kernel evaluate a value once when it is used twice,
#   or once per use? Measured, because it has now been guessed at twice and both
#   guesses were wrong.
#
#   Why it matters here. The two-term `partition` design is exponential in n:
#   1.97 s at n = 14, 30.28 s at n = 18, timeout above -- a factor of 15.4 for
#   four more units of n, which is 2^4. The only value used twice in it is the
#   block:
#
#       let blk := zipAdd ((x :: xs).take d) prev
#       blk ++ passAux d fuel ((x :: xs).drop d) blk
#
#   If the kernel evaluates `blk` once per use, that doubles per block and the
#   design is unusable at any size. If it shares, the exponential is somewhere
#   else and the design is salvageable. These are different repairs, and the
#   difference is worth one CI run.
#
#   The contradiction this has to resolve. The packed submission's `sweep`
#   references its row parameter `R` J+1 times per row and is NOT exponential --
#   it reduces every judged size in 0.07 s. So either parameters and `let`
#   bindings are shared differently, or the packed design is fine for a reason
#   that has nothing to do with sharing. The three cases below separate them.
#
#   Method. A chain that doubles a value n times. If the kernel shares, the chain
#   costs O(n) evaluations and the time is flat in n. If it duplicates, the chain
#   costs 2^n and the time doubles with every increment. The answer is the SHAPE
#   of the column, not any single number, which is what makes this robust to the
#   runner being noisy.
#
#     let       `let v := f k; v + v`         -- a let-bound local, used twice
#     param     `twice (f k)` with `twice a = a + a`   -- a parameter, used twice
#     ctor      `(f k, f k).1 + (f k, f k).2` is not the question; instead a
#               constructor field read twice, which is how the block is used
#               when the blocks are consed rather than appended
#
# Usage: py stage2/sharing.py [--sizes 8,12,16,20] [--timeout 120]
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

# Each variant builds the same number: 2^k. The three differ only in HOW the
# doubled value is referred to twice.
#
# `nestLet`  binds it with `let` and adds it to itself.
# `nestParam` passes it to a function whose parameter is used twice.
# `nestCtor` puts it in a pair and reads both fields, which is the shape the
#            block takes when blocks are consed into a list rather than appended.
PRELUDE = NL.join([
    "set_option maxRecDepth 8000000",
    "set_option maxHeartbeats 0",
    "",
    "def nestLet : Nat -> Nat",
    "  | 0     => 1",
    "  | k + 1 => let v := nestLet k; v + v",
    "",
    "def twice (a : Nat) : Nat := a + a",
    "",
    "def nestParam : Nat -> Nat",
    "  | 0     => 1",
    "  | k + 1 => twice (nestParam k)",
    "",
    "def pairUp (a : Nat) : Nat × Nat := (a, a)",
    "",
    "def nestCtor : Nat -> Nat",
    "  | 0     => 1",
    "  | k + 1 => let p := pairUp (nestCtor k); p.1 + p.2",
    "",
])

VARIANTS = ["nestLet", "nestParam", "nestCtor"]


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
        msg = re.sub(r"tmp\w+\.lean:", "", (proc.stdout + proc.stderr).strip())
        return None, " ".join(msg.split())[:140]
    return dt, "ok"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--sizes", default="8,12,16,20")
    ap.add_argument("--timeout", type=float, default=120.0)
    args = ap.parse_args()
    sizes = [int(v) for v in args.sizes.split(",")]

    trivial = PRELUDE + "theorem b : 1 + 1 = 2 := by rfl" + NL
    time_src(trivial, args.timeout)                       # warm up the package
    base = min(x for x in
               (time_src(trivial, args.timeout)[0] for _ in range(3))
               if x is not None)
    print(f"  each cell builds 2^k by doubling k times, so a kernel that SHARES")
    print(f"  the doubled value does O(k) work and one that DUPLICATES does 2^k")
    print(f"  process startup {base:.2f}s, subtracted\n")

    print(f"  {'k':>4}" + "".join(f"{v:>14}" for v in VARIANTS))
    print("  " + "-" * (4 + 14 * len(VARIANTS)))
    for k in sizes:
        row = f"  {k:>4}"
        for v in VARIANTS:
            # 2^k, so the expected literal is exact and cheap to parse
            src = PRELUDE + f"theorem b : {v} {k} = {2 ** k} := by rfl" + NL
            dt, status = time_src(src, args.timeout)
            if dt is None:
                row += f"{status[:13]:>14}"
            else:
                row += f"{max(0.0, dt - base):>13.2f}s"
        print(row)

    print()
    print("  flat down a column      -> the kernel SHARES; the exponential in the")
    print("                             two-term design is somewhere else")
    print("  doubling down a column  -> that form DUPLICATES, and the block must")
    print("                             be restructured so it is used once")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
