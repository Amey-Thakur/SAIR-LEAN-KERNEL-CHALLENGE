#!/usr/bin/env python3
# ==============================================================================
# File: bisect.py
# Description: Localises the exponential in the two-term design by timing the
#   table one row at a time, instead of guessing which subterm causes it.
#
#   The state of the question. `Submission.impl` is exponential in n: 1.97 s at
#   n = 14, 30.28 s at n = 18, timeout above, a factor of 15.4 for four more
#   units of n. Two candidate causes have been eliminated by measurement rather
#   than argument:
#
#     1. `rowsL n k` appearing twice, once for `.length` and once as the row.
#        Real, and fixed by passing the fuel; worth only 1.6x. Not the cause.
#     2. The block `blk` being used twice, in `blk ++ ...` and as the next
#        `prev`. `stage2/sharing.py` timed three chains that each build 2^k by
#        doubling k times -- through a `let`, through a parameter, and through a
#        constructor field -- and all three are flat to k = 20, where duplication
#        would cost 2^20 evaluations. The kernel shares all three. Not the cause.
#
#   So the arithmetic that seemed to fit -- 2^19 blocks at 50 us matching the
#   30.28 s -- was a coincidence, and fitting a mechanism to a single ratio is
#   how two hours went into the wrong two suspects.
#
#   What this measures instead. `rowsL n k` is the table after k passes. Timing
#   it for k = 0, 1, 2, ... at FIXED n says where the cost goes without any
#   hypothesis about which subterm is at fault:
#
#     time doubling as k grows   -> the duplication is per PASS, so it is in
#                                   `rowsL` or in how `pass` consumes its row
#     time flat in k, but the
#     whole thing still slow     -> the cost is inside a single pass, and the
#                                   pass itself is what to instrument
#     time growing smoothly      -> there is no exponential and the n-scaling
#                                   came from something else entirely
#
#   Each row is its own `lean` invocation, for the reason `timecases.py` gives:
#   one file would let a later case's elaboration overlap an earlier one and
#   report a single number that hides which row is expensive.
#
# Usage: py stage2/partition/bisect.py --pkg upstream/problems/partition
#          [--n 16] [--timeout 180]
# Author: Amey Thakur
# License: CC BY 4.0
# ==============================================================================

from __future__ import annotations

import argparse
import pathlib
import re
import shutil
import subprocess
import sys
import time
from functools import lru_cache

sys.setrecursionlimit(100000)
NL = chr(10)


@lru_cache(None)
def part_aux(k: int, m: int) -> int:
    """The specification's recurrence, so expected values are not guessed."""
    if k == 0:
        return 1 if m == 0 else 0
    return sum(part_aux(k - 1, m - j * k) for j in range(m // k + 1))


def defs_of(path: pathlib.Path) -> str:
    """The submission's definitions, without its import or its examples.

    Cut at the agreement examples rather than filtering them line by line: their
    doc comment would then have nothing to attach to, and a dangling `/-- ... -/`
    is a parse error. This is the same trap `timealt.py` hit.
    """
    body = path.read_text(encoding="utf-8")
    marker = "/-- Agreement at small inputs"
    if marker in body:
        body = body[:body.index(marker)]
    return NL.join(ln for ln in body.splitlines() if not ln.startswith("import "))


def time_rfl(pkg: pathlib.Path, prelude: str, expr: str, value: int,
             timeout: float) -> tuple[float | None, str]:
    src = ("import Spec" + NL + prelude + NL
           + "set_option maxRecDepth 8000000 in" + NL
           + "set_option maxHeartbeats 0 in" + NL
           + f"theorem bench : {expr} = {value} := by rfl" + NL)
    path = pkg / "Bisect.lean"
    path.write_text(src, encoding="utf-8")
    try:
        t0 = time.monotonic()
        proc = subprocess.run(["lake", "env", "lean", "Bisect.lean"], cwd=pkg,
                              capture_output=True, text=True, timeout=timeout)
        dt = time.monotonic() - t0
    except subprocess.TimeoutExpired:
        return None, f"timeout {timeout:.0f}s"
    finally:
        path.unlink(missing_ok=True)
    if proc.returncode != 0:
        msg = re.sub(r"Bisect\.lean:", "", (proc.stdout + proc.stderr).strip())
        return None, " ".join(msg.split())[:120]
    return dt, "ok"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--pkg", required=True)
    ap.add_argument("--n", type=int, default=16)
    ap.add_argument("--timeout", type=float, default=180.0)
    args = ap.parse_args()

    pkg = pathlib.Path(args.pkg)
    here = pathlib.Path(__file__).parent
    shutil.copyfile(here / "SubmissionTwoTerm.lean", pkg / "Submission.lean")
    prelude = defs_of(here / "SubmissionTwoTerm.lean")
    n = args.n

    base, status = time_rfl(pkg, prelude, "1 + 1", 2, args.timeout)
    if base is None:
        print(f"  baseline did not run: {status}")
        return 1
    print(f"  the table after k passes, at n = {n}, one invocation per row")
    print(f"  process startup {base:.2f}s, subtracted")
    print(f"  entry read is position {n}, whose value after k passes is")
    print(f"  partAux k {n} from the specification's own recurrence\n")

    print(f"  {'k':>4}{'partAux k n':>14}{'net':>10}{'vs previous':>13}")
    print("  " + "-" * 41)
    prev: float | None = None
    for k in range(0, n + 1):
        want = part_aux(k, n)
        expr = f"Submission.nth (Submission.rowsL {n} {k}) {n}"
        dt, status = time_rfl(pkg, prelude, expr, want, args.timeout)
        if dt is None:
            print(f"  {k:>4}{want:>14,}{status[:9]:>10}")
            prev = None
            continue
        net = max(0.0, dt - base)
        cell = f"  {k:>4}{want:>14,}{net:>9.2f}s"
        if prev is not None and prev > 0.02:
            cell += f"{net / prev:>12.1f}x"
        print(cell)
        prev = net

    print()
    print("  ratios near 2.0     -> the cost doubles per pass; the duplication")
    print("                         is in rowsL or in how pass consumes its row")
    print("  ratios near 1.0     -> flat per pass, so the cost is inside ONE")
    print("                         pass and the pass is what to instrument")
    print("  ratios rising then")
    print("  falling             -> no exponential; the n-scaling is elsewhere")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
