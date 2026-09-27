#!/usr/bin/env python3
# ==============================================================================
# File: timealt.py
# Description: Times the `sweepMul` variant against the entry now on the board,
#   in one job, at sizes large enough for a shared runner to resolve.
#
#   The question. Every arithmetic primitive was measured free at sixteen times
#   the row width, so the packed entry's 132,036,341 units of judged work are
#   reduction steps rather than arithmetic. The suspect is that
#
#       sweep s R (J + 1) = R + (sweep s R J) <<< s
#
#   names the previous row `R` once in the source and `J + 1` times in the
#   unfolding, so a kernel that zeta-expands the caller's `let` recomputes the
#   previous row for every term of the sweep. `Experiment.lean` rewrites the
#   sweep as `R * sweepMul s J`, where `R` occurs exactly once and `sweepMul`
#   mentions no row at all.
#
#   Why this does not use bench.py. That script checks `impl_correct` and its
#   axioms before it times anything, which is right for a candidate and wrong
#   here: the variant carries no proof yet, deliberately, because the point is
#   to find out whether a proof is worth writing. This times a plain `rfl`
#   against an expected literal instead.
#
#   Why n = 100 to 300 rather than the judged sizes. The packed entry reduces
#   every judged size in 0.01 s, which is below the resolution of a virtualised
#   runner. At n = 100 to 300 the same entry takes 0.04 s to 0.33 s, so a real
#   difference is visible and a factor can be read off. Both implementations are
#   timed in the same job, because the same code has measured 47.89 s and
#   59.60 s on two runs of this runner and a cross-run comparison at this scale
#   would be noise.
#
#   The expected values are recomputed here from the specification's own
#   recurrence rather than copied from a previous log, so a variant that agrees
#   with the old entry while both are wrong cannot pass.
#
# Usage: py stage2/partition/timealt.py --pkg upstream/problems/partition
#          [--sizes 100,150,200,300] [--timeout 300]
# Author: Amey Thakur
# License: CC BY 4.0
# ==============================================================================

from __future__ import annotations

import argparse
import pathlib
import shutil
import subprocess
import sys
import time
from functools import lru_cache

sys.setrecursionlimit(100000)


@lru_cache(None)
def part_aux(k: int, m: int) -> int:
    """The specification's recurrence, verbatim: partitions of m into parts <= k."""
    if k == 0:
        return 1 if m == 0 else 0
    return sum(part_aux(k - 1, m - j * k) for j in range(m // k + 1))


def p(n: int) -> int:
    return part_aux(n, n)


def time_rfl(pkg: pathlib.Path, expr: str, value: int, timeout: float,
             imports: str) -> tuple[float | None, str]:
    """Seconds for the kernel to reduce `expr` to `value`, or None and why not."""
    src = (f"{imports}\n"
           "set_option maxRecDepth 8000000 in\n"
           "set_option maxHeartbeats 0 in\n"
           f"theorem bench : {expr} = {value} := by rfl\n")
    path = pkg / "TimeAlt.lean"
    path.write_text(src, encoding="utf-8")
    try:
        t0 = time.monotonic()
        proc = subprocess.run(["lake", "env", "lean", "TimeAlt.lean"],
                              cwd=pkg, capture_output=True, text=True,
                              timeout=timeout)
        dt = time.monotonic() - t0
    except subprocess.TimeoutExpired:
        return None, f"timeout after {timeout:.0f}s"
    finally:
        path.unlink(missing_ok=True)
    if proc.returncode != 0:
        lines = (proc.stdout + proc.stderr).strip().splitlines()
        return None, (lines[0] if lines else "no output")[:88]
    return dt, "ok"


def baseline(pkg: pathlib.Path, timeout: float) -> float:
    """Process startup, to be subtracted. A trivial file, timed the same way."""
    dt, _ = time_rfl(pkg, "1 + 1", 2, timeout, "import Submission")
    return dt if dt is not None else 0.0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--pkg", required=True,
                    help="the problem package, with Submission.lean in place")
    ap.add_argument("--sizes", default="100,150,200,300")
    ap.add_argument("--timeout", type=float, default=300.0)
    args = ap.parse_args()

    pkg = pathlib.Path(args.pkg)
    sizes = [int(s) for s in args.sizes.split(",")]

    here = pathlib.Path(__file__).parent
    shutil.copyfile(here / "SubmissionPacked.lean", pkg / "Submission.lean")
    shutil.copyfile(here / "Experiment.lean", pkg / "Experiment.lean")

    print("  building the entry on the board and the variant beside it")
    for target in ("Submission", "Experiment"):
        proc = subprocess.run(["lake", "env", "lean", f"{target}.lean"],
                              cwd=pkg, capture_output=True, text=True,
                              timeout=args.timeout)
        if proc.returncode != 0:
            print(f"  {target}.lean did not compile:")
            print((proc.stdout + proc.stderr)[:3000])
            return 1
        print(f"  {target}.lean compiles")

    # The variant's definitions are inlined into each timing file rather than
    # imported. `lake env lean Experiment.lean` typechecks the file but writes
    # no olean, so `import Experiment` found nothing and every variant cell
    # failed while the entry on the board timed fine -- which looked like the
    # variant being slow rather than absent. Inlining keeps Experiment.lean the
    # single source of truth: the definitions are read from it, so the timed
    # code and the code whose agreement examples the kernel checked are the same
    # text. The examples themselves are dropped, having already been checked
    # above, and would otherwise be re-reduced inside every timing run.
    # Cut at the agreement examples rather than filtering them out line by
    # line: their doc comment would then have nothing to attach to, and a
    # dangling `/-- ... -/` is a parse error, so the variant would have failed
    # again for a second reason having nothing to do with its speed.
    body = (here / "Experiment.lean").read_text(encoding="utf-8")
    marker = "/-- Agreement at small inputs"
    if marker in body:
        body = body[:body.index(marker)]
    lines = [ln for ln in body.splitlines() if not ln.startswith("import ")]
    alt_defs = chr(10).join(lines)
    # Experiment.lean carries its own kernel-checked agreement examples at
    # n = 0, 1, 5, 10, 13 and 36, so compiling it is already a correctness
    # check; it cannot compile while computing the wrong thing at those sizes.
    subprocess.run(["lake", "build"], cwd=pkg, capture_output=True, text=True,
                   timeout=args.timeout)

    base = baseline(pkg, args.timeout)
    print(f"  process startup {base:.2f}s, subtracted below\n")

    print(f"{'n':>6}{'p(n)':>22}{'on the board':>15}{'sweepMul':>12}{'factor':>9}")
    print("  " + "-" * 62)
    tot_old = tot_new = 0.0
    for n in sizes:
        value = p(n)
        old, sold = time_rfl(pkg, f"Submission.impl {n}", value, args.timeout,
                             "import Submission")
        new, snew = time_rfl(pkg, f"Alt.impl {n}", value, args.timeout,
                             "import Submission" + chr(10) + alt_defs)
        cells = f"{n:>6}{value:>22}"
        if old is None:
            cells += f"{'failed':>15}"
            print(f"         board: {sold}")
        else:
            net_old = max(0.0, old - base)
            tot_old += net_old
            cells += f"{net_old:>14.2f}s"
        if new is None:
            cells += f"{'failed':>12}"
            print(f"         variant: {snew}")
        else:
            net_new = max(0.0, new - base)
            tot_new += net_new
            cells += f"{net_new:>11.2f}s"
        if old is not None and new is not None and new - base > 0.005:
            cells += f"{(old - base) / (new - base):>8.1f}x"
        print(cells)
    print("  " + "-" * 62)
    print(f"{'total':>6}{'':>22}{tot_old:>14.2f}s{tot_new:>11.2f}s"
          + (f"{tot_old / tot_new:>8.1f}x" if tot_new > 0.005 else ""))

    print("\n  a factor near 1 clears the duplication suspect and the sweepMul")
    print("  form is not worth proving; a large factor is the 132,036,341 and")
    print("  the proof obligation is then two lemmas, sweep_zero and sweep_succ.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
