#!/usr/bin/env python3
# ==============================================================================
# File: bench.py
# Description: Measures what a candidate submission costs the Lean kernel, by
#   building it in the upstream problem package and then forcing the kernel to
#   reduce `impl n` at each test size.
#
#   The official judge counts hardware instructions through perf_event_open,
#   which a virtualised CI runner does not expose, so what is reported here is
#   wall time. That is the same thing the upstream local evaluator reports, and
#   it is enough to rank two designs against each other, which is the only
#   question this script is asked. It is not an official score.
#
#   Expected answers are computed here from the specification's own recurrence,
#   independently of the submission, so a wrong answer cannot be measured as a
#   fast one.
#
# Usage: py stage2/bench.py --upstream DIR --problem partition
#          --submission FILE [--label NAME]
# Author: Amey Thakur
# License: CC BY 4.0
# ==============================================================================

from __future__ import annotations

import argparse
import json
import pathlib
import shutil
import subprocess
import sys
import time

# The published group endpoints. Unseeded local runs use exactly these.
CASES = {"partition": [14, 18, 22, 26, 32, 36]}

# Per-case watchdogs, by group, from the problem page.
TIMEOUT = {14: 30, 18: 30, 22: 60, 26: 60, 32: 120, 36: 120}


def partition_reference(n: int) -> int:
    """p(n) from the spec's recurrence, memoised. Independent of the submission."""
    table = [[0] * (n + 1) for _ in range(n + 1)]
    for m in range(n + 1):
        table[0][m] = 1 if m == 0 else 0
    for k in range(1, n + 1):
        for m in range(n + 1):
            table[k][m] = sum(table[k - 1][m - j * k] for j in range(m // k + 1))
    return table[n][n]


def run(cmd, cwd, timeout=None):
    started = time.monotonic()
    proc = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True,
                          timeout=timeout)
    return proc, time.monotonic() - started


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--upstream", required=True,
                    help="checkout of SAIRcompetition/lean-kernel-challenge")
    ap.add_argument("--problem", default="partition")
    ap.add_argument("--submission", required=True)
    ap.add_argument("--label", default=None)
    ap.add_argument("--out", default=None)
    ap.add_argument("--sizes", default=None,
                    help="comma-separated n values, in place of the judged ones. "
                         "The judged sizes finish too fast to time on a "
                         "virtualised runner, so larger ones are used to "
                         "separate designs; the ordering carries over.")
    args = ap.parse_args()

    label = args.label or pathlib.Path(args.submission).parent.name
    pkg = pathlib.Path(args.upstream).resolve() / "problems" / args.problem
    if not pkg.is_dir():
        print(f"  no such problem package: {pkg}")
        return 2

    print(f"=== {label} :: {args.problem} " + "=" * 40)
    shutil.copyfile(args.submission, pkg / "Submission.lean")

    result = {"label": label, "problem": args.problem, "cases": {}}

    # The proof is a gate, not a score: it either checks or the entry is
    # rejected however fast the computation is.
    proc, seconds = run(["lake", "build"], cwd=pkg, timeout=1800)
    result["build_seconds"] = round(seconds, 2)
    if proc.returncode != 0:
        print(f"  BUILD FAILED after {seconds:.1f}s")
        print(proc.stdout[-6000:])
        print(proc.stderr[-6000:])
        result["build"] = "failed"
        _write(args.out, result)
        return 1
    print(f"  proof checks, {seconds:.1f}s")
    result["build"] = "ok"

    # Whatever the proof rests on has to be one of the three permitted axioms.
    axioms = pkg / "Axioms.lean"
    axioms.write_text("import Submission\n#print axioms Submission.impl_correct\n",
                      encoding="utf-8")
    proc, _ = run(["lake", "env", "lean", "Axioms.lean"], cwd=pkg, timeout=600)
    axiom_line = (proc.stdout + proc.stderr).strip()
    print(f"  {axiom_line}")
    result["axioms"] = axiom_line
    axioms.unlink()
    # Anything outside the three permitted axioms is a rejection, so the whole
    # named set is checked rather than a list of known-bad ones.
    permitted = {"propext", "Quot.sound", "Classical.choice"}
    named = {w.strip(" ,[]'") for w in axiom_line.split()}
    named = {w for w in named if "." in w or w in permitted or w.endswith("Ax")}
    extra = named - permitted - {"Submission.impl_correct"}
    if extra:
        print(f"  DISQUALIFYING AXIOM: {sorted(extra)}")
        result["build"] = "forbidden-axiom"
        _write(args.out, result)
        return 1

    # Starting Lean and reading the built module costs the same in every
    # variant, and at the small sizes it is most of the measurement. It is
    # measured once here and taken off each case, so what is reported is the
    # reduction rather than the process.
    overhead = _time_one(pkg, 0, 1, TIMEOUT[14])
    result["overhead_seconds"] = round(overhead, 3) if overhead else None
    print(f"  fixed overhead per measurement {overhead:.2f}s, subtracted below"
          if overhead else "  overhead unmeasured; raw times reported")

    sizes = ([int(x) for x in args.sizes.split(",")] if args.sizes
             else CASES[args.problem])

    total = 0.0
    for n in sizes:
        want = partition_reference(n)
        seconds = _time_one(pkg, n, want, TIMEOUT.get(n, 120))
        if seconds is None:
            print(f"  n={n:>3}  did not produce a measurement")
            result["cases"][n] = None
            continue
        net = max(seconds - (overhead or 0.0), 0.0)
        total += net
        result["cases"][n] = round(net, 3)
        print(f"  n={n:>3}  p(n)={want:<9} {net:7.2f}s net "
              f"({seconds:.2f}s raw)")

    complete = all(v is not None for v in result["cases"].values())
    result["total_seconds"] = round(total, 2) if complete else None
    print(f"  total {total:.2f}s over {len(sizes)} cases"
          if complete else "  incomplete: no total")
    _write(args.out, result)
    return 0 if complete else 1


def _time_one(pkg, n, want, watchdog):
    """Time the kernel reducing `impl n` to its literal. None if it did not run.

    The recursion and heartbeat caps are elaborator limits, not kernel ones;
    left at their defaults they measure the cap rather than the algorithm.
    Raising them for every variant alike keeps the comparison fair.
    """
    bench = pkg / "Bench.lean"
    bench.write_text(
        "import Submission\n"
        "set_option maxRecDepth 1000000\n"
        "set_option maxHeartbeats 0\n"
        f"theorem bench : Submission.impl {n} = {want} := rfl\n",
        encoding="utf-8")
    try:
        proc, seconds = run(["lake", "env", "lean", "Bench.lean"], cwd=pkg,
                            timeout=watchdog * 4)
    except subprocess.TimeoutExpired:
        print(f"  n={n:>3}  TIMEOUT past {watchdog * 4}s")
        bench.unlink()
        return None
    bench.unlink()
    if proc.returncode != 0:
        print(f"  n={n:>3}  FAILED  {(proc.stdout + proc.stderr)[:400]}")
        return None
    return seconds


def _write(out, result):
    if out:
        pathlib.Path(out).write_text(json.dumps(result, indent=2), encoding="utf-8")


if __name__ == "__main__":
    sys.exit(main())
