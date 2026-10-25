#!/usr/bin/env python3
# ==============================================================================
# File: profkernel.py
# Description: Measures any problem at the boundary the judge measures, by
#   reading Lean's own profiler rather than the clock.
#
#   What the judge counts, from rules/evaluation.md: "In three separate
#   processes, count only the target declaration's kernel check, which reduces
#   `impl n` and compares it with `v`." Not parsing, not elaboration.
#
#   Lean's profiler reports a cumulative `type checking` figure, and type
#   checking is `Environment.addDecl`, which is the kernel. That is the same
#   boundary. `stage2/fib/measure.sh` established this on 18 October 2026, when
#   it showed that every `fib` figure this repository had recorded before then
#   was a measurement of Lean's parser: a file containing only the expected
#   31,348-digit literal, with `impl` appearing nowhere, cost the same 0.28 s
#   as the full assertion, while forcing the identical reduction against a
#   cheap right-hand side cost nothing measurable.
#
#   This is the generic version of that instrument. It is needed wherever
#   start-up dominates: a Mathlib package pays about 1.74 s before it does any
#   work, so a whole-process figure cannot resolve a change of 1.4x in a
#   computation that takes a fraction of a second.
#
# Usage: py stage2/profkernel.py --cases stage2/primecount/cases.json
#          --label candidate [--reps 2] [--min-n 50] [--out k.tsv]
#        run with cwd = upstream/problems/<problem>
# Author: Amey Thakur
# License: CC BY 4.0
# ==============================================================================

from __future__ import annotations

import argparse
import json
import pathlib
import re
import subprocess
import sys
import tempfile

sys.set_int_max_str_digits(200_000)

# The profiler prints a cumulative line per phase, in seconds or milliseconds.
PHASE = re.compile(r"^\s*type checking\s+([0-9.]+)(ms|s)\s*$", re.M)


def kernel_ms(text: str) -> float | None:
    """The last cumulative `type checking` figure, in milliseconds."""
    hits = PHASE.findall(text)
    if not hits:
        return None
    value, unit = hits[-1]
    return float(value) * (1.0 if unit == "ms" else 1000.0)


def run(cases: list[dict], label: str, reps: int) -> list[float]:
    """One process per repetition, every case in it, profiler on."""
    body = [
        "import Submission",
        "set_option maxRecDepth 8000000",
        "set_option maxHeartbeats 0",
        "set_option profiler true",
        "set_option profiler.threshold 1",
        "namespace Prof",
    ]
    for i, c in enumerate(cases):
        body.append(f"theorem k{i} : Submission.impl {c['n']} "
                    f"= {c['value']} := by rfl")
    body.append("end Prof")
    src = "\n".join(body) + "\n"

    out: list[float] = []
    for _ in range(reps):
        with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=".",
                                         delete=False,
                                         encoding="utf-8") as fh:
            fh.write(src)
            path = pathlib.Path(fh.name)
        try:
            proc = subprocess.run(["lake", "env", "lean", path.name],
                                  capture_output=True, text=True,
                                  encoding="utf-8", errors="replace",
                                  timeout=1800)
            blob = (proc.stdout or "") + (proc.stderr or "")
            if "error" in blob.lower():
                first = next((ln for ln in blob.splitlines()
                              if "error" in ln.lower()), "")
                print(f"  {label}: ERROR  {first[:120]}")
                return []
            ms = kernel_ms(blob)
            if ms is None:
                print(f"  {label}: no `type checking` line; "
                      "is the profiler threshold too high?")
                return []
            out.append(ms)
        finally:
            path.unlink(missing_ok=True)
    return out


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--cases", required=True)
    ap.add_argument("--label", required=True)
    ap.add_argument("--reps", type=int, default=2)
    ap.add_argument("--min-n", type=int, default=0,
                    help="skip cases below this n; the tiny ones are noise")
    ap.add_argument("--out")
    a = ap.parse_args()

    data = json.loads(pathlib.Path(a.cases).read_text(encoding="utf-8"))
    cases = [c for c in data["cases"] if int(c["n"]) >= a.min_n]
    if not cases:
        print("  no cases at or above --min-n")
        return 1

    runs = run(cases, a.label, a.reps)
    if not runs:
        return 1
    best = min(runs)
    print(f"  {a.label:<12} {len(cases):>3} cases   "
          f"kernel {best:>10.1f} ms   runs {[round(r, 1) for r in runs]}")
    if a.out:
        with open(a.out, "a", encoding="utf-8") as fh:
            fh.write(f"{a.label}\t{len(cases)}\t{best:.3f}\t"
                     f"{';'.join(f'{r:.3f}' for r in runs)}\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
