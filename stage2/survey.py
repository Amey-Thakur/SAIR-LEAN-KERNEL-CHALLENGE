#!/usr/bin/env python3
# ==============================================================================
# File: survey.py
# Description: Asks one question of a problem's shipped starter: can the Lean
#   kernel reduce `impl n` at the judged sizes at all?
#
#   That question turned out to matter. The primecount starter reduces for
#   n = 0, 1, 2 and fails for every larger n, because Nat.minFac is defined by
#   well-founded recursion and the kernel cannot unfold it. Every judged case
#   for that problem is n >= 50, so the shipped code scores nothing, and no
#   amount of tuning would have helped. The fib starter, measured the same way,
#   reduces every case in well under a second of real work. The two look alike
#   from the outside.
#
#   The expected answers come from Lean's own compiler through #eval, not from
#   a Python port of the specification. Porting polydisc's 12 KB specification
#   to check polydisc would mostly test the port. #eval runs the same
#   definitions the kernel will be asked to reduce, but through the compiler,
#   which handles well-founded recursion without difficulty. So the two passes
#   differ in exactly the thing being measured.
#
# Usage: py survey.py --problem <name> --sizes 2,4,8 [--timeout 120]
#          run from inside upstream/problems/<name>
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
import time

sys.set_int_max_str_digits(200_000)


def run_lean(src: str, timeout: float) -> tuple[int, str, float]:
    with tempfile.NamedTemporaryFile("w", suffix=".lean", dir=".",
                                     delete=False, encoding="utf-8") as fh:
        fh.write(src)
        path = pathlib.Path(fh.name)
    try:
        t0 = time.monotonic()
        p = subprocess.run(["lake", "env", "lean", path.name],
                           capture_output=True, text=True, timeout=timeout)
        return p.returncode, p.stdout + p.stderr, time.monotonic() - t0
    except subprocess.TimeoutExpired:
        return 124, f"timeout after {timeout:.0f}s", timeout
    finally:
        path.unlink(missing_ok=True)


def evaluate(n: int, timeout: float) -> tuple[str | None, str]:
    """The compiler's answer for `impl n`, which the kernel must then match."""
    code, out, _ = run_lean(f"import Submission\n#eval Submission.impl {n}\n",
                            timeout)
    if code != 0:
        return None, out.strip()[:300]
    # #eval prints the value on its own line; Int results may carry a sign
    m = re.search(r"^\s*(-?\d+)\s*$", out, re.M)
    return (m.group(1), "ok") if m else (None, out.strip()[:300])


def reduce_check(n: int, value: str, timeout: float) -> tuple[float | None, str]:
    """Whether the kernel reduces `impl n` to that literal, and how long."""
    code, out, dt = run_lean(
        "import Submission\n"
        "set_option maxRecDepth 100000 in\n"
        f"theorem t : Submission.impl {n} = {value} := by rfl\n", timeout)
    if code == 0:
        return dt, "ok"
    text = out.strip()
    # Two very different failures wear the same "rfl failed" hat. "not
    # definitionally equal" means the kernel could not reduce the term at all,
    # which is a fact about the submission. "maximum recursion depth" is a
    # limit of the elaborator running this check, which the judge's own
    # evaluation need not share. Reporting them as one thing would have called
    # the sha256 starter dead when it is only deep.
    kind = ("harness-limit: maxRecDepth"
            if "maximum recursion depth" in text
            else "does-not-reduce" if "not definitionally equal" in text
            else "other")
    return None, f"[{kind}] {text[:360]}"


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--problem", required=True)
    ap.add_argument("--sizes", required=True,
                    help="comma-separated inputs, from the judged groups")
    ap.add_argument("--timeout", type=float, default=120.0)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()

    sizes = [int(x) for x in args.sizes.split(",")]
    rows, reducible = [], 0
    print(f"  {args.problem}: {len(sizes)} sizes, {args.timeout:.0f}s each")

    for n in sizes:
        value, status = evaluate(n, args.timeout)
        if value is None:
            rows.append({"n": n, "evaluated": False, "seconds": None,
                         "status": f"#eval failed: {status}"})
            print(f"    n={n:<12} #eval FAILED  {status.splitlines()[0][:70]}")
            continue
        dt, rstatus = reduce_check(n, value, args.timeout)
        shown = value if len(value) <= 24 else f"{value[:12]}...({len(value)} digits)"
        if dt is None:
            rows.append({"n": n, "evaluated": True, "value_digits": len(value),
                         "seconds": None, "status": rstatus})
            first = rstatus.splitlines()[0][:70] if rstatus else "?"
            print(f"    n={n:<12} = {shown:<26} kernel FAILED  {first}")
        else:
            reducible += 1
            rows.append({"n": n, "evaluated": True, "value_digits": len(value),
                         "seconds": round(dt, 2), "status": "ok"})
            print(f"    n={n:<12} = {shown:<26} kernel {dt:6.2f}s")

    hard = sum(1 for r in rows if r.get("status", "").startswith("[does-not-reduce]"))
    limit = sum(1 for r in rows if r.get("status", "").startswith("[harness-limit"))
    if reducible == len(sizes):
        verdict = "every judged size reduces"
    elif hard:
        verdict = (f"{hard} of {len(sizes)} judged sizes do not reduce at all; "
                   f"the starter scores nothing on those")
    elif limit:
        verdict = (f"{limit} of {len(sizes)} hit this harness's recursion "
                   f"limit, which is not the same as failing to reduce; "
                   f"inconclusive, raise the limit or measure another way")
    else:
        verdict = f"{reducible} of {len(sizes)} reduced"
    print(f"  {verdict}")

    out = {"problem": args.problem, "rows": rows,
           "reducible": reducible, "sizes": len(sizes), "verdict": verdict}
    if args.out:
        pathlib.Path(args.out).write_text(json.dumps(out, indent=2) + "\n",
                                          encoding="utf-8")
    return 0


if __name__ == "__main__":
    sys.exit(main())
