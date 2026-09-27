#!/usr/bin/env python3
# ==============================================================================
# File: report_times.py
# Description: Prints a markdown table of one or two timing runs for the CI
#   step summary, and the ratio between them where both reduced a case.
#
#   A case that did not reduce is printed as such rather than dropped. Dropping
#   it would let a candidate that fails on the largest sizes look faster than
#   one that succeeds on all of them, which is the opposite of the truth.
#
# Usage: py report_times.py starter-times.json [candidate-times.json]
# Author: Amey Thakur
# License: CC BY 4.0
# ==============================================================================

from __future__ import annotations

import json
import pathlib
import sys


def load(path: str):
    p = pathlib.Path(path)
    if not p.is_file():
        return None
    try:
        return json.loads(p.read_text(encoding="utf-8"))
    except Exception:
        return None


def cell(row) -> str:
    if row is None:
        return "-"
    if row["seconds"] is None:
        return f"**{row['status']}**"
    return f"{row['seconds']:.2f}s"


def main() -> int:
    runs = [load(a) for a in sys.argv[1:]]
    runs = [r for r in runs if r]
    if not runs:
        print("(no timings)")
        return 0

    ns = sorted({r["n"] for run in runs for r in run["rows"]})
    by = [{r["n"]: r for r in run["rows"]} for run in runs]
    labels = [run["label"] for run in runs]

    header = "| n | " + " | ".join(labels) + (" | ratio |" if len(runs) == 2 else " |")
    sep = "|---:|" + "---:|" * (len(labels) + (1 if len(runs) == 2 else 0))
    print(header)
    print(sep)
    for n in ns:
        cells = [cell(b.get(n)) for b in by]
        line = f"| {n} | " + " | ".join(cells)
        if len(runs) == 2:
            a, b = by[0].get(n), by[1].get(n)
            if a and b and a["seconds"] and b["seconds"] and b["seconds"] > 0:
                line += f" | {a['seconds'] / b['seconds']:.1f}x"
            else:
                line += " | -"
        print(line + " |")

    print()
    for run in runs:
        print(f"- **{run['label']}**: {run['reduced']} of {run['cases']} cases "
              f"reduced, {run['total_seconds']:.2f}s over those that did.")
    if len(runs) == 2 and all(r["reduced"] == r["cases"] for r in runs):
        a, b = runs[0]["total_seconds"], runs[1]["total_seconds"]
        if b > 0:
            print(f"- Overall **{a / b:.1f}x** on the cases both reduced.")
    elif len(runs) == 2:
        print("- Totals are not comparable: the two runs did not reduce the "
              "same set of cases.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
