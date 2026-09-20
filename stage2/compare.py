#!/usr/bin/env python3
# ==============================================================================
# File: compare.py
# Description: Prints several bench runs side by side against the first one,
#   per case and in total. Every run happens on the same runner in the same
#   job, so the ratios between them survive the fact that the absolute numbers
#   do not.
#
# Usage: py stage2/compare.py baseline.json candidate.json [more.json ...]
# Author: Amey Thakur
# License: CC BY 4.0
# ==============================================================================

from __future__ import annotations

import json
import pathlib
import sys


def load(path):
    p = pathlib.Path(path)
    if not p.exists():
        return None
    try:
        return json.loads(p.read_text(encoding="utf-8"))
    except json.JSONDecodeError:
        return None


def main() -> int:
    if len(sys.argv) < 3:
        print("usage: compare.py BASELINE.json RUN.json [RUN.json ...]")
        return 2

    runs = [(pathlib.Path(a).stem, load(a)) for a in sys.argv[1:]]
    for name, run in runs:
        if run is None:
            print(f"  {name}: no measurements were written")
        elif run.get("build") != "ok":
            print(f"  {name}: {run.get('build')}")

    usable = [(n, r) for n, r in runs if r and r.get("build") == "ok"]
    if len(usable) < 2:
        print("  fewer than two runs completed; nothing to compare")
        return 1

    base_name, base = usable[0]
    cases = sorted({int(k) for _, r in usable for k in r["cases"]})

    head = f"  {'n':>4}  {base_name:>11}"
    for name, _ in usable[1:]:
        head += f"  {name:>11}  {'x':>8}"
    print()
    print(head)
    print("  " + "-" * (len(head) - 2))

    for n in cases:
        b = base["cases"].get(str(n))
        line = f"  {n:>4}  " + (f"{b:10.2f}s" if b is not None else "        -- ")
        for _, r in usable[1:]:
            c = r["cases"].get(str(n))
            line += "  " + (f"{c:10.2f}s" if c is not None else "        -- ")
            line += "  " + (f"{b / c:7.1f}x" if b and c else "      --")
        print(line)

    print("  " + "-" * (len(head) - 2))
    bt = base.get("total_seconds")
    line = f"  {'all':>4}  " + (f"{bt:10.2f}s" if bt else "        -- ")
    for _, r in usable[1:]:
        ct = r.get("total_seconds")
        line += "  " + (f"{ct:10.2f}s" if ct else "        -- ")
        line += "  " + (f"{bt / ct:7.1f}x" if bt and ct else "      --")
    print(line)

    ranked = [(r.get("total_seconds"), n) for n, r in usable if r.get("total_seconds")]
    if ranked:
        print()
        for seconds, name in sorted(ranked):
            print(f"  {name:>12}  {seconds:8.2f}s")
        print(f"\n  fastest: {sorted(ranked)[0][1]}")
    print()
    print("  Wall time on a virtualised runner, not the judge's instruction count.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
