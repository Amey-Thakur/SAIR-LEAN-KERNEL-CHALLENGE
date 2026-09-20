#!/usr/bin/env python3
# ==============================================================================
# File: compare.py
# Description: Prints two bench runs side by side and says which is faster, per
#   case and in total. Both runs happen on the same runner in the same job, so
#   the ratio between them survives the fact that the absolute numbers do not.
#
# Usage: py stage2/compare.py baseline.json candidate.json
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
    return json.loads(p.read_text(encoding="utf-8"))


def main() -> int:
    if len(sys.argv) != 3:
        print("usage: compare.py BASELINE.json CANDIDATE.json")
        return 2
    base, cand = load(sys.argv[1]), load(sys.argv[2])

    for name, run in (("baseline", base), ("candidate", cand)):
        if run is None:
            print(f"  {name}: no measurements were written")
        elif run.get("build") != "ok":
            print(f"  {name}: {run.get('build')}")
    if not base or not cand or base.get("build") != "ok" or cand.get("build") != "ok":
        return 1

    cases = sorted({int(k) for k in base["cases"]} | {int(k) for k in cand["cases"]})
    print()
    print(f"  {'n':>4}  {'baseline':>10}  {'candidate':>10}  {'speedup':>9}")
    print("  " + "-" * 40)
    for n in cases:
        b = base["cases"].get(str(n))
        c = cand["cases"].get(str(n))
        bs = f"{b:8.2f}s" if b is not None else "       --"
        cs = f"{c:8.2f}s" if c is not None else "       --"
        ratio = f"{b / c:8.2f}x" if b and c else "       --"
        print(f"  {n:>4}  {bs:>10}  {cs:>10}  {ratio:>9}")

    bt, ct = base.get("total_seconds"), cand.get("total_seconds")
    print("  " + "-" * 40)
    if bt and ct:
        print(f"  {'total':>4}  {bt:8.2f}s  {ct:8.2f}s  {bt / ct:8.2f}x")
        print()
        faster = "candidate" if ct < bt else "baseline"
        print(f"  {faster} is faster on total kernel wall time")
    else:
        print("  no total: not every case completed")
    print()
    print("  Wall time on a virtualised runner, not the judge's instruction count.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
