#!/usr/bin/env python3
# ==============================================================================
# File: bulk.py
# Description: Emits one Lean file holding several hardest-difficulty cases,
#   so that a change worth a tenth of the work can actually be seen.
#
#   Why one file. timecases.py runs a case per process, which is right when
#   the question is which size is expensive. It is useless here: Lean
#   start-up is 0.95 s of every figure, the largest judged case is about
#   1.1 s of work, and two cases at the same difficulty differed from each
#   other by 0.5 s. A saving of a tenth disappears into that.
#
#   Eight distinct inputs in one process pays start-up once against about
#   nine seconds of work. They are distinct so that nothing is answered from
#   the kernel's cache, and all of difficulty level 4, where the coefficients
#   are 3,484 bits and the discriminant about 80,000, because that is where
#   the judged cost is.
#
#   The expected values come from the transcription in model.py, which that
#   file checks against Bareiss elimination on the full Sylvester matrix at
#   this very difficulty. Here the values only have to be right; the
#   independence that matters is already established there.
#
# Usage: py stage2/polydisc/bulk.py --emit > Bulk.lean
# Author: Amey Thakur
# License: CC BY 4.0
# ==============================================================================

from __future__ import annotations

import argparse
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
sys.set_int_max_str_digits(2_000_000)

from model import disc_spec, kbits_of                              # noqa: E402

# Eight distinct points inside difficulty level 4 (n >= 2^56), spread so that
# no two share a coefficient stream.
INPUTS = [
    144115188075855872,      # 2^57
    200000000000000003,
    1152921504606846976,     # 2^60
    2305843009213693951,
    4611686018427387904,     # 2^62
    7000000000000000001,
    9223372036854775783,
    9223372036854775807,     # 2^63 - 1
]


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--emit", action="store_true",
                    help="print the Lean file on stdout")
    args = ap.parse_args()

    lines = ["import Submission",
             "set_option maxRecDepth 8000000",
             "set_option maxHeartbeats 0",
             "namespace PolydiscBulk"]
    for i, n in enumerate(INPUTS):
        k = kbits_of(n)
        if k != 3484:
            print(f"input {n} is difficulty {k} bits, not 3484", file=sys.stderr)
            return 1
        value = disc_spec(n)
        lines.append(f"theorem b{i} : Submission.impl {n} = {value} := by rfl")
    lines.append("end PolydiscBulk")

    if args.emit:
        print("\n".join(lines))
    else:
        print(f"  {len(INPUTS)} level-4 cases, "
              f"{sum(len(line) for line in lines):,} characters of Lean",
              file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
