#!/usr/bin/env python3
# ==============================================================================
# File: cases.py
# Description: Computes the expected answers for a problem at its judged sizes,
#   so CI can check that the kernel reduces `impl n` to the right literal.
#
#   A proof that `impl = spec` is a proof about the definitions. It does not
#   establish that the kernel can actually reduce `impl n` inside the judge's
#   time limit, and it does not catch a proof of the wrong statement. These
#   cases are the second check: the kernel has to produce the number.
#
#   The reference answers are computed here by a method deliberately unlike the
#   submission's, so agreement is evidence rather than a tautology. fib is the
#   plain two-term recurrence, not fast doubling; primecount is trial division,
#   not a sieve.
#
# Usage: py stage2/cases.py --problem fib|primecount [--out cases.json]
# Author: Amey Thakur
# License: CC BY 4.0
# ==============================================================================

from __future__ import annotations

import argparse
import json
import pathlib
import sys

# F(150000) has about 31,000 decimal digits, past CPython's default limit on
# converting an integer to a string. The limit is a denial-of-service guard on
# untrusted input, not a correctness one, and these integers are ours.
sys.set_int_max_str_digits(200_000)

# The judged ranges, from rules/problems/<name>.md. The endpoints of each group
# are used, plus small values where the answer is known by hand.
PLANS = {
    "fib": {
        "groups": [(5_000, 10_000), (20_000, 40_000), (80_000, 150_000)],
        "small": [0, 1, 2, 3, 10, 20, 50],
    },
    "primecount": {
        "groups": [(50, 100), (150, 300), (600, 1_000)],
        "small": [0, 1, 2, 3, 10, 30],
    },
    "mertens": {
        "groups": [(25, 50), (80, 150), (300, 500)],
        "small": [0, 1, 2, 3, 10],
    },
}


def fib_plain(n: int) -> int:
    """The specification's own recurrence, iteratively. Not fast doubling."""
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a


def pi_trial(n: int) -> int:
    """Count primes up to n by trial division. Not a sieve."""
    def prime(p: int) -> bool:
        if p < 2:
            return False
        d = 2
        while d * d <= p:
            if p % d == 0:
                return False
            d += 1
        return True
    return sum(1 for k in range(n + 1) if prime(k))


def mertens_trial(n: int) -> int:
    """Sum the Moebius function by factorising each k. Mathlib puts mu(0) = 0."""
    def mu(k: int) -> int:
        if k == 0:
            return 0
        if k == 1:
            return 1
        distinct, m, d = 0, k, 2
        while d * d <= m:
            if m % d == 0:
                m //= d
                if m % d == 0:      # a squared prime factor
                    return 0
                distinct += 1
            d += 1
        if m > 1:
            distinct += 1
        return -1 if distinct % 2 else 1
    return sum(mu(k) for k in range(n + 1))


REFERENCE = {"fib": fib_plain, "primecount": pi_trial,
             "mertens": mertens_trial}

# A few values that are known independently of any code here, so a systematic
# error in the reference above cannot pass unnoticed.
KNOWN = {
    "fib": {0: 0, 1: 1, 2: 1, 3: 2, 10: 55, 20: 6765, 50: 12586269025},
    "primecount": {0: 0, 1: 0, 2: 1, 3: 2, 10: 4, 30: 10, 100: 25, 1000: 168},
    # Mertens values. These are cross-checked against a linear sieve for mu,
    # which shares no code with the trial-division reference above; the two
    # agree at every k up to 500. An earlier version of this line carried
    # M(500) = -7 from memory, the check caught it, and -6 is what both
    # methods give.
    "mertens": {0: 0, 1: 1, 2: 0, 3: -1, 10: -1, 100: 1, 300: -5, 500: -6},
}


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--problem", required=True, choices=sorted(PLANS))
    ap.add_argument("--out", default=None)
    args = ap.parse_args()

    plan = PLANS[args.problem]
    ref = REFERENCE[args.problem]

    ns = sorted(set(plan["small"]) | {n for g in plan["groups"] for n in g})

    # cross-check against the values known by hand before trusting the rest
    bad = [f"n={n}: reference {ref(n)}, known {v}"
           for n, v in KNOWN[args.problem].items() if ref(n) != v]
    if bad:
        for b in bad:
            print(f"  FAIL  {b}")
        return 1
    print(f"  reference agrees with {len(KNOWN[args.problem])} "
          f"independently known values")

    cases = [{"n": n, "value": ref(n)} for n in ns]
    for c in cases[:8]:
        v = str(c["value"])
        shown = v if len(v) <= 40 else f"{v[:18]}...{v[-12:]} ({len(v)} digits)"
        print(f"    n={c['n']:<8} {shown}")
    if len(cases) > 8:
        big = cases[-1]
        print(f"    ... largest n={big['n']}, "
              f"{len(str(big['value']))} digits")

    out = pathlib.Path(args.out or
                       pathlib.Path(__file__).parent / args.problem / "cases.json")
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps({"problem": args.problem, "cases": cases},
                              indent=2) + "\n", encoding="utf-8")
    print(f"  {len(cases)} cases written to {out}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
