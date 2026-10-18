#!/usr/bin/env python3
# ==============================================================================
# File: model.py
# Description: Transcribes the locked polydisc specification, and checks it
#   against an independent discriminant.
#
#   The live entry for polydisc is `impl := discSpec`, the specification
#   itself, so there is no candidate yet and nothing is known about where its
#   kernel work goes. Writing the Lean first would mean debugging an algorithm
#   and a proof at once, through a CI round trip, with no toolchain on this
#   machine. The specification is transcribed here instead, where a
#   disagreement costs a second.
#
#   The check is a resultant computed by a different route: the discriminant
#   of a monic p is (-1)^(d(d-1)/2) * Res(p, p'), and Res is computed here by
#   plain fraction-free elimination on the full Sylvester matrix rather than
#   by the specification's subresultant PRS. Agreement is then evidence
#   rather than a tautology.
#
# Usage: py stage2/polydisc/model.py
# Author: Amey Thakur
# License: CC BY 4.0
# ==============================================================================

from __future__ import annotations

import sys

sys.set_int_max_str_digits(2_000_000)

# ------------------------------------------------- the locked specification --
LCG_A = 6364136223846793005
LCG_C = 1442695040888963407
LCG_M = 18446744073709551616


def lcg_next(state: int) -> int:
    return (LCG_A * state + LCG_C) % LCG_M


def lcg_seed(n: int) -> int:
    return (LCG_A * (n + 1) + LCG_C) % LCG_M


def difficulty_level(n: int) -> int:
    if n < 67108864:
        return 0
    if n < 68719476736:
        return 1
    if n < 70368744177664:
        return 2
    if n < 72057594037927936:
        return 3
    return 4


def kbits_of(n: int) -> int:
    return (15, 36, 205, 1001, 3484)[difficulty_level(n)]


def clamp_width(k: int, width: int) -> int:
    return min(k, max(2, width))


def coefficient_width(k: int, i: int) -> int:
    """Nat arithmetic: `-` truncates at zero and `/` floors."""
    if k <= 64:
        base = 2 * max(0, 36 - k) // 7
        span = 10 + base
        return clamp_width(k, base + max(0, k - base) * i // span)
    numerator = (k - 3) * (102 * 24 * i - 2 * i * i)
    denominator = 100 * 576
    return clamp_width(k, 3 + (numerator + denominator - 1) // denominator)


def collect_coeff_word(words: int, shift: int, state: int) -> tuple[int, int]:
    if words == 0:
        return (0, state)
    state2 = lcg_next(state)
    tail, final = collect_coeff_word(words - 1, shift + 64, state2)
    return (state2 * 2 ** shift + tail, final)


def centered_nonzero_coeff(k: int, words: int, word: int) -> int:
    coefficient = (word >> (64 * words - k)) - 2 ** (k - 1)
    return 1 if coefficient == 0 else coefficient


def coefficients_from(count: int, k: int, index: int, state: int) -> list[int]:
    out = []
    for _ in range(count):
        width = coefficient_width(k, index)
        words = (width + 63) // 64
        word, state = collect_coeff_word(words, 0, state)
        out.append(centered_nonzero_coeff(width, words, word))
        index += 1
    return out


def poly_of(n: int) -> list[int]:
    """Monic, degree 24, coefficients high to low."""
    k = kbits_of(n)
    return [1] + coefficients_from(24, k, 1, lcg_seed(n))


def deriv_hl(p: list[int]) -> list[int]:
    degree = len(p) - 1
    return [(degree - i) * p[i] for i in range(degree)]


def trim_leading(p: list[int]) -> list[int]:
    i = 0
    while i < len(p) and p[i] == 0:
        i += 1
    return p[i:]


def scale_polynomial(factor: int, p: list[int]) -> list[int]:
    return [factor * c for c in p]


def cancel_pseudo_leading(lc_g: int, lc_r: int, coeffs: list[int],
                          divisors: list[int]) -> list[int]:
    out = []
    for i, c in enumerate(coeffs):
        if i < len(divisors):
            out.append(lc_g * c - lc_r * divisors[i])
        else:
            out.append(lc_g * c)
    return out


def pseudo_remainder(dividend: list[int], divisor: list[int]) -> list[int] | None:
    dividend = trim_leading(dividend)
    divisor = trim_leading(divisor)
    if not divisor:
        return None
    if len(dividend) < len(divisor):
        return dividend
    fuel = len(dividend) + 1
    remaining = len(dividend) - len(divisor) + 1
    while True:
        if fuel == 0:
            return None
        fuel -= 1
        dividend = trim_leading(dividend)
        if len(dividend) < len(divisor):
            lead = divisor[0] if divisor else 0
            return scale_polynomial(lead ** remaining, dividend)
        if not divisor or not dividend:
            return None
        lc_g, lc_r = divisor[0], dividend[0]
        dividend = trim_leading(
            cancel_pseudo_leading(lc_g, lc_r, dividend[1:], divisor[1:]))
        remaining = max(0, remaining - 1)


def exact_divide_polynomial(divisor: int, p: list[int]) -> list[int] | None:
    out = []
    for c in p:
        if divisor == 0 or c % divisor != 0:
            return None
        out.append(c // divisor)
    return out


def normal_resultant(f: list[int], g: list[int]) -> int | None:
    f = trim_leading(f)
    g = trim_leading(g)
    if not (len(f) == len(g) + 1 and g):
        return None
    fuel = len(g) + 1
    initial = True
    while True:
        if fuel == 0:
            return None
        fuel -= 1
        raw = pseudo_remainder(f, g)
        if raw is None:
            return None
        if initial:
            divided = raw
        else:
            head = f[0] if f else 0
            divided = exact_divide_polynomial(head ** 2, raw)
            if divided is None:
                return None
        remainder = trim_leading(divided)
        if not remainder:
            return 0
        if len(remainder) + 1 == len(g):
            if len(remainder) == 1:
                return remainder[0]
            f, g, initial = g, remainder, False
        else:
            return None


def resultant_from_poly(p: list[int]) -> int:
    d = deriv_hl(p)
    r = normal_resultant(p, d)
    if r is None:
        raise RuntimeError("the Bareiss fallback was reached; model it too")
    return r


def disc_spec(n: int) -> int:
    p = poly_of(n)
    degree = len(p) - 1
    sign = 1 if (degree * (degree - 1) // 2) % 2 == 0 else -1
    return sign * resultant_from_poly(p)


# ------------------------------------------- an independent discriminant -----
def sylvester_resultant(p: list[int], q: list[int]) -> int:
    """Res(p, q) by Bareiss elimination on the full Sylvester matrix.

    Deliberately not the specification's route: no subresultant PRS, no
    exact-division shortcut, no monic reduction.
    """
    m, n = len(p) - 1, len(q) - 1
    size = m + n
    rows = [[0] * size for _ in range(size)]
    for i in range(n):
        for j, c in enumerate(p):
            rows[i][i + j] = c
    for i in range(m):
        for j, c in enumerate(q):
            rows[n + i][i + j] = c
    sign, prev = 1, 1
    for k in range(size - 1):
        if rows[k][k] == 0:
            swap = next((r for r in range(k + 1, size) if rows[r][k] != 0), None)
            if swap is None:
                return 0
            rows[k], rows[swap] = rows[swap], rows[k]
            sign = -sign
        for i in range(k + 1, size):
            for j in range(k + 1, size):
                rows[i][j] = (rows[k][k] * rows[i][j]
                              - rows[i][k] * rows[k][j]) // prev
            rows[i][k] = 0
        prev = rows[k][k]
    return sign * rows[size - 1][size - 1]


def disc_independent(n: int) -> int:
    p = poly_of(n)
    d = deriv_hl(p)
    degree = len(p) - 1
    sign = 1 if (degree * (degree - 1) // 2) % 2 == 0 else -1
    return sign * sylvester_resultant(p, d)


# ------------------------------------------------------------------ checks ---
JUDGED = [2 ** 18, 2 ** 25, 2 ** 37, 2 ** 45, 2 ** 57, 2 ** 63 - 1]
SMALL = [0, 1, 2, 3, 1000]


def main() -> int:
    import json
    import pathlib
    import time

    bad = []
    cases = []
    for n in SMALL + JUDGED:
        k = kbits_of(n)
        t0 = time.monotonic()
        a = disc_spec(n)
        t1 = time.monotonic()
        b = disc_independent(n)
        t2 = time.monotonic()
        ok = a == b
        if not ok:
            bad.append(n)
        cases.append({"n": n, "value": a})
        print(f"  n = {n:<20} k = {k:>4} bits   disc {a.bit_length():>6} bits"
              f"   spec {t1 - t0:6.2f}s  independent {t2 - t1:6.2f}s   "
              f"{'agrees' if ok else 'DISAGREES'}")

    out = pathlib.Path(__file__).resolve().parent / "cases.json"
    out.write_text(json.dumps(
        {"problem": "polydisc",
         "note": "values computed by the specification and confirmed against "
                 "Bareiss elimination on the full Sylvester matrix, which is "
                 "a different route: no subresultant PRS and no monic "
                 "reduction",
         "cases": cases}, indent=2) + "\n", encoding="utf-8")

    print()
    print(f"  {len(cases) - len(bad)} of {len(cases)} values agree with an "
          f"independently computed discriminant")
    print(f"  wrote {out.name}")
    return 1 if bad else 0


if __name__ == "__main__":
    raise SystemExit(main())
