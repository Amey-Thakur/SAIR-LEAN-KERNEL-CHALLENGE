#!/usr/bin/env python3
# ==============================================================================
# File: costmodel.py
# Description: Where polydisc's kernel work goes, counted under two models.
#
#   The live entry is the specification itself, so nothing is known about
#   which part of it is expensive. Two things could dominate and they call for
#   opposite fixes:
#
#     * the number of kernel operations, where the per-operation overhead is
#       what matters and the cure is to perform fewer of them, which is what
#       the partition entry did;
#     * the size of the operands, where the cure is to make the integers
#       smaller, and performing more operations to do it can still win.
#
#   So this counts both: operations, split by what performs them, and the
#   total bit-length passing through the multiplications and divisions, which
#   is what a bignum library's running time actually tracks.
#
#   It instruments the transcription in model.py rather than re-deriving it,
#   so the thing measured is the thing checked.
#
# Usage: py stage2/polydisc/costmodel.py
# Author: Amey Thakur
# License: CC BY 4.0
# ==============================================================================

from __future__ import annotations

import collections
import sys

sys.set_int_max_str_digits(2_000_000)

from model import (JUDGED, kbits_of, lcg_next, lcg_seed, coefficient_width,
                   trim_leading, deriv_hl, poly_of)                 # noqa: E402

OPS: collections.Counter = collections.Counter()
BITS: collections.Counter = collections.Counter()


def op(where: str, n: int = 1) -> None:
    OPS[where] += n


def mul(where: str, a: int, b: int) -> int:
    OPS[where] += 1
    BITS[where] += a.bit_length() + b.bit_length()
    return a * b


def div(where: str, a: int, b: int) -> int:
    OPS[where] += 1
    BITS[where] += a.bit_length() + b.bit_length()
    return a // b


# ------------------------------------------------- instrumented spec parts ---
def collect_coeff_word_c(words: int, shift: int, state: int) -> tuple[int, int]:
    if words == 0:
        op("setup: build the coefficient words")
        return (0, state)
    op("setup: build the coefficient words")
    op("setup: the LCG", 3)                 # multiply, add, modulus
    state2 = lcg_next(state)
    tail, final = collect_coeff_word_c(words - 1, shift + 64, state2)
    # `state' * 2 ^ shift + tail` is not small arithmetic: 2 ^ shift is a
    # `shift`-bit number, the product is 64 bits against it, and `tail` has
    # already grown to the same width. Counting these as three cheap
    # operations, as an earlier version of this file did, hid the whole of
    # the setup's bit-work.
    power = 2 ** shift
    op("setup: the power of two")
    BITS["setup: the power of two"] += shift
    placed = mul("setup: place the word", state2, power)
    op("setup: accumulate the word")
    BITS["setup: accumulate the word"] += max(shift, tail.bit_length())
    return (placed + tail, final)


def poly_of_c(n: int) -> list[int]:
    k = kbits_of(n)
    op("setup: the seed", 3)
    state = lcg_seed(n)
    out = []
    index = 1
    for _ in range(24):
        op("setup: one coefficient")
        op("setup: the width profile", 8)   # the clamped ramp, roughly
        width = coefficient_width(k, index)
        words = (width + 63) // 64
        op("setup: words needed", 2)
        word, state = collect_coeff_word_c(words, 0, state)
        op("setup: centre the coefficient", 4)   # shift, 2^(k-1), subtract, test
        coefficient = (word >> (64 * words - width)) - 2 ** (width - 1)
        out.append(1 if coefficient == 0 else coefficient)
        index += 1
    return [1] + out


def deriv_hl_c(p: list[int]) -> list[int]:
    degree = len(p) - 1
    out = []
    for i in range(degree):
        op("derivative: one term")
        # `p.getD i 0` walks i cons cells
        op("derivative: getD walks the list", i + 1)
        out.append(mul("derivative: the product", degree - i, p[i]))
    return out


def trim_c(p: list[int]) -> list[int]:
    i = 0
    while i < len(p) and p[i] == 0:
        op("PRS: trimLeading")
        i += 1
    op("PRS: trimLeading")
    return p[i:]


def cancel_c(lc_g: int, lc_r: int, coeffs: list[int],
             divisors: list[int]) -> list[int]:
    out = []
    for i, c in enumerate(coeffs):
        op("PRS: cancel one coefficient")
        if i < len(divisors):
            a = mul("PRS: cancel, the products", lc_g, c)
            b = mul("PRS: cancel, the products", lc_r, divisors[i])
            out.append(a - b)
            op("PRS: cancel, the subtraction")
        else:
            out.append(mul("PRS: cancel, the products", lc_g, c))
    op("PRS: cancel one coefficient")
    return out


def pseudo_remainder_c(dividend: list[int], divisor: list[int]):
    dividend = trim_c(dividend)
    divisor = trim_c(divisor)
    if not divisor:
        return None
    if len(dividend) < len(divisor):
        return dividend
    remaining = len(dividend) - len(divisor) + 1
    while True:
        op("PRS: one pseudo-remainder step")
        dividend = trim_c(dividend)
        if len(dividend) < len(divisor):
            lead = divisor[0]
            out = []
            power = lead ** remaining
            op("PRS: the trailing power", remaining)
            for c in dividend:
                out.append(mul("PRS: the trailing scale", power, c))
            return out
        lc_g, lc_r = divisor[0], dividend[0]
        dividend = trim_c(cancel_c(lc_g, lc_r, dividend[1:], divisor[1:]))
        remaining = max(0, remaining - 1)


def exact_divide_c(divisor: int, p: list[int]):
    out = []
    for c in p:
        op("PRS: exact division, one coefficient")
        # the specification tests divisibility and then divides: two
        # big-integer divisions where the algorithm guarantees one suffices
        div("PRS: exact division, the remainder test", c, divisor)
        if c % divisor != 0:
            return None
        out.append(div("PRS: exact division, the quotient", c, divisor))
    return out


def normal_resultant_c(f: list[int], g: list[int]):
    f = trim_c(f)
    g = trim_c(g)
    initial = True
    while True:
        op("PRS: one outer step")
        raw = pseudo_remainder_c(f, g)
        if raw is None:
            return None
        if initial:
            divided = raw
        else:
            head = f[0]
            sq = mul("PRS: the previous leading coefficient squared", head, head)
            divided = exact_divide_c(sq, raw)
            if divided is None:
                return None
        remainder = trim_c(divided)
        if not remainder:
            return 0
        if len(remainder) + 1 == len(g):
            if len(remainder) == 1:
                return remainder[0]
            f, g, initial = g, remainder, False
        else:
            return None


def disc_spec_c(n: int) -> int:
    p = poly_of_c(n)
    d = deriv_hl_c(p)
    r = normal_resultant_c(p, d)
    op("the sign", 4)
    return r


# ------------------------------------------------------------------ report ---
def main() -> int:
    from model import disc_spec

    print(f"  {'n':>8} {'k bits':>7} {'disc bits':>10} {'operations':>11} "
          f"{'bit-work':>14}")
    rows = []
    for n in JUDGED:
        OPS.clear()
        BITS.clear()
        got = disc_spec_c(n)
        want = disc_spec(n)
        if got != want:
            print(f"  instrumented run disagrees at n = {n}")
            return 1
        rows.append((n, kbits_of(n), want.bit_length(), sum(OPS.values()),
                     sum(BITS.values()), OPS.copy(), BITS.copy()))
        print(f"  2^{n.bit_length() - 1:<6} {kbits_of(n):>7} "
              f"{want.bit_length():>10} {sum(OPS.values()):>11,} "
              f"{sum(BITS.values()):>14,}")

    print()
    print("  where the operations go, at the largest judged size")
    _, _, _, total, _, ops, bits = rows[-1]
    for where, count in ops.most_common(12):
        share = count / total * 100
        print(f"      {count:>8,}  {share:5.1f}%  {where}")
    print()
    print("  where the bit-work goes, at the largest judged size")
    tb = sum(bits.values())
    for where, count in bits.most_common(8):
        print(f"      {count:>12,}  {count / tb * 100:5.1f}%  {where}")

    print()
    print("  operations are roughly flat in the coefficient width, "
          "bit-work is not:")
    for n, k, db, o, b, _, _ in rows:
        print(f"      k={k:>4}  operations {o:>8,}   bit-work {b:>14,}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
