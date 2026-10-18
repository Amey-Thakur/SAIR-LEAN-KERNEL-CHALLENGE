#!/usr/bin/env python3
# ==============================================================================
# File: predict.py
# Description: What each candidate cost model predicts, per judged case, so a
#   measured per-case instruction count can be read against all of them at
#   once instead of being fitted to whichever one is believed that day.
#
#   The judged metric is an instruction count of the kernel check alone. Four
#   models could produce it, and they differ by orders of magnitude in how
#   they weigh the easy sizes against the hard ones:
#
#     operations  one unit per kernel operation, width ignored
#     linear      the sum of operand bit lengths, which is what costmodel.py
#                 already reports as "bit-work"
#     karatsuba   max(limbs)^1.585 per multiplication, GMP's actual regime
#                 for operands of this size
#     schoolbook  the product of the operand limb counts
#
#   The discriminating statistic is the RATIO between the hardest judged size
#   and the easiest, because the four models put it at 2, 101, 400 and 1,800.
#   One measurement of two cases settles it.
#
# Usage: py stage2/polydisc/predict.py
# Author: Amey Thakur
# License: CC BY 4.0
# ==============================================================================

from __future__ import annotations

import collections
import sys

sys.set_int_max_str_digits(2_000_000)

from model import (JUDGED, kbits_of, lcg_next, coefficient_width,     # noqa
                   lcg_seed)

MODELS = ("operations", "linear", "karatsuba", "schoolbook")


class Cost:
    """Accumulates every model at once, split by where the work happens."""

    def __init__(self) -> None:
        self.table = {m: collections.Counter() for m in MODELS}

    def plain(self, where: str, count: int = 1) -> None:
        self.table["operations"][where] += count
        for m in ("linear", "karatsuba", "schoolbook"):
            self.table[m][where] += count

    def mul(self, where: str, a: int, b: int) -> int:
        la = max(1, (a.bit_length() + 63) // 64)
        lb = max(1, (b.bit_length() + 63) // 64)
        self.table["operations"][where] += 1
        self.table["linear"][where] += a.bit_length() + b.bit_length() + 1
        self.table["karatsuba"][where] += int(max(la, lb) ** 1.585) + 1
        self.table["schoolbook"][where] += la * lb
        return a * b

    def div(self, where: str, a: int, b: int) -> int:
        la = max(1, (a.bit_length() + 63) // 64)
        lb = max(1, (b.bit_length() + 63) // 64)
        self.table["operations"][where] += 1
        self.table["linear"][where] += a.bit_length() + b.bit_length() + 1
        # a quotient of q limbs against a divisor of lb costs about q*lb
        self.table["karatsuba"][where] += int(max(la, lb) ** 1.585) + 1
        self.table["schoolbook"][where] += max(1, la - lb + 1) * lb
        return a // b

    def total(self, model: str) -> int:
        return sum(self.table[model].values())


def collect_word(c: Cost, words: int, state: int) -> tuple[int, int]:
    acc = 0
    for j in range(words):
        c.plain("setup: the LCG", 1)
        c.mul("setup: the LCG", 6364136223846793005, state)
        c.plain("setup: the LCG", 1)
        state = lcg_next(state)
        power = 2 ** (64 * j)
        c.plain("setup: the power of two")
        acc += c.mul("setup: place the word", state, power)
        c.plain("setup: accumulate the word")
    return acc, state


def poly(c: Cost, n: int) -> list[int]:
    k = kbits_of(n)
    c.plain("setup: the seed", 3)
    state = lcg_seed(n)
    out = [1]
    for i in range(1, 25):
        width = coefficient_width(k, i)
        c.plain("setup: the width profile", 8)
        words = (width + 63) // 64
        word, state = collect_word(c, words, state)
        c.plain("setup: centre the coefficient", 4)
        value = (word >> (64 * words - width)) - 2 ** (width - 1)
        out.append(1 if value == 0 else value)
    return out


def deriv(c: Cost, p: list[int]) -> list[int]:
    degree = len(p) - 1
    out = []
    for i in range(degree):
        c.plain("derivative: the walk", i + 2)
        out.append(c.mul("derivative: the product", degree - i, p[i]))
    return out


def prs(c: Cost, f: list[int], g: list[int]) -> int | None:
    initial = True
    while True:
        # the pseudo-remainder: two cancel passes in the normal case
        lc_g, lc_f = g[0], f[0]
        h = []
        for i in range(1, len(f)):
            c.plain("PRS: cancel, the structure", 2)
            a = c.mul("PRS: cancel, the products", lc_g, f[i])
            if i < len(g):
                b = c.mul("PRS: cancel, the products", lc_f, g[i])
                c.plain("PRS: cancel, the subtraction")
                h.append(a - b)
            else:
                h.append(a)
        lc_h = h[0]
        u = []
        for i in range(1, len(h)):
            c.plain("PRS: cancel, the structure", 2)
            a = c.mul("PRS: cancel, the products", lc_g, h[i])
            b = c.mul("PRS: cancel, the products", lc_h, g[i])
            c.plain("PRS: cancel, the subtraction")
            u.append(a - b)
        # the trailing scale by lc(g) ^ 0, which is a multiplication by one
        for i, value in enumerate(u):
            c.plain("PRS: the trailing structure")
            u[i] = c.mul("PRS: the trailing scale by one", 1, value)
        if not initial:
            sq = c.mul("PRS: the previous leading coefficient squared",
                       lc_f, lc_f)
            out = []
            for value in u:
                c.plain("PRS: exact division, the structure", 2)
                c.mul("PRS: exact division, the exactness test",
                      value // sq, sq)
                out.append(c.div("PRS: exact division, the quotient",
                                 value, sq))
            u = out
        c.plain("PRS: trimLeading", 4)
        if len(u) == 1:
            return u[0]
        f, g, initial = g, u, False


def disc(c: Cost, n: int) -> int:
    p = poly(c, n)
    d = deriv(c, p)
    return prs(c, p, d)


def main() -> int:
    from model import disc_spec

    rows = []
    for n in JUDGED:
        c = Cost()
        got = disc(c, n)
        want = disc_spec(n)
        if abs(got) != abs(want):
            print(f"  the instrumented run disagrees at n = {n}")
            return 1
        rows.append((n, kbits_of(n), c))

    print(f"  {'case':>10} {'k':>6} " +
          " ".join(f"{m:>16}" for m in MODELS))
    for n, k, c in rows:
        print(f"  2^{n.bit_length() - 1:<8} {k:>6} " +
              " ".join(f"{c.total(m):>16,}" for m in MODELS))
    print()
    print("  predicted TOTAL over the six judged cases, "
          "and the ratio hardest : easiest")
    for m in MODELS:
        total = sum(c.total(m) for _, _, c in rows)
        ratio = rows[-1][2].total(m) / rows[0][2].total(m)
        per_unit = 10_322_617_420 / total
        print(f"      {m:<11} {total:>14,}   ratio {ratio:>8.1f}   "
              f"instructions per unit if this model is right: {per_unit:,.1f}")

    print()
    print("  where the work sits at the hardest judged size, under each model")
    hardest = rows[-1][2]
    wheres = sorted(hardest.table["operations"],
                    key=lambda w: -hardest.table["karatsuba"][w])
    print(f"      {'':<46}" + " ".join(f"{m:>12}" for m in MODELS))
    for where in wheres:
        line = f"      {where:<46}"
        for m in MODELS:
            share = hardest.table[m][where] / hardest.total(m) * 100
            line += f" {share:>11.1f}%"
        print(line)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
