#!/usr/bin/env python3
# ==============================================================================
# File: fused.py
# Description: Checks the fused subresultant step against the specification's
#   own two cancellation passes, before any of it is written in Lean.
#
#   Measured: the judge charges per kernel operation and the subresultant loop
#   is where the operations are. The loop spends nine `Int` operations per
#   output coefficient:
#
#       pass 1   h[i+1] = g0*f[i+1] - f0*g[i+1]        2 mul, 1 sub
#       pass 2   u[i]   = g0*h[i+1] - h[1]*g[i]        2 mul, 1 sub
#       scale    u[i] * (g0 ^ 0)                       1 mul, always by one
#       divide   u[i] / f0^2, tested by multiplying back   1 div, 1 mul
#
#   Composing the two passes gives, with A = g0^2, B = g0*f0 and
#   C = g0*f[1] - f0*g[1],
#
#       u[i] = A*f[i+1] - B*g[i+1] - C*g[i]
#
#   which is three multiplications and two subtractions: seven operations
#   instead of nine, and the multiplication by one disappears.
#
#   The composition is only valid when the first pass does not drop a degree,
#   because the specification trims after every pass and a drop changes both
#   the number of passes and the trailing exponent. So the fused step is
#   guarded by `C != 0` and by the result's own leading coefficient being
#   nonzero, and anything else falls back to the specification's own route.
#   This file checks that the guard is right by running both on every judged
#   difficulty and on the abnormal inputs it can construct.
#
# Usage: py stage2/polydisc/fused.py
# Author: Amey Thakur
# License: CC BY 4.0
# ==============================================================================

from __future__ import annotations

import sys

sys.set_int_max_str_digits(2_000_000)

from model import (JUDGED, deriv_hl, disc_spec, normal_resultant,  # noqa: E402
                   poly_of, trim_leading)


def fused_step(f: list[int], g: list[int]) -> list[int] | None:
    """One subresultant step, fused. `None` means the guard failed and the
    specification's own route must be used."""
    if len(f) != len(g) + 1 or len(g) < 2:
        return None
    f0, g0 = f[0], g[0]
    if f0 == 0 or g0 == 0:
        return None
    n = len(g)                                   # f is [f0..fn], g is [g0..g(n-1)]
    A = g0 * g0
    B = g0 * f0
    C = g0 * f[1] - f0 * g[1]
    if C == 0:
        return None                              # the first pass drops a degree
    sq = f0 * f0
    out = []
    for i in range(1, n):
        term = A * f[i + 1]
        if i + 1 < n:
            term -= B * g[i + 1]
        term -= C * g[i]
        if term % sq != 0:
            return None
        out.append(term // sq)
    if not out or out[0] == 0:
        return None                              # the result drops a degree
    return out


def spec_step(f: list[int], g: list[int]) -> list[int] | None:
    """The specification's own step: two cancellation passes, the trailing
    scale, and the exact division, with every trim in place."""
    from model import (cancel_pseudo_leading, exact_divide_polynomial,
                       pseudo_remainder)
    raw = pseudo_remainder(f, g)
    if raw is None:
        return None
    sq = f[0] * f[0]
    divided = exact_divide_polynomial(sq, raw)
    if divided is None:
        return None
    remainder = trim_leading(divided)
    if not remainder or len(remainder) + 1 != len(g):
        return None
    _ = cancel_pseudo_leading                    # imported for the record only
    return remainder


def main() -> int:
    agree = disagree = guarded = 0
    for n in JUDGED:
        p = poly_of(n)
        f, g = trim_leading(p), trim_leading(deriv_hl(p))
        step = 0
        while len(g) >= 2 and len(f) == len(g) + 1:
            fast = fused_step(f, g)
            slow = spec_step(f, g)
            if fast is None:
                guarded += 1
                if slow is None:
                    agree += 1
                else:
                    disagree += 1
                    print(f"  n=2^{n.bit_length() - 1} step {step}: the guard "
                          f"refused a step the specification completed")
                break
            if fast == slow:
                agree += 1
            else:
                disagree += 1
                print(f"  n=2^{n.bit_length() - 1} step {step}: DISAGREE")
                print(f"      fused {str(fast)[:90]}")
                print(f"      spec  {str(slow)[:90]}")
                break
            f, g = g, fast
            step += 1
        # and the whole discriminant, by the fused route, against the spec
        value = fused_resultant(p)
        want = normal_resultant(trim_leading(p), trim_leading(deriv_hl(p)))
        if value != want:
            print(f"  n=2^{n.bit_length() - 1}: fused resultant disagrees")
            return 1
        sign = 1 if (24 * 23 // 2) % 2 == 0 else -1
        if sign * value != disc_spec(n):
            print(f"  n=2^{n.bit_length() - 1}: fused discriminant disagrees")
            return 1
        print(f"  2^{n.bit_length() - 1:<4} {step} fused steps, "
              f"discriminant agrees ({disc_spec(n).bit_length()} bits)")

    print(f"\n  steps agreeing {agree}, disagreeing {disagree}, "
          f"guard refusals {guarded}")

    # the guard must also refuse, rather than answer wrongly, on a polynomial
    # built to drop a degree in the first pass
    bad = [1, 0, 0, 0, 5, 0, 0, 0, 7]
    f2, g2 = trim_leading(bad), trim_leading(deriv_hl(bad))
    if len(f2) == len(g2) + 1:
        fast, slow = fused_step(f2, g2), spec_step(f2, g2)
        ok = (fast is None) or (fast == slow)
        print(f"  constructed abnormal input: "
              f"{'guard refused or agreed' if ok else 'WRONG'}")
        if not ok:
            return 1
    return 0 if disagree == 0 else 1


def fused_resultant(p: list[int]) -> int | None:
    """The whole loop by the fused route, falling back the way the Lean would:
    the specification's own function from the point of refusal."""
    f, g = trim_leading(p), trim_leading(deriv_hl(p))
    if len(f) != len(g) + 1 or not g:
        return None
    while True:
        if len(g) == 1:
            return g[0]
        fast = fused_step(f, g)
        if fast is None:
            return normal_resultant(f, g)
        if len(fast) == 1:
            return fast[0]
        f, g = g, fast


if __name__ == "__main__":
    raise SystemExit(main())
