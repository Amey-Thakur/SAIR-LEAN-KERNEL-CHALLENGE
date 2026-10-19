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


def bound_track(n: int) -> tuple[int, int, int]:
    """How wide a slot a packed loop would have to reserve.

    A Kronecker-packed subresultant loop can do its arithmetic with no bounds
    at all, because evaluation at a base is a ring homomorphism. What needs a
    bound is recovering the leading coefficient and the degree from the packed
    integer, which is only possible when every coefficient is smaller than half
    the base. The question is whether a bound propagated from the data, rather
    than proved by a Hadamard-style argument, stays tight enough to fix one
    base for the whole run:

        M' = (|A| + |B| + |C|) * max(Mf, Mg) / f0^2

    which is six `Nat` operations per step, not per coefficient, and uses the
    leading coefficients actually in hand. Returns the true final coefficient
    width, the propagated bound's width, and the slack between them, in bits.
    """
    p = poly_of(n)
    f, g = trim_leading(p), trim_leading(deriv_hl(p))
    # the input bounds are provable from the specification's own construction:
    # |a_i| <= 2^(k-1), and the derivative multiplies by at most the degree
    from model import kbits_of
    k = kbits_of(n)
    mf = 2 ** (k - 1)
    mg = 24 * mf
    true_max = max(max(abs(x) for x in f), max(abs(x) for x in g))
    while len(g) >= 2 and len(f) == len(g) + 1:
        f0, g0 = f[0], g[0]
        A = g0 * g0
        B = g0 * f0
        C = g0 * f[1] - f0 * g[1]
        r = fused_step(f, g)
        if r is None:
            break
        # the bound, rounded up, and never below one
        sq = f0 * f0
        mr = ((abs(A) + abs(B) + abs(C)) * max(mf, mg) + sq - 1) // sq
        worst = max(abs(x) for x in r)
        assert worst <= mr, f"the propagated bound is not a bound at n={n}"
        true_max = max(true_max, worst)
        f, g, mf, mg = g, r, mg, mr
    return (true_max.bit_length(), mg.bit_length(),
            mg.bit_length() - true_max.bit_length())


def packed_run(n: int) -> tuple[int | None, int, int]:
    """The subresultant loop done on packed integers, end to end.

    This is the design the measurements point at: the coefficient list is
    carried as `P(B)` for a power-of-two base `B`, the whole step is

        R = (A * F - B' * G * B - C * G) / f0^2

    three multiplications, two differences and one division on ONE integer
    instead of seven operations per coefficient, and the leading and second
    coefficients are recovered by division when the bound permits it.

    The base cannot be fixed before the run: an a priori bound on the final
    coefficient needs a Hadamard-style argument, and propagating one from the
    input alone compounds doubly exponentially. It can be fixed ADAPTIVELY,
    starting from the input bound and doubling whenever the propagated bound
    outgrows half the base, which costs one unpack and one repack when it
    happens. This returns the resultant, the number of rebasings, and the
    final slot width, so the cost of that can be counted rather than guessed.
    """
    from model import kbits_of

    def pack(coeffs: list[int], slot: int) -> int:
        acc = 0
        for c in coeffs:                      # high to low, Horner
            acc = (acc << slot) + c
        return acc

    def unpack(x: int, length: int, slot: int) -> list[int]:
        half = 1 << (slot - 1)
        out = []
        for _ in range(length):               # balanced digits, low to high
            d = x % (1 << slot)
            if d >= half:
                d -= 1 << slot
            out.append(d)
            x = (x - d) >> slot
        return out[::-1]

    p = poly_of(n)
    f, g = trim_leading(p), trim_leading(deriv_hl(p))
    k = kbits_of(n)
    mf, mg = 2 ** (k - 1), 24 * 2 ** (k - 1)
    slot = 2 * mg.bit_length() + 2
    rebase = 0
    fl, gl = len(f), len(g)
    F, G = pack(f, slot), pack(g, slot)
    while True:
        if gl == 1:
            return unpack(G, 1, slot)[0], rebase, slot
        if gl < 1 or fl != gl + 1:
            return None, rebase, slot
        # the two leading coefficients of each side, which is what the bound
        # buys: one division and one remainder apiece in a real implementation
        f0, f1 = unpack(F, fl, slot)[:2]
        g0, g1 = unpack(G, gl, slot)[:2]
        if f0 == 0 or g0 == 0:
            return None, rebase, slot
        A, Bp, C = g0 * g0, g0 * f0, g0 * f1 - f0 * g1
        if C == 0:
            return None, rebase, slot
        sq = f0 * f0
        # The step, on one integer. The alignment is the whole trick: the `A`
        # term takes f without its leading coefficient, the `B'` term takes g
        # without its leading coefficient shifted up one slot, and the `C`
        # term takes g ENTIRE -- that last one is what makes the top slot
        # vanish, since A*f1 - B'*g1 - C*g0 is identically zero. Taking g's
        # tail there instead leaves g0*C behind in the top slot, which is the
        # mistake this file was written to catch.
        ftail = F - (f0 << (slot * (fl - 1)))
        gtail = G - (g0 << (slot * (gl - 1)))
        num = A * ftail - Bp * (gtail << slot) - C * G
        if num % sq != 0:
            return None, rebase, slot
        R, rl = num // sq, gl - 1
        mr = ((abs(A) + abs(Bp) + abs(C)) * max(mf, mg) + sq - 1) // sq
        F, G, fl, gl, mf, mg = G, R, gl, rl, mg, mr
        # and rebase both sides when the bound has outgrown half a slot
        if mg.bit_length() + 2 > slot:
            fc, gc = unpack(F, fl, slot), unpack(G, gl, slot)
            slot = 2 * mg.bit_length() + 2
            F, G = pack(fc, slot), pack(gc, slot)
            rebase += 1


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

    print()
    print("  the same loop done on packed integers, end to end")
    print(f"      {'case':>8} {'resultant':>12} {'rebasings':>10} "
          f"{'final slot':>11}")
    for n in JUDGED:
        value, rebase, slot = packed_run(n)
        want = normal_resultant(trim_leading(poly_of(n)),
                                trim_leading(deriv_hl(poly_of(n))))
        verdict = "agrees" if value == want else f"WRONG {str(value)[:20]}"
        print(f"      2^{n.bit_length() - 1:<6} {verdict:>12} {rebase:>10} "
              f"{slot:>11,}")
        if value != want:
            return 1

    print()
    print("  how wide a slot a packed loop must reserve, if the bound is "
          "propagated from the data")
    print(f"      {'case':>8} {'true bits':>11} {'bound bits':>11} "
          f"{'slack':>8} {'factor':>8}")
    for n in JUDGED:
        true_bits, bound_bits, slack = bound_track(n)
        print(f"      2^{n.bit_length() - 1:<6} {true_bits:>11,} "
              f"{bound_bits:>11,} {slack:>8,} "
              f"{bound_bits / max(1, true_bits):>8.2f}")

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
