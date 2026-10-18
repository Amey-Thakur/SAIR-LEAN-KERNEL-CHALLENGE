#!/usr/bin/env python3
# ==============================================================================
# File: model.py
# Description: Transcribes the sha256 specification, then a candidate that
#   computes the same digest with fewer kernel operations, and checks the two
#   agree before any Lean is written.
#
#   Why. The previous entry replaced the list-based message schedule with a
#   16-field structure and measured 11%, and its own note drew the right
#   conclusion: the cost of this problem is the round function's masked 32-bit
#   arithmetic, not the plumbing around it. This file attacks the arithmetic.
#
#   Three changes, each of which the specification licenses rather than
#   approximates:
#
#   1. Defer the mask across a chain of additions. `add32` masks after every
#      single addition, but masking is reduction modulo 2^32 and addition
#      commutes with it, so a sum of five terms needs ONE mask, not five.
#      The same argument says a term entering such a sum need not be masked at
#      all, because any bits it carries at or above 2^32 are discarded by the
#      final mask. That removes the mask from every sigma.
#
#   2. Rotate with one multiply instead of two shifts and an or. For x < 2^32,
#      `x * (2^32 + 1)` is `x` placed twice, side by side, so every rotation of
#      x is a single shift of that doubled word. Masking distributes over
#      exclusive or, so the three rotations of a sigma share one mask at the
#      end instead of carrying one each.
#
#   3. Fold the padding. Every chained step hashes a 32-byte message, so the
#      padded block's words 8 to 15 are the constants
#      [0x80000000, 0, 0, 0, 0, 0, 0, 256] on every one of the 512 steps. The
#      schedule's early expansion steps therefore add terms that are zero, and
#      sigma1 of a zero word is zero.
#
#   The operation counts here are a model and nothing more. On this repository
#   an operation count has twice overstated a measured gain, most recently by a
#   factor of 15 on ca-rule110, so the figure that decides anything is the
#   wall clock in CI.
#
# Usage: py stage2/sha256/model.py
# Author: Amey Thakur
# License: CC BY 4.0
# ==============================================================================

from __future__ import annotations

M32 = 0xFFFFFFFF
DOUBLE = (1 << 32) | 1

K = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1,
    0x923f82a4, 0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
    0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786,
    0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147,
    0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
    0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
    0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a,
    0x5b9cca4f, 0x682e6ff3, 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
    0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
]

IV = [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
      0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

PAD = [0x80000000, 0, 0, 0, 0, 0, 0, 256]


class Ops:
    """Counts Nat primitives, so the change is quantified and not asserted."""

    def __init__(self) -> None:
        self.n = 0

    def __call__(self, k: int = 1) -> None:
        self.n += k


# ------------------------------------------------- the locked specification --
def s_add32(a, b, op):
    op(2)                      # one add, one mask
    return (a + b) & M32


def s_rotr32(x, n, op):
    op(4)                      # two shifts, one or, one mask
    return ((x >> n) | (x << (32 - n))) & M32


def s_small0(x, op):
    op(2)                      # one shift, two xors less the shared one
    return s_rotr32(x, 7, op) ^ s_rotr32(x, 18, op) ^ (x >> 3)


def s_small1(x, op):
    op(2)
    return s_rotr32(x, 17, op) ^ s_rotr32(x, 19, op) ^ (x >> 10)


def s_big0(x, op):
    op(2)
    return s_rotr32(x, 2, op) ^ s_rotr32(x, 13, op) ^ s_rotr32(x, 22, op)


def s_big1(x, op):
    op(2)
    return s_rotr32(x, 6, op) ^ s_rotr32(x, 11, op) ^ s_rotr32(x, 25, op)


def s_ch(x, y, z, op):
    op(4)
    return (x & y) ^ ((x ^ M32) & z)


def s_maj(x, y, z, op):
    op(5)
    return (x & y) ^ (x & z) ^ (y & z)


def s_schedule(block, op):
    w = list(block)
    for i in range(16, 64):
        nxt = s_add32(s_add32(s_small1(w[i - 2], op), w[i - 7], op),
                      s_add32(s_small0(w[i - 15], op), w[i - 16], op), op)
        w.append(nxt)
    return w


def s_compress(state, block, op):
    w = s_schedule(block, op)
    a, b, c, d, e, f, g, h = state
    for i in range(64):
        t1 = s_add32(h, s_add32(s_big1(e, op),
                                s_add32(s_ch(e, f, g, op),
                                        s_add32(K[i], w[i], op), op), op), op)
        t2 = s_add32(s_big0(a, op), s_maj(a, b, c, op), op)
        h, g, f, e = g, f, e, s_add32(d, t1, op)
        d, c, b, a = c, b, a, s_add32(t1, t2, op)
    return [s_add32(x, y, op) for x, y in zip(state, [a, b, c, d, e, f, g, h])]


def s_step(digest, op):
    return s_compress(IV, list(digest) + PAD, op)


# -------------------------------------------------------- the candidate ------
def c_double(x, op):
    """x placed twice side by side, in one multiplication."""
    op(1)
    return x * DOUBLE


def c_big0(x, op):
    """Three rotations and one mask, sharing one doubled word."""
    xx = c_double(x, op)
    op(6)                      # three shifts, two xors, one mask
    return ((xx >> 2) ^ (xx >> 13) ^ (xx >> 22)) & M32


def c_big1(x, op):
    xx = c_double(x, op)
    op(6)
    return ((xx >> 6) ^ (xx >> 11) ^ (xx >> 25)) & M32


def c_small0(x, op):
    """`x >> 3` is already below 2^32, so it joins the xor unmasked."""
    xx = c_double(x, op)
    op(6)
    return ((xx >> 7) ^ (xx >> 18) ^ (x >> 3)) & M32


def c_small1(x, op):
    xx = c_double(x, op)
    op(6)
    return ((xx >> 17) ^ (xx >> 19) ^ (x >> 10)) & M32


def c_schedule(w0, op):
    """The 48 expansion steps, with the padding's zeros folded away.

    Words 8 to 15 are the same constants on every chained step, so terms that
    read them are known now: `w[i-7]` and `w[i-16]` vanish where they are zero,
    and `sigma1 0` is 0.
    """
    w = list(w0)
    for i in range(16, 64):
        terms = []
        s1_src, add_src = w[i - 2], w[i - 7]
        if not (i - 2 < 16 and w0[i - 2] == 0):
            terms.append(c_small1(s1_src, op))
        if not (i - 7 < 16 and w0[i - 7] == 0):
            terms.append(add_src)
        if not (i - 15 < 16 and w0[i - 15] == 0):
            terms.append(c_small0(w[i - 15], op))
        if not (i - 16 < 16 and w0[i - 16] == 0):
            terms.append(w[i - 16])
        # one mask for the whole sum, however many terms it has
        op(max(0, len(terms) - 1) + 1)
        total = 0
        for t in terms:
            total += t
        w.append(total & M32)
    return w


def c_compress(state, block, op):
    w = c_schedule(block, op)
    a, b, c, d, e, f, g, h = state
    for i in range(64):
        # five terms, four additions, ONE mask; big1 arrives unmasked and the
        # bits it carries above 2^32 are discarded by that one mask
        op(5)
        t1 = (h + c_big1(e, op) + s_ch(e, f, g, op) + K[i] + w[i]) & M32
        op(2)
        t2 = (c_big0(a, op) + s_maj(a, b, c, op)) & M32
        op(2)
        h, g, f, e = g, f, e, (d + t1) & M32
        op(2)
        d, c, b, a = c, b, a, (t1 + t2) & M32
    out = []
    for x, y in zip(state, [a, b, c, d, e, f, g, h]):
        op(2)
        out.append((x + y) & M32)
    return out


def c_step(digest, op):
    return c_compress(IV, list(digest) + PAD, op)


# ----------------------------------------------------------- the seed --------
def seed_step32(x):
    return (1664525 * x + 1013904223) & M32


def seed_digest(seed):
    out, x = [], seed & M32
    for _ in range(8):
        x = seed_step32(x)
        out.append(x)
    return out


def encode(digest):
    out = 0
    for word in digest:
        out = (out << 32) | word
    return out


def main() -> None:
    import hashlib

    # agreement, and against an independent implementation of SHA-256 too
    bad = 0
    for seed in [0, 1, 2, 0xDEADBEEF, 0x9E3779B9, M32, 123456789]:
        d = seed_digest(seed)
        spec, cand = list(d), list(d)
        for _ in range(4):
            spec = s_step(spec, Ops())
            cand = c_step(cand, Ops())
            # hashlib hashes the same 32 bytes, which is the whole point of
            # checking: it shares no code with either transcription
            raw = b"".join(x.to_bytes(4, "big") for x in d)
            if _ == 0:
                ref = list(int.from_bytes(hashlib.sha256(raw).digest()[i:i + 4],
                                          "big") for i in range(0, 32, 4))
                if ref != spec:
                    print(f"  SPEC DISAGREES WITH hashlib at seed {seed}")
                    bad += 1
        if spec != cand:
            print(f"  MISMATCH at seed {seed}")
            bad += 1
    print(f"checked 7 seeds x 4 chained steps, {bad} mismatches")

    # where the operations go, per chained step
    d = seed_digest(0xDEADBEEF)
    so, co = Ops(), Ops()
    s_step(d, so)
    c_step(d, co)
    print()
    print(f"  specification route   {so.n:>8,} operations per step")
    print(f"  candidate route       {co.n:>8,} operations per step")
    print(f"  ratio                 {so.n / co.n:>8.2f}x")
    print()
    for steps in (4, 32, 512):
        print(f"  at {steps:>3} chain steps: {so.n * steps:>11,}"
              f" -> {co.n * steps:>11,}")
    print()
    print("  An operation count is a model. On this repository it has twice")
    print("  overstated a measured gain. CI decides.")
    if bad:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
