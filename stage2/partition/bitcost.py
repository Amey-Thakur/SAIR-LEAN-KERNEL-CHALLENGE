#!/usr/bin/env python3
# ==============================================================================
# File: bitcost.py
# Description: Costs the partition designs in WORD operations rather than in
#   Nat operations, which is the difference between the model this repository
#   has been using and the metric the judge actually applies.
#
#   The occasion for writing it: the live leaderboard puts our packed entry at
#   132,036,341 units of work against a leader at 1,429,499, a factor of 92.
#   The step model said the packed row does 2,801 operations against the list
#   row's 182,642, a factor of 65 the other way. Both cannot be right about
#   what matters, and the judge is the one that counts.
#
#   The suspicion this tests: packing made every operation act on a 2,701-bit
#   number. A 64-bit machine word holds 64 of those bits, so one packed
#   operation is roughly 43 word operations, and some of them are worse than
#   linear. Counting Nat operations hides that completely, which is the exact
#   blind spot Section 6.3 of the paper describes for field width, one scale up.
#
# Usage: py stage2/partition/bitcost.py
# Author: Amey Thakur
# License: CC BY 4.0
# ==============================================================================

from __future__ import annotations

from functools import lru_cache

W = 64  # bits per machine word


def words(bits: int) -> int:
    return max(1, (bits + W - 1) // W)


@lru_cache(None)
def partAux(k: int, m: int) -> int:
    if k == 0:
        return 1 if m == 0 else 0
    return sum(partAux(k - 1, m - j * k) for j in range(m // k + 1))


# ------------------------------------------------- the packed design ---------
def packed_word_ops(n: int, mask_instead_of_mod: bool = False) -> dict:
    """Word operations for the packed row, by kind.

    Shifts and adds on a b-bit operand are linear in its words. The modulus is
    a division by a 2701-bit constant, which is the expensive one: schoolbook
    division is quadratic in the quotient's words, and replacing it with a
    bitwise AND against a precomputed mask makes it linear.
    """
    w = 2 * n + 1
    row_bits = w * (n + 1)
    rw = words(row_bits)

    shift_add = 0
    for d in range(1, n + 1):
        terms = n // d
        # each term: one shift and one add, both on a row-sized operand.
        # the shifted operand grows, so charge the larger of the two
        for j in range(1, terms + 1):
            shifted = words(row_bits + j * d * w)
            shift_add += shifted      # the shift
            shift_add += shifted      # the add
    reduce_cost = 0
    for _ in range(1, n + 1):
        widest = words(row_bits + n * w)     # worst case before reduction
        if mask_instead_of_mod:
            reduce_cost += widest            # one AND, linear
        else:
            # division of a widest-word number by an rw-word constant
            reduce_cost += max(1, (widest - rw + 1)) * rw
    return {"shift_add": shift_add, "reduce": reduce_cost,
            "total": shift_add + reduce_cost, "row_words": rw}


# --------------------------------------------------- the list design ---------
def list_word_ops(n: int) -> dict:
    """Word operations for the row-of-lists design.

    Every entry is a single small number, so every arithmetic operation is one
    word. The cost is constructor matches, which are pointer work rather than
    arithmetic, and are charged here at one unit each.
    """
    length = n + 1
    matches = 0
    adds = 0
    for d in range(1, n + 1):
        for m in range(length):
            q = m // d
            for j in range(q + 1):
                matches += (m - j * d) + 1   # nth walks that many cells
                adds += 1                    # one small addition
    return {"matches": matches, "adds": adds, "total": matches + adds}


def main() -> int:
    ENDPOINTS = [14, 18, 22, 26, 32, 36]
    print(f"{'n':>4}{'packed w/ mod':>16}{'packed w/ mask':>16}"
          f"{'list':>12}{'row words':>11}")
    print("-" * 60)
    tot = {"mod": 0, "mask": 0, "list": 0}
    for n in ENDPOINTS:
        p = packed_word_ops(n)
        pm = packed_word_ops(n, mask_instead_of_mod=True)
        l = list_word_ops(n)
        tot["mod"] += p["total"]; tot["mask"] += pm["total"]; tot["list"] += l["total"]
        print(f"{n:>4}{p['total']:>16,}{pm['total']:>16,}{l['total']:>12,}"
              f"{p['row_words']:>11}")
    print("-" * 60)
    print(f"{'tot':>4}{tot['mod']:>16,}{tot['mask']:>16,}{tot['list']:>12,}")

    print(f"\n  where the packed cost goes, at n = 36:")
    p = packed_word_ops(36)
    print(f"    shifts and adds : {p['shift_add']:>12,} word ops")
    print(f"    the modulus     : {p['reduce']:>12,} word ops"
          f"   ({100 * p['reduce'] / p['total']:.0f}% of the total)")
    pm = packed_word_ops(36, True)
    print(f"    same with a mask: {pm['reduce']:>12,} word ops")
    print(f"    replacing mod by mask would cut the total "
          f"{p['total'] / pm['total']:.1f}x")

    print(f"\n  the two models disagree about which design is cheaper:")
    print(f"    Nat operations  packed 2,801   list 182,642   -> packed wins 65x")
    print(f"    word operations packed {tot['mod']:,}   list {tot['list']:,}"
          f"   -> list wins {tot['mod'] / tot['list']:.0f}x")
    print(f"\n  measured on the live board: ours 132,036,341, leader 1,429,499")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
