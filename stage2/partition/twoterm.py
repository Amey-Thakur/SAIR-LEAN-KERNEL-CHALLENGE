#!/usr/bin/env python3
# ==============================================================================
# File: twoterm.py
# Description: Settles the two-term design in Python before any Lean is written:
#   checks it against the specification's own recurrence, and counts the
#   operations it performs so the design can be costed against the leaderboard.
#
#   Why a two-term design at all. The specification computes
#
#       partAux (k+1) m = sum over j of partAux k (m - j*(k+1))
#
#   which is 3,577 additions at n = 36. The same table satisfies a two-term
#   identity, which the packed submission already PROVES and then uses only as a
#   bound rather than as the algorithm:
#
#       partAux (k+1) m = partAux k m + partAux (k+1) (m - (k+1))
#
#   That is 666 additions at n = 36 and 2,074 across the six judged sizes. Rank 1
#   is at 1,429,499 units of computation, and 1,429,499 / 2,074 = 689 units per
#   operation, which is about what one kernel addition on a single-word number
#   costs. So the leaders are almost certainly computing this identity on small
#   numbers, and their bookkeeping is negligible beside the additions.
#
#   Why small numbers rather than a packed row. The ranked metric charges by
#   operand size (see MODELS.md for the calibration). The packed row is 43
#   machine words wide at n = 36, so even the two-term identity computed on
#   packed rows is 2,074 operations at about 25 words average, which prices at
#   roughly 35,000,000 -- worse than the 132,036,341 entry only by luck of
#   rounding, and nowhere near the plateau. The same 2,074 operations on
#   single-word values price at about 1,430,000. The design has to keep every
#   value a single partition count.
#
#   The formulation, which is simpler than it first looks. Writing one pass as
#
#       out[m] = in[m] + out[m - d]
#
#   seems to need random access d positions back into the output, which on a list
#   means either an index walk or a queue. It needs neither. Cut the row into
#   consecutive blocks of d. Position m sits at offset r in block i, and m - d
#   sits at the SAME offset r in block i-1. So
#
#       out_block_0 = in_block_0
#       out_block_i = in_block_i + out_block_{i-1}     elementwise
#
#   which is a fold over blocks carrying the previous output block, with no
#   indexing at all. Every element is touched a constant number of times.
#
# Usage: py stage2/partition/twoterm.py
# Author: Amey Thakur
# License: CC BY 4.0
# ==============================================================================

from __future__ import annotations

from functools import lru_cache

ENDPOINTS = [14, 18, 22, 26, 32, 36]


# ------------------------------------------------- the specification ---------
@lru_cache(None)
def part_aux(k: int, m: int) -> int:
    """The specification's recurrence, verbatim."""
    if k == 0:
        return 1 if m == 0 else 0
    return sum(part_aux(k - 1, m - j * k) for j in range(m // k + 1))


def spec(n: int) -> int:
    return part_aux(n, n)


# --------------------------------------------------- the candidate -----------
class Count:
    """Operations charged the way the judge appears to charge them.

    `adds` is the arithmetic. `cells` is every other constructor step: one for
    each cons cell built or matched by chunking, zipping or joining. Both are
    counted because the leaders' figure implies their bookkeeping is small
    beside their additions, and whether ours is small is the whole question.
    """

    def __init__(self) -> None:
        self.adds = 0
        self.cells = 0

    def total(self) -> int:
        return self.adds + self.cells


def chunk(d: int, xs: list[int], c: Count) -> list[list[int]]:
    """Cut into consecutive blocks of d. The last block may be shorter.

    Charged the way Lean pays for it rather than the way Python does. The Lean
    definition cuts each block with `take d` and then advances with `drop d`, and
    each of those walks the block, so a block of length L costs 2L rather than L.
    An earlier version of this file charged L, understating the whole design by
    about a third, and the figure that came out of it was quoted before it was
    checked.
    """
    out: list[list[int]] = []
    i = 0
    while i < len(xs):
        block = xs[i:i + d]
        c.cells += 2 * len(block)      # take d, then drop d
        out.append(block)
        i += d
    return out


def zip_add(xs: list[int], ys: list[int], c: Count) -> list[int]:
    """Elementwise sum; where ys runs out, xs passes through unchanged.

    The short-ys case is what makes block 0 work without a special case: its
    previous block is empty, so it passes straight through.
    """
    out = []
    for i, x in enumerate(xs):
        if i < len(ys):
            out.append(x + ys[i])
            c.adds += 1
        else:
            out.append(x)
        c.cells += 1
    return out


def one_pass(d: int, row: list[int], c: Count) -> list[int]:
    """One pass of the two-term recurrence: out[m] = row[m] + out[m-d]."""
    prev: list[int] = []
    blocks = []
    for block in chunk(d, row, c):
        prev = zip_add(block, prev, c)
        blocks.append(prev)
    joined: list[int] = []
    for b in blocks:
        joined.extend(b)
        c.cells += len(b)
    return joined


def impl(n: int, c: Count) -> int:
    """Row 0 is 1 at m = 0 and 0 elsewhere; then one pass per part size."""
    row = [1] + [0] * n
    c.cells += n + 1
    for d in range(1, n + 1):
        row = one_pass(d, row, c)
    return row[n]


# ---------------------------------------------------- the sum form -----------
def sum_form_adds(n: int) -> int:
    """Additions the specification's sum form performs, for comparison."""
    total = 0
    for d in range(1, n + 1):
        for m in range(n + 1):
            total += m // d          # one addition per extra term
    return total


def two_term_adds(n: int) -> int:
    """Additions the two-term identity performs: n - d + 1 per pass."""
    return sum(max(0, n - d + 1) for d in range(1, n + 1))


def main() -> int:
    # Correctness first, and at every size rather than only the judged ones: a
    # design that agrees at the six endpoints and disagrees at n = 7 is worse
    # than useless, because the judge would accept it and the proof would not.
    bad = []
    for n in range(0, 41):
        c = Count()
        got = impl(n, c)
        want = spec(n)
        if got != want:
            bad.append((n, got, want))
    if bad:
        print("  DISAGREES with the specification:")
        for n, got, want in bad[:10]:
            print(f"    n={n}  got {got}  want {want}")
        return 1
    print("  agrees with the specification at every n from 0 to 40")

    print(f"\n  additions, by formulation")
    print(f"{'n':>6}{'sum form':>12}{'two-term':>12}{'saving':>9}")
    print("  " + "-" * 37)
    ts = tt = 0
    for n in ENDPOINTS:
        s, t = sum_form_adds(n), two_term_adds(n)
        ts += s
        tt += t
        print(f"{n:>6}{s:>12,}{t:>12,}{s / t:>8.1f}x")
    print("  " + "-" * 37)
    print(f"{'tot':>6}{ts:>12,}{tt:>12,}{ts / tt:>8.1f}x")

    print(f"\n  operations actually performed, and what they price at")
    print(f"  at 689 units each, the rate rank 1's figure implies")
    print(f"{'n':>6}{'adds':>10}{'cells':>10}{'total':>10}{'priced':>14}")
    print("  " + "-" * 50)
    grand = 0
    for n in ENDPOINTS:
        c = Count()
        impl(n, c)
        grand += c.total()
        print(f"{n:>6}{c.adds:>10,}{c.cells:>10,}{c.total():>10,}"
              f"{c.total() * 689:>14,}")
    print("  " + "-" * 50)
    print(f"{'tot':>6}{'':>10}{'':>10}{grand:>10,}{grand * 689:>14,}")

    print(f"\n  where that would stand")
    board = [("rank 1", 1_429_499), ("rank 7", 1_877_306),
             ("rank 8", 7_621_271), ("rank 13", 51_260_077),
             ("ours now, rank 14", 132_036_341)]
    priced = grand * 689
    for name, v in board:
        rel = priced / v
        print(f"    {name:<20}{v:>14,}   ours would be {rel:>6.2f}x that")

    print(f"\n  the bookkeeping question: additions are {tt:,} of {grand:,} "
          f"operations,")
    print(f"  so overhead is {(grand - tt) / tt:.1f}x the arithmetic. The "
          f"leaders' figure")
    print(f"  implies theirs is close to zero, so this is where the remaining")
    print(f"  distance to the plateau sits.")

    # The 689-unit rate used above rests on one assumption about the leaders:
    # that they perform 2,074 operations and nothing else material. If their
    # bookkeeping is anything like ours, the true rate is far lower and every
    # absolute figure here moves with it. A RATIO against a design whose score
    # we are about to learn does not move, which is why it is printed too.
    #
    # Submission 713 is the sum-over-multiplicities list design, which bitcost.py
    # counts at 137,678 elementary steps in this same convention: one unit per
    # cons cell walked or built, one per addition. When 713 is scored, dividing
    # its figure by this ratio predicts the two-term design directly, with no
    # assumption about the leaders at all.
    LIST_SUM_FORM_STEPS = 137_678
    ratio = LIST_SUM_FORM_STEPS / grand
    print()
    print(f"  calibration that needs no assumption about the leaders")
    print(f"    sum-form list design (submission 713) {LIST_SUM_FORM_STEPS:>10,} steps")
    print(f"    two-term design (this file)           {grand:>10,} steps")
    print(f"    two-term should score 1/{ratio:.1f} of whatever 713 scores")
    for label, guess in (("if 713 scores  95,000,000", 95_000_000),
                         ("if 713 scores 132,000,000", 132_000_000)):
        print(f"      {label}  ->  about {guess / ratio:>12,.0f}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
