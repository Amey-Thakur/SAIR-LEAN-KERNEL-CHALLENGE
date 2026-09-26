#!/usr/bin/env python3
# ==============================================================================
# File: model.py
# Description: Transcribes the locked ca-rule110 specification, and the
#   bit-packed design meant to replace it, and checks they agree.
#
#   Writing the Lean first would mean debugging the algorithm and the proof at
#   the same time, through a CI round trip, with no toolchain on this machine.
#   The algorithm is settled here instead, where a disagreement costs a second.
#   Only the correspondence proof is left for Lean.
#
#   The design. The spec holds the row as a List Bool of length 256 and reads
#   neighbours with getD, which costs a traversal per read: three reads per
#   cell, 256 cells, so a step is quadratic. Packed into the bits of one Nat,
#   cell i is bit i, and the whole row steps at once:
#
#       new = (c | r) & ~(l & c & r)
#
#   where l is the row rotated one place up and r one place down. That is the
#   Rule 110 table, which this file verifies exhaustively rather than asserts.
#
# Usage: py stage2/ca-rule110/model.py
# Author: Amey Thakur
# License: CC BY 4.0
# ==============================================================================

from __future__ import annotations

import json
import pathlib
import random

W = 256
MASK = (1 << W) - 1


# ----------------------------------------------------- the locked spec -------
def rule110(l: bool, c: bool, r: bool) -> bool:
    """Transcribed from Spec.lean: false on three patterns, true otherwise."""
    if (l, c, r) in {(True, True, True), (True, False, False), (False, False, False)}:
        return False
    return True


def step_row(row: list[bool]) -> list[bool]:
    n = len(row)
    return [rule110(row[(i + n - 1) % n], row[i], row[(i + 1) % n])
            for i in range(n)]


def iter_row(t: int, row: list[bool]) -> list[bool]:
    for _ in range(t):
        row = step_row(row)
    return row


def encode_row(row: list[bool]) -> int:
    acc = 0
    for b in reversed(row):
        acc = 2 * acc + (1 if b else 0)
    return acc


def ca_mix32(x: int) -> int:
    x = ((x ^ (x >> 16)) * 0x7FEB352D) & 0xFFFFFFFF
    x = ((x ^ (x >> 15)) * 0x846CA68B) & 0xFFFFFFFF
    return (x ^ (x >> 16)) & 0xFFFFFFFF


def init_row_for(seed: int) -> list[bool]:
    out = []
    for i in range(W):
        if i == 0:
            out.append(True)
        elif i == 1:
            out.append(False)
        else:
            out.append(bool((ca_mix32(seed + (i + 1) * 0x9E3779B9) >> 31) & 1))
    return out


def ca_spec_n(n: int) -> int:
    return encode_row(iter_row(n >> 32, init_row_for(n & 0xFFFFFFFF)))


# ------------------------------------------------- the packed design ---------
def rotl(r: int) -> int:
    """Bit i of the result is bit i-1 of r, cyclically: the left neighbour."""
    return ((r << 1) | (r >> (W - 1))) & MASK


def rotr(r: int) -> int:
    """Bit i of the result is bit i+1 of r, cyclically: the right neighbour."""
    return ((r >> 1) | ((r & 1) << (W - 1))) & MASK


def pstep(r: int) -> int:
    return (r | rotr(r)) & (MASK ^ (rotl(r) & r & rotr(r)))


def piter(t: int, r: int) -> int:
    for _ in range(t):
        r = pstep(r)
    return r


def pinit(seed: int) -> int:
    acc = 0
    for i in range(W - 1, -1, -1):
        if i == 0:
            bit = 1
        elif i == 1:
            bit = 0
        else:
            bit = (ca_mix32(seed + (i + 1) * 0x9E3779B9) >> 31) & 1
        acc = 2 * acc + bit
    return acc


def impl(n: int) -> int:
    return piter(n >> 32, pinit(n & 0xFFFFFFFF))


# --------------------------------------------------------------- checks ------
def main() -> int:
    fails = []

    # 1. the boolean identity, over all eight patterns
    for l in (False, True):
        for c in (False, True):
            for r in (False, True):
                want = rule110(l, c, r)
                got = (c or r) and not (l and c and r)
                if want != got:
                    fails.append(f"rule110({l},{c},{r}): table {want}, formula {got}")
    print(f"  rule110 formula (c|r)&~(l&c&r) checked on all 8 patterns: "
          f"{'ok' if not fails else 'FAILED'}")

    # 2. the packed initial row equals the encoded spec row
    seeds = [0, 1, 2, 0xFFFFFFFF, 0x9E3779B9, 12345] + \
            [random.Random(k).getrandbits(32) for k in range(8)]
    for s in seeds:
        if pinit(s) != encode_row(init_row_for(s)):
            fails.append(f"pinit({s}) != encodeRow(initRowFor({s}))")
    print(f"  pinit matches encodeRow(initRowFor .) on {len(seeds)} seeds: "
          f"{'ok' if not any('pinit' in f for f in fails) else 'FAILED'}")

    # 3. the step correspondence, which is the lemma Lean will have to prove
    rng = random.Random(7)
    bad_step = 0
    for _ in range(300):
        row = [rng.random() < 0.5 for _ in range(W)]
        if encode_row(step_row(row)) != pstep(encode_row(row)):
            bad_step += 1
    if bad_step:
        fails.append(f"step correspondence failed on {bad_step} of 300 rows")
    print(f"  encodeRow(stepRow row) == pstep(encodeRow row) on 300 random "
          f"rows: {'ok' if not bad_step else 'FAILED'}")

    # edge rows: all zero, all one, single bits at the wrap boundary
    edges = [[False] * W, [True] * W,
             [i == 0 for i in range(W)], [i == W - 1 for i in range(W)],
             [i in (0, W - 1) for i in range(W)]]
    bad_edge = [i for i, row in enumerate(edges)
                if encode_row(step_row(row)) != pstep(encode_row(row))]
    if bad_edge:
        fails.append(f"step correspondence failed on edge rows {bad_edge}")
    print(f"  the same on {len(edges)} edge rows including both wrap cases: "
          f"{'ok' if not bad_edge else 'FAILED'}")

    # 4. end to end against the spec, at and beyond the judged step counts
    cases = []
    for steps in (0, 1, 2, 4, 8, 13):
        for seed in (0, 1, 0xDEADBEEF, 0x9E3779B9):
            n = (steps << 32) | seed
            want, got = ca_spec_n(n), impl(n)
            cases.append({"n": n, "steps": steps, "seed": seed, "value": want})
            if want != got:
                fails.append(f"impl != spec at steps={steps} seed={seed:#x}")
    print(f"  impl == caSpecN on {len(cases)} cases "
          f"(steps 0,1,2,4,8,13; the judged maximum is 8): "
          f"{'ok' if not any('impl !=' in f for f in fails) else 'FAILED'}")

    # 5. what the design is worth, in operations rather than in claims
    spec_ops = 8 * W * 3 * (W // 2)          # 3 getD reads per cell per step
    packed_ops = 8 * 8                        # 8 bitwise ops per step
    print(f"\n  at the judged maximum of 8 steps on a {W}-cell row:")
    print(f"    spec, list reads          ~{spec_ops:,}")
    print(f"    packed, Nat operations     {packed_ops}")
    print(f"    ratio                      ~{spec_ops // packed_ops:,}x")

    out = pathlib.Path(__file__).with_name("cases.json")
    out.write_text(json.dumps({"width": W, "cases": cases}, indent=2) + "\n",
                   encoding="utf-8")
    print(f"\n  {len(cases)} expected values written to {out.name}")

    for f in fails:
        print(f"  FAIL  {f}")
    print(f"\n{'all checks passed' if not fails else str(len(fails)) + ' FAILURES'}")
    return 1 if fails else 0


if __name__ == "__main__":
    raise SystemExit(main())
