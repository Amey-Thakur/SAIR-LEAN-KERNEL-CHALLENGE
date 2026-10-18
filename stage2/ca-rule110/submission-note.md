# Submission note — `ca-rule110`

Paste the block below into the **Submission note** field.

```
Approach: the initial row computed on all 256 cells at once, in one natural number.

The previous entry packed the row into a Nat and stepped it eight operations at a time, and its note declined to touch the initial row: "a few hundred kernel steps against the hundreds of thousands the stepping costs". That was wrong, and measuring it is what this entry rests on. The judged cases ask for at most 13 steps, so the stepping is at most 117 operations, while the initial row evaluates a 32-bit mixing hash once per cell, 256 times, for 5,348. The row is 5,348 of 5,465 operations. The stepping was never where the work was.

So only the row changes: every cell gets a 64-bit lane inside one natural number and the whole hash runs on all 256 cells at once, 64 wide operations in place of 5,348 narrow ones. The packed step, the rotations and their correspondence proof are carried over unchanged.

Lanes are a sum, not a bitwise or, and the rest follows from that. The hash multiplies, multiplication distributes over a sum and not over a disjunction, and core Lean has no lemma to convert between them. Paying the no-carry argument once, in Lane.testBit_pack, where the lane bound does the work, buys two lemmas with no side conditions whatever: Lane.pack_mul, a scalar multiplies every lane, and Lane.pack_add, two packings add lane by lane. The seeded ramp seed + (i+1)*0x9e3779b9 across 256 lanes then costs two multiplications and one addition against seed-independent constants instead of 256 of each, and in the gather the halves of every round are joined by pack_add and raised by pack_mul, so no carry argument appears in the tree at all.

Masking before the multiply, not after. The specification masks to 32 bits after each multiply; a packed lane cannot, because shifting the packed number right drags the low bits of lane i+1 into the top of lane i and the multiply would then carry them across the boundary. They agree because (a % 2^m * c) % 2^m = (a * c) % 2^m, proved as Lane.mul_mod_pow, and the mask after the shift is a no-op on a lane narrow enough, proved as Lane.shiftRight_mod_eq. Masking first also caps the widest intermediate at 32 + 31 = 63 bits rather than 41 + 32 = 73, which is why a lane here is 64 bits and not the 128 the specification's own order would force, halving every operand.

The gather. Bit 31 of each of 256 lanes leaves the bits 64 places apart, and no single shift closes that up. Merging in pairs does, and each round is one mask, one shift, one mask, one multiply and one addition; eight rounds bring all 256 cells together. The payload at round r is itself a width-one packing, which makes the tree an induction over one lemma rather than eight separate bit arguments, and a packing of a single lane is that lane, so the eighth round is the answer rather than a step towards it.

Correctness. Lane.testBit_pack is the lemma everything rests on: a bit inside lane i of the packed number is that bit of lane i's value. Lane.eq_of_lanes turns a shifted-and-masked value back into a packing, so pack_mul applies to it. Lane.mixLane_eq proves the lane-local hash equals the specification's caMix32 for every input below 2^48, which covers all 256 lanes, a lane holding seed + (i+1)*0x9e3779b9 with seed below 2^32. Lane.encodeRow_map_range identifies the specification's own encodeRow of a List.range map as a width-one packing, the same object the gather produces, so the two meet inside the lane algebra rather than by reasoning about lists. Row.packedRow_eq assembles these into the row being encodeRow (initRowFor seed) for every seed below 2^32, and caSeed_lt supplies that bound from the specification's own masking.

impl_correct is proved for every n, including zero steps and counts beyond the judged range. Core Lean only, with no Mathlib dependency, so every lemma is about the exact function the kernel reduces. #print axioms Submission.impl_correct reports propext, Classical.choice and Quot.sound, all permitted.

No precomputed answers. There is no table of rows, no hardcoded answer and no branch carrying one. The wide constants are the all-ones lane pattern, the lane-index ramp, the 32-bit field mask and the eight gather masks; none depends on the seed or the step count, each is related to its packed form by rfl, and every cell of every row is computed at reduction time from the specification's own seed.

Acknowledgements and references. No Contributor Network item and no external source was used. Carrying several values in the fields of one wide word, usually called SIMD within a register, is a known idiom and is not claimed as new, nor is the pairwise merge that gathers scattered bits. Specific to this entry are the additive packing, so that the hash's multiplications and the gather's joins need no carry reasoning; the observation that masking before the multiply rather than after both preserves the answer and halves the lane width; and the correspondence proof against this locked specification.
```

## The other fields

| Field | Value |
|---|---|
| Problem | **ca-rule110** |
| Submission source | **Upload Submission.lean** |
| File | `stage2/ca-rule110/Submission.lean` |
| Reference | leave empty; nothing from the Contributor Network was used |

## Measured before submitting

`.github/workflows/ca.yml`, challenge pinned at
`940f0a2ead23ef70ab1387edabb347e629111edd`. The previous entry and this one
are built and timed on the same runner, back to back, on all 24 judged cases
in a single process so that Lean start-up is paid once rather than 24 times.

| | previous entry | this entry |
| :--- | ---: | ---: |
| 24 judged cases, one process | 2.50 s | **0.28 s** |
| cases reduced to the specification's value | 24 of 24 | **24 of 24** |
| axioms | permitted | **permitted** |

Lean start-up is about 0.24 s of each figure, measured directly by a file that
imports `Spec` and asserts nothing. Subtracting it leaves 2.26 s against
0.04 s. The lower figure is close enough to the floor that the ratio is better
read as a lower bound: what the measurement establishes is that the previous
entry's judged work has essentially gone, not its exact multiple.

The initial row alone, eight seeds, timed the same way:

| | start-up only | specification route | packed |
| :--- | ---: | ---: | ---: |
| eight seeds, one process | 0.24 s | 0.90 s | **0.16 s** |

## What the measurement corrected, twice

**The previous entry's own note had the cost backwards.** It declined to touch
the initial row on the grounds that the stepping dominated. `stepmodel.py`
counts it the other way round: at most 13 steps is at most 117 operations, and
the row is 5,348. A claim about where the work goes is worth measuring even
when it is your own.

**The operation count then overstated the gain.** 5,348 narrow operations
against 64 wide ones is a factor of 84, and the row-only measurement is 5.6.
The operands are the reason: a packed value is 16,384 bits where the
specification's are 32 to 64, and the kernel is not indifferent to width. The
row-only figure is also floor-limited, which the full-case measurement shows:
there the packed side falls to within 0.04 s of bare start-up.

## Checked before any Lean was written

`lanes.py` settles the algorithm against the specification at lane width 128,
and `gentime.py --check` re-checks it at width 64, which is the width the
mask-before-multiply order permits: **2,008 seeds, no mismatches**, including
the four judged seeds and every edge case the two fixed cells create.

`LaneProbe.lean` carries the whole lane development and compiles on its own in
CI, so a wrong lemma name is reported by itself and the live entry is never at
risk while the proof is being built. It keeps a `#check` for every core name
the proof was unsure of; one CI round then prints the real statement, which is
much cheaper than guessing. It also checks, by `rfl`, that the kernel can
verify a mask literal against its packed form at both sizes the design needs,
which is what licenses writing the masks as literals rather than building them
at reduction time.

## What this does not do

It does not approach a podium. Rank 3 on this problem is about 3.3 million
against the previous entry's 2,155,396,166, a factor of 652, and removing
essentially all of the judged work is still short of that by one to two orders
of magnitude. The remaining distance is not in the row and not in the
stepping; it is in the step count, which this entry iterates one row at a time
exactly as the specification does.

Three cheap improvements were identified and deliberately left out, because
each is worth a few operations out of 64 and the measurement no longer
resolves them:

* the final exclusive or of the hash cannot change bit 31, since it xors in
  bit 47 of a value below `2 ^ 32`, so the whole third stage could go;
* the mask between the shift and the exclusive or is redundant, because the
  mask after the exclusive or already discards the neighbour's bits;
* each gather round could use a disjunction and a pre-shifted mask instead of
  a multiply and an addition, which is four operations a round instead of five.
