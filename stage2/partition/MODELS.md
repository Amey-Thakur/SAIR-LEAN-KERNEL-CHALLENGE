# Three cost models, two instruments, and which one the judge uses

This file exists because the `partition` entry was reasoned about with three
different cost models in one day, each of which contradicted the others, and two
of them produced a submission. The record is kept so the next attempt starts from
what was measured rather than from whichever model was most recently believed.

## The measurements, first

Every number below was measured, in CI, in one job where a comparison is made.

| instrument | what it says |
| --- | --- |
| wall clock, six judged sizes | packed 0.07 s, list 3.63 s -- **packed wins 52x** |
| `primitives.py`, one operation | every primitive flat from 2,701 to 43,216 bits |
| `widthcost.py`, 20,000 steps, width varied | 20,301 bits costs **1.1x** what 1 bit costs |
| `widthcost.py`, width fixed, steps varied | 2x steps -> 2.1x, 4x -> 4.6x, 8x -> 10.0x |
| `timealt.py`, sweep with `R` used once | **0.6x** -- the variant is slower |
| the board, our entry | `computationTotal` 132,036,341 |
| the board, rank 1 | `computationTotal` 1,429,499 |

## The two budgets on the board, only one of which is ranked

The leaderboard row carries `rankingContract: computation-total-v1` and two
separate figures:

| | ours | rank 1 | rank 2 |
| --- | ---: | ---: | ---: |
| `computationTotal` (ranked) | 132,036,341 | 1,429,499 | 1,438,118 |
| `correctnessWork` (**not** ranked) | 3,449,915,665 | 13,626,223,161 | 39,397,845,014 |

**Proof cost is not ranked.** Rank 2 spends 39.4 billion units checking its proof
to reach a ranked 1,438,118. Ours spends 3.4 billion, a quarter of rank 1's and a
eleventh of rank 2's. Every design decision so far has economised on a budget
nobody scores, and there is roughly an order of magnitude of unused allowance for
a heavier proof that makes the reduction cheaper.

## The models

**Operation count.** Counts `Nat` operations and charges each one unit. Says
packed 2,801 against list 182,642, so packed wins 65x. This is the model the
paper uses.

**Word count** (`bitcost.py`). Charges by operand size in 64-bit words. Says
packed 168,692 against list 137,678, so the list design wins slightly, and that
78% of the packed cost is the per-row reduction, which a mask would cut 3.9x.

**Reduction-step count.** Charges one unit per kernel unfolding irrespective of
width, which is what `widthcost.py` measured wall time to obey. Packed does about
720 sweep steps across the six judged sizes; the list design does about 182,642.

## Which one the judge uses

Wall clock and the ranked metric disagree, and the disagreement is the whole
problem. Wall clock obeys the step-count model: width is free, because GMP makes
a 43-word operation about as fast as a 1-word one, so packing 43 words into one
operation is a 52x win in real time.

The ranked metric does not. Calibrating it against the leaders: the two-term
peeling identity needs 2,074 additions across the six judged sizes, and
1,429,499 / 2,074 = **689 units per small-number operation**. Apply that same
rate to the word model's count for our design:

    168,692 word operations x 689 = 116,000,000    predicted
                                    132,036,341    measured

within 14%. **The judge charges by operand size, and `bitcost.py` predicts it.**
Wall clock was the wrong instrument to test that model with, and using it to
declare the model refuted was a mistake made here and then corrected.

So the ordering is real but inverted between the two instruments:

| design | wall clock | ranked metric |
| --- | --- | --- |
| packed row | 0.07 s, best | ~132M, worse |
| list rows | 3.63 s, 52x worse | ~95M predicted, better |

## What follows, and what is still open

The 92x gap is not in the arithmetic and not in the field width. `sweepMul`
cleared the last remaining cheap suspect: the kernel does share the previous row,
so nothing is being recomputed.

To reach the plateau a design needs **both** few operations and small operands,
which neither of ours has. The two-term peeling identity

    partAux (k+1) m = partAux k m + partAux (k+1) (m - (k+1))

is already proved in `SubmissionPacked.lean` and used only as a bound. Computed
rather than merely proved, it is 2,074 additions on small numbers across the six
judged sizes -- 4,000 steps or so once the shift register that supplies
`out[m-k]` in constant time is counted, which is about 2.8M units against the
leader's 1.4M. That is the design worth building, and it is closer to the list
version than to the packed one.

**Still open, and the cheapest test available:** submission 713 was the list
design, submitted on the word model, superseded within the minute by 716 when
wall clock appeared to refute it. The word model puts it near 95M, better than
the 132M on the board. When the board rescores, 713's number is a direct test of
the size-charging calibration above, at no cost. Nothing further should be built
on that calibration until it reports.
