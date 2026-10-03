# Three cost models, two instruments, and which one the judge uses

This file exists because the `partition` entry was reasoned about with three
different cost models in one day, each of which contradicted the others, and two
of them produced a submission. The record is kept so the next attempt starts from
what was measured rather than from whichever model was most recently believed.

## THE ANSWER, 3 Oct 2026: the metric counts reduction STEPS

Everything below that argues the ranked metric charges by operand size is WRONG,
and was settled by submitting the design it implied.

| design | operations | operand width | measured |
| --- | ---: | ---: | ---: |
| packed row (716) | ~1,600 | 43 words | **131,460,833** |
| two-term, small numbers (796) | ~18,820 | 1 word | **3,396,012,941** |

Twenty-six times worse. Per operation that is roughly 180,000 units for the
narrow design against 82,000 for the wide one, so **narrow operands cost MORE
per operation, not less**. The ranked quantity follows the number of kernel
reduction steps and is close to blind to width -- which is exactly what
`widthcost.py` had already measured for elapsed time, holding the step count at
20,000 and varying only width, where a 20,301-bit operand cost 1.1 times a
1-bit one. Elapsed time and the ranked metric agree after all. They were never
in conflict.

**Where the reasoning went wrong.** The argument against flat pricing was: the
packed entry performs about 1,600 operations, so at the leaders' implied 689
units per operation it would score about 1.1M and beat rank 1; it scores 119
times that, therefore width must be charged. The conclusion does not follow from
the premise -- the operation count was the weak link, not the pricing model, and
a single ratio was used to rule out the simpler hypothesis. The simpler
hypothesis was right.

**What this costs.** Submission 796 replaced a 131,460,833 entry with a
3.4 billion one and dropped the standing from rank 15 to rank 24 of 31 over
three days, because the board publishes once daily and takes only the latest
submission before its 00:00 UTC cutoff. Submission 1103 restores the packed
design.

**The rule that follows.** Improve this entry by removing reduction STEPS. Do not
narrow operands, do not replace the modulus with a mask, do not tighten the
field width `2n+1` -- all three are width work and width is nearly free. The
packed design performs about `n * H(n)` sweep unfoldings per size; a geometric
multiplier built by doubling would make each row O(log) instead of O(n/d), which
is roughly 1.7x fewer steps, and that is the direction worth proving.

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

## The two-term design, built

`TwoTerm.lean` computes the peeling identity instead of proving it and walking
away. `SubmissionTwoTerm.lean` is the same file with the namespace renamed, so
the judge sees `Submission.impl` and `Submission.impl_correct`.

The formulation is simpler than it looks. One pass computes
`out[m] = row[m] + out[m - d]`, which appears to need random access `d` positions
back into the output. It needs neither an index walk nor a queue: cut the row into
consecutive blocks of `d`, and position `m` at offset `r` in block `i` has
`m - d` at the SAME offset `r` in block `i - 1`. So each block's output is the
elementwise sum of that block with the previous block's output, which is a fold
carrying one value.

`impl_correct` is proved for every `n`, not only at the judged sizes. The proof is
(a) the first block returns the row plus whatever block was handed in, (b) past
the first block the pass peels one term, (c) a pass preserves the length; then
strong induction on `m` gives the specification's sum, and `specSum_lt` and
`specSum_ge` are reused verbatim from `SubmissionPacked.lean`, where `specSum` is
definitionally the specification's own sum.

### What it costs

| design | elementary steps, six judged sizes |
| --- | ---: |
| sum over multiplicities, packed row | 168,692 word operations |
| sum over multiplicities, list (submission 713) | 137,678 |
| **two-term, list** | **18,820** |

of which only 2,074 are additions: the bookkeeping is 8.1x the arithmetic, and
that is where the remaining distance to the plateau sits. Fusing `take` and `drop`
into the emit would save about a quarter of it, not the 7x the plateau needs, so
the overhead is not what separates this from rank 1.

### Two routes to the same prediction, both wrong

At the 689-unit rate derived from the leaders, 18,820 steps price at
**12,966,980**. Independently, and with no assumption about the leaders at all,
the two-term design is 7.3x fewer steps than the sum-form list design, so it
should score 1/7.3 of whatever submission 713 scores -- about 13.0M if 713 comes
in near 95M, about 18.0M if 713 comes in at 132M.

Both routes predicted about 13M. The measured figure was 3,396,012,941, which is
262 times the prediction and 26 times WORSE than the entry it replaced. Both
routes shared the same false premise, that the metric charges by operand size,
so agreeing with each other proved nothing. Two derivations of one assumption
are not two pieces of evidence. An earlier
count in `twoterm.py` said 10.1M and rank 8; it charged one unit for cutting a
block where Lean pays two, once for `take d` and once for `drop d`, and understated
the design by a third.

### What the plateau is not

Two hypotheses about the 1.43M plateau are already ruled out, and recording that
is worth more than another guess.

**It is not bought with a heavy proof.** Proof cost is unranked, and rank 2 spends
39.4 billion units on `correctnessWork`, which suggested the leaders prove
something hard -- Euler's pentagonal number theorem would give p(n) in far fewer
additions -- to get a cheap computation. But **rank 4 reaches 1,457,591 with
`correctnessWork` of 3,999,155,807, only 1.16x ours.** The plateau is reachable
with a proof no larger than the one already written here, so it is a
representational trick and not a theorem.

**It is not reachable by fusing the fold.** Replacing the block formulation with a
single recursion that walks the row while consuming the previous block costs MORE,
not less: per element it pays a head, a tail, a cons to the output, a cons to the
accumulator and the addition, plus an amortised reverse, which is about six units
against the block version's four. An earlier note here said fusing would save
about a quarter; it does not, and the block form is already the cheaper one.

**What remains unexplained.** At about 700 units per single-word operation --
which our own packed entry corroborates, 132,036,341 over 168,692 word operations
being 783 -- the leaders' 1,429,499 buys roughly 1,900 operations, against the
2,074 additions the identity needs at minimum. That is essentially zero
bookkeeping, which no list representation can achieve. A packed row does reach
about 720 operations across the six sizes, but each is charged by width, and the
2,701-bit row makes each one cost 183,000. Getting to 1,985 per operation would
need operands of two or three machine words, and a row wide enough to hold
p(36) = 17,977 in 37 fields cannot be that narrow. So neither of our two
representations explains the plateau, and the mechanism is still open.
