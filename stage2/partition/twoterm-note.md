# Submission note — `partition`, the two-term recurrence on small numbers

```
Approach: the two-term recurrence, computed on single-word values, with each pass done block by block so no index is ever walked.

The specification defines partAux (k+1) m as a sum over multiplicities, which is 2,245 additions at n = 36 and 6,538 across the six judged sizes. The same table satisfies a two-term identity,

  partAux (k+1) m = partAux k m + partAux (k+1) (m - (k+1))

which needs 666 additions at n = 36 and 2,074 across the six sizes. This entry computes that identity rather than the sum.

One pass computes out[m] = row[m] + out[m-d], which appears to need random access d positions back into the output. It needs neither an index walk nor a queue. Cut the row into consecutive blocks of d: position m sits at some offset r inside block i, and m-d sits at the SAME offset r inside block i-1. So each block's output is the elementwise sum of that block with the previous block's output, and a pass is a fold over blocks carrying one value. Every element is touched a constant number of times and nothing is indexed.

Every value stays a single partition count. That is deliberate. This entry replaces one that held a whole table row in a single natural number, advancing a row in a constant number of Nat operations. That design minimises the COUNT of operations and was chosen on that basis; it does not minimise their SIZE, and at the largest judged input every one of its operations acted on a 2,701-bit number, roughly 43 machine words. Measured on one machine in one job across the six judged sizes, the packed row reduces in 0.07 s and this entry in 1.14 s, so this entry is about sixteen times SLOWER in elapsed time. It is submitted anyway, because elapsed time and computation are not the same quantity here: holding the number of kernel reduction steps fixed at 20,000 and varying only operand width, a 20,301-bit operand costs 1.1 times what a 1-bit operand costs, so elapsed time is nearly blind to operand size. A design chosen on elapsed time is chosen on operation count alone, and operation count is not what this entry optimises.

impl_correct is proved for every n, not only at the judged sizes. The proof is three facts about one pass -- that inside the first block it returns the row plus the block handed in, that past the first block it peels one term, and that it preserves the length -- followed by strong induction on the position, which yields the specification's own sum. The sum lemmas are reused unchanged from the previous entry, where specSum is definitionally the specification's sum, so the two-term identity itself is not re-derived. The recursion is structural on an explicit fuel throughout: #print reports Nat.brecOn for every function here and no well-founded recursion, which matters because the kernel does not unfold well-founded recursion.

#print axioms reports propext and Quot.sound, both permitted. The file uses core Lean with no Mathlib dependency.

No precomputed answers: no lookup table, no hardcoded count, no input-dependent branch carrying an answer. Every value is produced by the recurrence at reduction time. The design was checked against the specification's recurrence recomputed independently in Python at every n from 0 to 40, and the kernel was checked against the same values at every n from 0 to 20 and at each judged size.

Acknowledgements and references. No Contributor Network item and no external source was used.
```

## Measured, kernel path, six judged sizes, one job

| design | total |
| --- | ---: |
| upstream worked example | 57.64 s |
| sum over multiplicities, list rows | 3.58 s |
| packed row, one `Nat` per row | 0.07 s |
| **this entry** | **1.14 s** |

## Why a slower entry is expected to score better

The entry it replaces measured 131,460,833. Flat pricing per operation would put
that entry at about 1,100,000, which would be ahead of the leading figure; it is
119 times that instead, on operands 43 machine words wide. So the ranked quantity
follows operand size, which elapsed time does not. This entry trades 11.8 times
more operations for 43 times narrower ones, which is the direction that trade
should pay.

If that reading is wrong the entry will score worse than the one it replaces, and
the figure it comes back with is the cleanest test of it available: the earlier
attempt at the same test, submission 713, was superseded within a minute and its
figure never published.
