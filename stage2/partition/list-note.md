# Submission note — `partition`, list rows

```
Approach: rows of small numbers, no packing.

This replaces a packed-row entry that the leaderboard measured at 132,036,341 units of work against a leader at 1,429,499. That entry held a whole table row in one natural number, which minimises the COUNT of Nat operations and was chosen on that basis. The ranking metric is kernel work, not operation count, and the two disagree here: packing made every operation act on a 2,701-bit number, roughly 43 machine words, and the per-row reduction became a division by a 2,701-bit constant, which is superlinear. A cost model charging by operand size puts 78% of that entry's cost in the reduction alone.

This entry keeps every value a small number. Row k is a List Nat whose m-th entry is partAux k m, row k+1 is built from row k, and the previous row is named once so it is built once. Each cell is the specification's own sum with the recursive call replaced by a lookup, so correctness is a congruence rather than a re-derivation: two functions that agree everywhere the sum looks give the same sum, and the sum only ever reads indices m - j*d, which never exceed m.

What it pays for is indexing: reading position m of a list walks m cons cells. That is the cost the packed design was built to avoid, and the measurement says it was the cheaper cost of the two.

impl_correct is proved for every n. #print axioms reports only the permitted axioms, and the file uses core Lean with no Mathlib dependency.

No precomputed answers: no lookup table, no hardcoded count, no input-dependent branch carrying an answer. Every value comes from the specification's recurrence at reduction time, and the results were checked against the recurrence recomputed independently in Python at every n from 0 to 13 and at the six judged sizes.

Acknowledgements and references. No Contributor Network item and no external source was used.
```

Submitted to calibrate what a list step costs in kernel work, which the
authoring machine cannot measure: it reports wall time on a virtualised runner
and the judge counts hardware instructions.
