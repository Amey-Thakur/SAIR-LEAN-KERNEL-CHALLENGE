# Submission note — `permanent`

```
Approach: scan each row once, before the search, instead of once per node.

The specification expands the permanent as a depth-first search over injective column choices, with a bit mask recording the columns already taken. At every node it folds over List.range width, reads row.getD j 0, and skips the cell when the entry is zero or the column is used.

Two costs compound there, and neither is the search. The matrix is sparse: permanentEntry gives a diagonal and exactly two seeded off-diagonal columns, so a row has at most three non-zero entries while the fold examines all of them. And row.getD j 0 walks the list, so reading column j costs j steps, making one row scan quadratic in the width rather than linear. Together that is roughly 256 list steps at each node to find three useful ones, paid again at every node of a depth-16 search.

Both are fixed once, before the search starts, by turning each row into its list of non-zero (column, entry) pairs. That transformation costs one quadratic scan per row in total rather than per node, and the search then touches only the cells that can contribute.

Nothing about the traversal changes: same order, same mask, same arithmetic, same answer. The correspondence is foldl_pairs_eq, an induction whose step is the observation the specification already makes, that an entry of zero contributes nothing, so dropping the zero cells before the fold and testing for them inside it agree.

One detail is worth recording because it cost three attempts. The specification's guard is entry = 0 || used.testBit j, which mixes a Prop with a Bool, so Lean inserts a decide. Collapsing that coercion in place, against the compound term row.getD j 0, defeated simp every time. Stated on plain variables it collapses immediately, so the two branches are lifted into guard_zero and guard_nonzero and rewritten with thereafter, which is both shorter and robust.

Measured in the real problem package at the pinned upstream commit, starter and candidate in the same continuous-integration job on the same runner, because wall time on a shared runner varies by about twenty per cent between runs. At the judged dimensions: 6 gives 0.41 s against 0.38 s, 12 gives 3.14 s against 1.51 s, and 16 gives 27.12 s against 8.79 s. That is a factor of about 3.1 at the hardest judged size.

impl_correct is proved for every n, including dimensions far outside the judged range. #print axioms Submission.impl_correct reports propext alone, one of the three permitted, without Classical.choice or Quot.sound.

No precomputed answers. There is no table of permanents, no hardcoded value and no input-dependent branch carrying an answer; every entry comes from the specification's own permanentEntry at reduction time. Expected values used to check the kernel came from Lean's own compiler through #eval, a different evaluator from the kernel being measured.

Acknowledgements and references. No Contributor Network item and no external source was used. Exploiting sparsity in a permanent expansion is elementary and is not claimed as new; what is specific to this entry is the observation that the specification's own zero test is what licenses hoisting the scan out of the search, and the correspondence proof that makes the hoist legitimate.
```

## Measured before submitting

Run `36286793984`, challenge pinned at `940f0a2ead23ef70ab1387edabb347e629111edd`.
Build clean; `#print axioms Submission.impl_correct` reports `[propext]`.

| dimension | starter | this entry |
| ---: | ---: | ---: |
| 6 | 0.41 s | 0.38 s |
| 12 | 3.14 s | 1.51 s |
| 16 | 27.12 s | **8.79 s** |
