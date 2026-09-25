# Submission note — `partition`

Paste the block below into the **Submission note** field. It is 2,914 of the
5,000 characters allowed.

```
Approach: the whole table row in one natural number.

The locked specification defines partAux k m by recursion on the largest allowed part, so evaluating it directly re-derives the same partAux k m along every path that reaches it: about 128,000 calls at n = 36 for a table holding only 1,369 distinct entries.

This submission keeps the recurrence exactly as specified and changes only where the values live. Row k is held as a single Nat, with the entry for target m in the m-th field of w bits. The row step is then the specification's own sum lifted to that representation:

  R' = ( R + (R <<< d*w) + (R <<< 2*d*w) + ... ) mod 2^(w*(n+1))

because field m of that sum is the sum over all j with j*d <= m of field (m - j*d) of R, which is exactly the specification's sum over multiplicities of the largest part d. The kernel performs each term as one arithmetic operation on one large integer, whatever the row's length: 528 operations at n = 36 in place of roughly 32,000 list-traversal steps for the same table held as a list.

Correctness. Fields cannot carry into one another provided every entry fits in w bits. Peeling one term off the specification's sum gives

  partAux (k+1) m = partAux k m + partAux (k+1) (m - (k+1))

and from it partAux k m <= 2^(m+k) follows by induction: the first summand is at most 2^(m+k), the second at most 2^m, and together they stay below 2^(m+k+1). Both indices run no higher than n, so w = 2n+1 bits are enough. That bound is proved in the file rather than assumed; it is the only thing standing between this representation and a wrong answer.

impl_correct is proved for every n, including 0 and values far outside the test ranges. The file is self-contained: the packing, the indexed read and every supporting lemma are defined in the submission rather than imported, so each lemma is about the exact function the kernel reduces. It uses core Lean only, with no Mathlib dependency. #print axioms Submission.impl_correct reports propext and Quot.sound.

No precomputed answers. There is no lookup table, no hardcoded value and no input-dependent branch carrying an answer. Every count is computed from the specification's recurrence at evaluation time. impl 0 through impl 13 were checked against the counts known by hand, and the six published group endpoints against the recurrence recomputed independently in Python.

Acknowledgements and references. No Contributor Network item and no external source was used. Holding a dynamic-programming row as the digits of one large integer, so that a strided sum becomes a shift and an add, is a known idiom in bit-parallel dynamic programming and is not claimed as new; what is specific to this entry is lifting the locked specification's own multiplicity sum into that form, and the 2^(m+k) bound that licenses it. The specification and the test structure are the competition's own.
```

## The other fields

| Field | Value |
|---|---|
| Problem | **Integer partitions** — not Fibonacci |
| Submission source | **Upload Submission.lean** |
| Saved Playground solution | not used |
| File | `SubmissionPacked.lean`, renamed to `Submission.lean` |
| Reference | leave empty; nothing from the Contributor Network was used |
| Sharing agreement | as the form requires |

## Before pressing submit

- The file must be named `Submission.lean`.
- It is 20,530 bytes, against the 1 MiB limit.
- `lake build` closes the proof, and `#print axioms Submission.impl_correct`
  reports `propext` and `Quot.sound`, both permitted.
- The latest entry per problem is the one evaluated, **not the best**, so
  nothing slower should be uploaded after this one.
