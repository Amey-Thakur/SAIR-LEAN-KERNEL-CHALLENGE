# Baseline submission note

Paste the block below into the **Submission note** field for each of the seven
problems that previously had no entry. It is deliberately plain about what the
entry is.

```
Baseline entry: the reference starter from the challenge repository, unmodified.

This is the participant starter shipped in problems/<name>/Submission.lean at the pinned upstream commit, submitted without change so that the problem has a valid entry on record while optimisation continues. It is not claimed as original work and no performance claim is made for it.

It is submitted because it is correct rather than because it is fast. The starter already discharges the required theorem: for most problems impl is definitionally the specification and impl_correct is rfl, for primecount it is a short proof through Nat.prime_def_minFac, and for sha256 the starter carries a real message-schedule optimisation with its own proof. None of the seven uses sorry, native_decide, partial or unsafe.

The latest entry per problem is the one evaluated rather than the best, so any later submission for this problem is intended to replace this one, and this note will not be reused for it.
```

## Which problems this covers

`fib`, `mertens`, `primecount`, `ca-rule110`, `permanent`, `polydisc`,
`sha256`. Not `partition`, which already has the packed-row entry and must not
be overwritten by a baseline.
