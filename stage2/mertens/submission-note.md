# Submission note — `mertens`

Paste the block below into the **Submission note** field.

```
Approach: make the factorisation reducible, then let Mathlib's own characterisation of moebius do the rest.

The starter does not score, and the reason is not speed. mertensSpec sums ArithmeticFunction.moebius, which is defined through Squarefree and the prime factorisation; both reach Nat.minFac, which is well-founded recursion, and the Lean kernel does not unfold well-founded recursion. Measured against the shipped starter at the judged sizes, impl n reduces for n = 0 and fails for every one of 25, 50, 80, 150, 300 and 500. Since every judged case is n >= 25, the starter produces no answer at all. The diagnosis was checked rather than assumed: decide cannot settle ArithmeticFunction.moebius 6 = 1 either, which places the blocker at moebius itself rather than in the summation around it.

The repair goes one layer deeper than a primality test, because the whole factorisation is unreducible, and it is built in three steps.

1. Nat.minFac_eq states that n.minFac is 2 when 2 divides n and n.minFacAux 3 otherwise, so replacing minFacAux replaces minFac. minFacAuxFast is the same upward walk written with an explicit fuel, which makes the recursion structural and so reducible. minFacAuxFast_eq states exactly how much fuel is enough, n < (k + 2 * fuel) * (k + 2 * fuel), which is where the walk stops; minFacFast_eq then gives minFacFast = Nat.minFac.

2. Nat.primeFactorsList recurses on n / minFac n, also well founded. With step 1 in hand the same walk takes a fuel, and factorsFast_eq proves the two agree whenever the fuel lasts. Each step divides by a prime factor, so n itself is far more fuel than needed.

3. With a reducible factorisation, Mathlib's own characterisation applies directly. Squarefree n is equivalent to the factor list having no duplicates, by Nat.squarefree_iff_nodup_primeFactorsList, which is decidable and reducible; moebius is then the sign of the factor count when squarefree and zero otherwise, by moebius_apply_of_squarefree, moebius_eq_zero_of_not_squarefree and cardFactors_apply. The Mertens sum is accumulated structurally and proved against the specification by peeling one term with Finset.sum_range_succ.

Nothing about the specification is changed or approximated; every value is Mathlib's moebius, reached by a route the kernel can travel.

Measured in the real problem package at the pinned upstream commit. The starter reduces 1 of 11 test cases. This entry reduces 11 of 11: n = 300 in 3.17 s and n = 500 in 4.22 s, against a 120 s target for the hardest group.

impl_correct is proved for every n, including 0 and sizes far outside the judged range. #print axioms Submission.impl_correct reports propext, Classical.choice and Quot.sound, all permitted.

No precomputed answers. There is no table of moebius values, no hardcoded sum and no input-dependent branch carrying an answer. The expected values used to check the kernel were computed twice by unlike methods, trial-division factorisation and a linear sieve, which agree at every k up to 500; an earlier version of that check carried M(500) = -7 from memory, the cross-check caught it, and both methods give -6.

Acknowledgements and references. No Contributor Network item and no external source was used. Trial division and the squarefree characterisation of moebius are standard and are not claimed as new; what is specific to this entry is the observation that the shipped starter cannot be reduced by the kernel at any judged size, and the three-step bridge that restores reducibility without changing what is computed.
```

## The other fields

| Field | Value |
|---|---|
| Problem | **mertens** |
| Submission source | **Upload Submission.lean** |
| File | `stage2/mertens/Submission.lean` |
| Reference | leave empty; nothing from the Contributor Network was used |

## Measured before submitting

Run `36285080406` of `.github/workflows/mathlib-problems.yml`, challenge pinned
at `940f0a2ead23ef70ab1387edabb347e629111edd`:

| n | starter | this entry |
| ---: | :--- | ---: |
| 25 | fails | 2.09 s |
| 50 | fails | 2.17 s |
| 80 | fails | 2.28 s |
| 150 | fails | 2.52 s |
| 300 | fails | 3.17 s |
| 500 | fails | **4.22 s** |

`lake build` clean, and `#print axioms Submission.impl_correct` reports
`[propext, Classical.choice, Quot.sound]`.
