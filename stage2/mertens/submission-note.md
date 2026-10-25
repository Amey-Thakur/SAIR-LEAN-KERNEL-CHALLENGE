# Submission note - `mertens`

Paste the block below into the **Submission note** field.

```
Approach: the same algorithm, with three places where the kernel was doing work that is not arithmetic.

Background. The shipped starter cannot be reduced: Nat.minFac dispatches to minFacAux, Nat.primeFactorsList recurses on n / minFac n, and both are well-founded recursion, which the Lean kernel does not unfold. The live entry replaced each with a fuelled structural walk, bounded by n < k * k written out rather than through Nat.sqrt, which is itself well founded. That is the algorithm and it is unchanged here.

Three changes, none of which touches the algorithm.

First, the inner walk. k * k on Nat elaborates to @HMul.hMul Nat Nat Nat instHMul k k, and the kernel unfolds instHMul, Mul.mul and instMulNat before it reaches Nat.mul and its own accelerator; the same holds for % and +. Three such operations run on every iteration of the trial-division walk, which is the innermost loop of the whole problem: once per candidate divisor, per factorisation, per n.

Second, the outer sum. sumMu recurses n times and is the outermost loop, so whatever a level costs is paid n times over. That recursion was left to the equation compiler, which produces Nat.brecOn with a Nat.below motive; an explicit Nat.rec reduces by one iota step with no below structure at all. The accumulator is written Int.add for the same reason the walk is written Nat.mul.

Third, the sign. (-1 : Int) ^ fs.length goes through Monoid.npow, which performs one multiplication per prime factor, and it is evaluated once for every n up to the judged size. The parity of the length decides the answer in one Nat.mod and a branch.

Measured at the boundary the rules define as counted. rules/evaluation.md counts only the target declaration's kernel check, and Lean's profiler reports a cumulative type checking phase, which is Environment.addDecl, which is that check. Previous entry 1,360 ms against this entry 1,170 ms over the five judged cases: a factor of 1.162 on the minimum of five repetitions, and 1.145 on the median. Both designs are built and measured back to back in the same job on the same runner.

The number of repetitions mattered and is worth recording. Two repetitions could not resolve this change at all. On a shared runner the spread within a single job reached ten per cent, which is comparable to the effect, and two successive measurements of the very same pair of designs gave 1.094 and 1.033. Five repetitions with the minimum taken is stable and agrees with the median to within two per cent. A ratio is only as good as the spread underneath it.

Wall clock cannot see any of this, which is why none is quoted. A Mathlib package pays about 1.74 s of start-up before it does any work, larger than the whole computation. The same trap was measured on fib in this repository on 18 October 2026, where a file containing only that problem's expected literal, with impl appearing nowhere, cost exactly as much as the full assertion.

Correctness carries no new risk. None of the three new forms is proved correct from scratch: minFacAuxRaw_eq, sumMuRaw_eq and signOf_eq prove each equal to what the live entry already does, so every existing lemma, from minFacFast_eq through factorsFast_eq and muFast_eq to the route into ArithmeticFunction.moebius, is reused untouched. Four one-line bridging lemmas are needed because rw finishes with rfl at reducible transparency, which cannot see through an instance chain even where the two sides are definitionally equal. One consequence is worth stating: a case split has to be made on the raw form, since the goal after unfolding reads k.mod 2 and a hypothesis about k % 2 will not match it syntactically.

impl_correct is proved for every n. #print axioms Submission.impl_correct reports propext, Classical.choice and Quot.sound, all permitted.

No precomputed answers. There is no table of Moebius values or of primes, no hardcoded value and no input-dependent branch carrying an answer; every factorisation is computed at reduction time.

Acknowledgements and references. No Contributor Network item and no external source was used. Writing arithmetic against a type's own operations rather than through a typeclass, preferring a recursor to a compiled recursion, and deciding a sign by parity rather than by exponentiation are ordinary facts about how Lean elaborates and are not claimed as discoveries. What is specific here is the measurement that they are jointly worth about fifteen per cent on this problem, taken at the judged boundary with enough repetitions to exceed the runner's own spread, and the decision to prove each fast form equal to the slow one so that a change made for speed carries no proof risk.
```

## The other fields

| Field | Value |
|---|---|
| Problem | **mertens** |
| Submission source | **Upload Submission.lean** |
| File | `stage2/mertens/Submission.lean` |
| Reference | leave empty; nothing from the Contributor Network was used |

## Measured

| | previous entry | this entry |
| :--- | ---: | ---: |
| kernel ms, five judged cases, min of 5 | 1,360 | **1,170** |
| factor, min / median | - | **1.162x / 1.145x** |
| projected rank | 35 of 35 | **34** |

Axioms `[propext, Classical.choice, Quot.sound]`. Build green, 0 errors.

---

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
