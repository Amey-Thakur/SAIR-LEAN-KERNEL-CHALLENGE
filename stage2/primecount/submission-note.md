# Submission note - `primecount`

Paste the block below into the **Submission note** field.

```
Approach: the same bounded trial division, with nothing left between its loop and the kernel.

Background, because it decides what is worth changing. The shipped starter does not score at all: it tests primality with Nat.minFac, which dispatches to minFacAux, defined by well-founded recursion, and the Lean kernel does not unfold well-founded recursion. impl n reduces for n = 0, 1 and 2 and fails for every larger n, while every judged case is n >= 50. The live entry repaired that with an explicit fuel and a square-root bound written as p < d * d rather than through Nat.sqrt, which is itself well-founded recursion. That is the algorithm and it is unchanged here.

What changes is everything between the loop and the kernel's own arithmetic. d * d on Nat elaborates to @HMul.hMul Nat Nat Nat instHMul d d, and the kernel unfolds instHMul, Mul.mul and instMulNat before it reaches Nat.mul and its accelerator. The same holds for % and for +. Three such operations run on every iteration, and the loop runs about twenty-one thousand times at the largest judged size. The recursion, though structural, was left to the equation compiler, which produces Nat.brecOn with a Nat.below motive; an explicit Nat.rec reduces by one iota step a level and builds no below structure at all.

Measured at the boundary the rules define as counted. rules/evaluation.md counts only the target declaration's kernel check, and Lean's profiler reports a cumulative type checking phase, which is Environment.addDecl, which is that kernel check. Previous entry 1,350 ms against this entry 1,170 ms, a factor of 1.154, best of two runs each, both built and measured back to back on the same runner in the same job, over the six judged cases at n >= 50.

Wall clock cannot see this change and that is why it is not quoted. A Mathlib package pays about 1.74 s of start-up before it does any work, which is larger than the whole computation. The same trap was found and measured on fib in this repository on 18 October 2026: a file containing only that problem's expected literal, with impl appearing nowhere, cost exactly as much as the full assertion, while forcing the identical reduction against a cheap right-hand side cost nothing measurable. Every fib figure recorded here before that date was a measurement of Lean's parser rather than of the kernel. primecount's expected values are small, so the literal is not the issue here, but start-up is, and the instrument is the same one.

Correctness carries no new risk. The new loop is not proved correct from scratch: noFactorFast_eq proves it equal to the loop already in the live entry, by induction on the fuel with each step closing by rfl once the instance chain is crossed by three one-line bridging lemmas. Every existing lemma, noFactorFrom_sound, noFactorFrom_complete and the route from countP to Nat.primeCounting, is reused untouched. The only other change is one rewrite inserted into isPrimeFast_eq. The bridging lemmas are needed because rw finishes with rfl at reducible transparency, which cannot see through the instance chain even though the two sides are definitionally equal.

impl_correct is proved for every n. #print axioms Submission.impl_correct reports propext, Classical.choice and Quot.sound, all permitted.

No precomputed answers. There is no table of primes, no hardcoded value and no input-dependent branch carrying an answer. Every candidate is divided at reduction time, and the count is still the starter's own countP over List.range.

Acknowledgements and references. No Contributor Network item and no external source was used. Writing arithmetic against a type's own operations rather than through a typeclass, and preferring a recursor to a compiled recursion, are ordinary facts about how Lean elaborates and are not claimed as discoveries. What is specific to this entry is the measurement that they are worth about fifteen per cent here, taken at the judged boundary rather than on a clock that cannot resolve them, and the decision to prove the fast loop equal to the slow one rather than to reprove the bound, so that a change made for speed carries no proof risk.
```

## The other fields

| Field | Value |
|---|---|
| Problem | **primecount** |
| Submission source | **Upload Submission.lean** |
| File | `stage2/primecount/Submission.lean` |
| Reference | leave empty; nothing from the Contributor Network was used |

## Measured

| | previous entry | this entry |
| :--- | ---: | ---: |
| kernel ms, six judged cases | 1,350 | **1,170** |
| factor | - | **1.154x** |
| projected rank | 38 of 38 | **34** |

Axioms `[propext, Classical.choice, Quot.sound]`. Build green.

---

# Submission note — `primecount`

Paste the block below into the **Submission note** field.

```
Approach: a primality test the kernel can actually reduce, bounded at the square root.

The starter does not score, and the reason is not speed. It tests primality with Nat.minFac p == p. Nat.minFac dispatches even numbers by a special case and sends everything else to minFacAux, which is defined by well-founded recursion, and the Lean kernel does not unfold well-founded recursion. Timing the shipped starter at the judged sizes shows exactly that boundary: impl n reduces for n = 0, 1 and 2, and every larger n fails with "Submission.impl 3 is not definitionally equal to 2". Since every judged case is n >= 50, the starter produces no answer at all.

This entry replaces only the primality test. The count is still the starter's own countP over List.range, so the proof reuses the starter's route from countP through List.countP_eq_length_filter and List.filter_congr to Nat.primeCounting, and the single new obligation is that the fast test agrees with Nat.Prime.

The test is trial division written with an explicit fuel parameter, which makes the recursion structural and therefore reducible by the kernel, and it stops as soon as d * d passes p. Nat.sqrt is deliberately not used to express that bound, although it would read better: Nat.sqrt is itself well-founded recursion through Nat.sqrt.iter, so calling it would reintroduce the exact defect being repaired. The bound is written p < d * d, one multiplication and one comparison on numbers the kernel handles natively.

Correctness is proved in two halves because they need different things. noFactorFrom_sound carries the fuel side condition m < d + fuel, which is what licenses concluding primality; noFactorFrom_complete needs no side condition, because exhausting the fuel only ever answers true. isPrimeFast_eq discharges the side condition from m * m <= p and 2 <= m, which force m <= p, and connects to Nat.prime_def_le_sqrt through Nat.le_sqrt.

Measured on the judged sizes, in the real problem package at the pinned upstream commit. The starter reduces 3 of 12 test cases. An intermediate version that walked every divisor from p - 1 downward reduces 12 of 12 but costs 91.4 s at n = 1000, because its total work is quadratic in n. This entry reduces 12 of 12 at 3.8 s for the same case, about 21,000 divisor tests up to n = 1000 rather than 500,000. The intermediate version is kept in the repository as SubmissionLinear.lean rather than discarded, since it is a complete fix on its own and a useful check on this one.

impl_correct is proved for every n, including 0 and sizes far outside the judged range. #print axioms Submission.impl_correct reports propext, Classical.choice and Quot.sound, all permitted.

No precomputed answers. There is no table of primes, no hardcoded count and no input-dependent branch carrying an answer; every value is computed at reduction time. The expected answers used to check the kernel were computed by trial division in Python, a method deliberately unlike a sieve, and cross-checked against independently known values including pi(1000) = 168 before being trusted.

Acknowledgements and references. No Contributor Network item and no external source was used. Trial division bounded at the square root is elementary and is not claimed as new; what is specific to this entry is the observation that the shipped starter cannot be reduced by the kernel at any judged size, and the structural-recursion formulation that repairs it without reintroducing Nat.sqrt.
```

## The other fields

| Field | Value |
|---|---|
| Problem | **primecount** |
| Submission source | **Upload Submission.lean** |
| File | `stage2/primecount/Submission.lean` |
| Reference | leave empty; nothing from the Contributor Network was used |

## Measured before submitting

Run `36283533436` of `.github/workflows/mathlib-problems.yml`, challenge pinned
at `940f0a2ead23ef70ab1387edabb347e629111edd`:

| | starter | linear | this entry |
| :--- | ---: | ---: | ---: |
| cases reduced | 3 of 12 | 12 of 12 | **12 of 12** |
| n = 300 | fails | 8.65 s | **2.23 s** |
| n = 600 | fails | 30.57 s | **2.83 s** |
| n = 1000 | fails | 91.42 s | **3.79 s** |

`lake build` clean, and `#print axioms Submission.impl_correct` reports
`[propext, Classical.choice, Quot.sound]`.
