# Submission note — `polydisc`

## The block to paste into the Submission note field

```
Approach: the specification's own algorithm with two redundant big-integer
operations per coefficient removed, chosen by measuring the judged metric
rather than modelling it.

The metric is defined as an instruction count of the kernel check of one
declaration. That is reproducible outside the judge: callgrind counts guest
instructions exactly, and differencing a file against itself compiled with
debug.skipKernelTC removes the elaborator, leaving the kernel check alone. On
the shipped starter this instrument reads 10,716,251,946 against the
leaderboard's 10,322,617,420 for the same file, a ratio of 1.038, and it
reproduces to 0.014% across runners. Every figure below is that measurement.

What it says is that the judge charges for kernel reduction steps and that
operand width is nearly free: the easiest judged case costs 1,482,800,494 and
the hardest 2,377,037,902, a ratio of 1.60, where the operand widths differ by
140 and the discriminant by 142. A bit-length proxy predicts 97 for that ratio
and a schoolbook proxy 8,205. Measuring the parts separately, the coefficient
setup is 4.5% of the easiest case and 12.3% of the hardest, and the
subresultant loop is the remaining 88% to 96%, so the loop's Int operations are
the only thing worth removing.

The specification performs two per coefficient that it does not need.

First, pseudoRemainderGo finishes with scalePolynomial ((divisor.headD 0) ^
remaining) dividend. In the normal case, which every judged input takes, the
dividend has exactly one coefficient more than the divisor, so remaining starts
at 2, two cancellation steps run, and the factor is lc ^ 0 = 1: the
specification multiplies every coefficient of the widest intermediate it ever
holds by one, 276 times per judged case, and walks and rebuilds the list to do
it. scaleP returns the list unchanged when the factor is one and calls the
specification's own scalePolynomial otherwise, so an abnormal degree drop,
where the factor really is lc or lc ^ 2, still scales. The obligation is one
lemma: multiplying a list by one returns it.

Second, exactDividePolynomial tests coefficient % divisor != 0 and then divides
again for the quotient. This computes the quotient once and checks it by
multiplying back. Correctness rests on one identity, c % d = 0 if and only if
c / d * d = c, proved from Int.ediv_mul_cancel_of_emod_eq_zero and
Int.emod_def; it needs no hypothesis about the inputs and holds for a zero
divisor too, where both sides say c = 0.

Measured on the six judged sizes, starter against this entry, built and counted
on the same runner in the same job: 10,717,732,851 against 10,026,832,267, a
6.45% reduction, faster on every individual case by between 5.66% and 7.48%.

impl_correct is proved for every n. #print axioms Submission.impl_correct
reports [propext, Quot.sound], inside the permitted set and without
Classical.choice.

No precomputed answers. There is no table of discriminants, no hardcoded value
and no input-dependent branch carrying an answer; every value is computed at
reduction time from the specification's own generator stream.

Acknowledgements and references. No Contributor Network item and no external
source was used. The subresultant PRS and the Bareiss fallback are the
specification's. What is specific here is the measurement that located the cost
in the loop rather than the setup, and the observation that the loop's final
scaling is always by one in the normal case.
```

| Field | Value |
|---|---|
| Problem | **polydisc** |
| Submission source | **Upload Submission.lean** |
| File | `stage2/polydisc/Submission.lean` |
| Reference | leave empty; nothing from the Contributor Network was used |

## The instrument, first, because everything below depends on it

The rules say what the metric is. `rules/evaluation.md`: "In three separate
processes, count only the target declaration's kernel check, which reduces
`impl n` and compares it with `v`", on a "Linux PMU host" with "kernel
instruction counts", and `evaluation/judge/timer-kernel/timer_control.c`
confirms it is `PERF_COUNT_HW_INSTRUCTIONS` armed around the replay with
`perf_event_open`. So the ranked quantity is **instructions retired by the
kernel while reducing `impl n`**, and nothing else: not elaboration, not
parsing the expected literal, not the proof.

A GitHub runner has no usable PMU, so `perf` cannot reproduce that counter.
Callgrind can. It counts guest instructions exactly, with no run-to-run noise,
which is the same quantity a PMU reports for user-space work. The elaborator is
then removed by differencing the same file against itself compiled with
`debug.skipKernelTC`, which elaborates the declaration and never hands it to
the kernel.

`instrument.py` and `runbench.sh` do this, one process per case, as the judge
does. **Checked before it was trusted:**

| | instructions |
| :--- | ---: |
| sum of the six judged kernel checks, shipped starter | 10,716,251,946 |
| leaderboard, submission 692, the same file | **10,322,617,420** |
| ratio | **1.038** |

Within 4%. The residual is **not** the choice of representative inputs: two
inputs in the same band differ by 0.1% to 0.3% here, because the operation
count depends on the band and the degree and not on the particular stream. The
likely source is the measurement boundary and the processor — callgrind's
synthetic CPU selects different GMP code paths from a PMU host, and the judge
arms its counter around a replay of a binary export rather than around a
freshly elaborated declaration. For ranking two designs against each other,
which is all this is used for, a fixed 4% offset does not matter; both sides
carry it.

Two further checks that the instrument is sound:

* the baseline file, which imports and asserts nothing, differences to
  **−202,344** against signals of 1.5 billion. The noise floor is 0.014% of
  the smallest figure measured, so no ratio here is resting on the floor.
* the two hardest judged cases, which are the same difficulty, agree to
  **0.3%** on the kernel count (2,375,274,780 and 2,367,116,536) while their
  wall-clock-equivalent totals differ by **33%** (10.9 billion against 8.2
  billion, almost all of it elaboration). The clock was measuring the
  elaborator.

This is what the earlier 3% figure in this file was measured with, and why it
could not be reconciled with any model: it was a wall-clock difference on a
file whose cost is mostly elaboration.

## What the judge charges for: operations, not width

| judged case | k, coefficient bits | kernel instructions |
| :--- | ---: | ---: |
| 2^18 | 15 | 1,483,351,202 |
| 2^25 | 15 | 1,485,120,760 |
| 2^37 | 205 | 1,502,591,447 |
| 2^45 | 205 | 1,502,797,221 |
| 2^57 | 3,484 | 2,375,274,780 |
| 2^62 | 3,484 | 2,367,116,536 |

The hardest judged size costs **1.60x** the easiest. `predict.py` prices the
same six cases under four models and the ratios they predict are:

| model | predicted hardest : easiest | verdict |
| :--- | ---: | :--- |
| operation count | 1.8 | **correct** |
| sum of operand bit lengths | 97.4 | wrong by 60x |
| Karatsuba word count | 1,233 | wrong by 770x |
| schoolbook word count | 8,205 | wrong by 5,100x |

The operand widths across those cases differ by a factor of 140 and the
discriminant by 142. **Width is nearly free; the number of kernel reduction
steps is the currency.** This agrees with `widthcost.py`, with the ca-rule110
resubmission measured the same day, and it closes the question
`costmodel.py` left open.

A corollary worth keeping: the true bit-work of this computation, with GMP's
Karatsuba regime, is about 5x10^7 instructions per hardest case against a
measured 2.4x10^9. **Arithmetic is 2% of this problem and kernel overhead is
98%.** Nothing that only narrows operands can pay.

### What an operation costs, by kind

Measured by differencing pairs of loops that differ by one operation:

| operation | kernel instructions each |
| :--- | ---: |
| one step of a fuel recursion, no arithmetic at all | ~109,000 |
| one `Nat` operation, 64-bit | ~24,000 |
| one `Int` operation, 64-bit | ~132,000 |
| one `Int` operation, 3,484-bit | ~155,000 |
| one `Int` operation, 20,000-bit | ~483,000 |
| one `Int` operation, 80,000-bit | ~2,860,000 |
| one list cell: match, cons and an `Int` add | ~15,000 |

Read that table carefully, because it is where "width is free" has a limit.
From 64 bits to 3,484 bits — 54x the width — an `Int` operation costs **1.17x**
more. From 3,484 to 80,000 bits — 23x the width — it costs **18x** more. So
width is genuinely free up to a few thousand bits and roughly linear above
twenty thousand. The judged cases still come out at a ratio of 1.60 because the
operations on the widest intermediates are the few late subresultant steps,
where the polynomial has only two or three coefficients left.

**An `Int` operation costs 5.4x a `Nat` operation of the same width**, because
`Int` is an inductive type with two constructors and every operation is a case
analysis before it is arithmetic. Two further measurements of the same effect:

* a negative accumulator costs **1.48x** a positive one for identical
  arithmetic at 3,484 bits (429,519,156 against 289,863,222 for 500 steps),
  because the `negSucc` side goes through `negOfNat` and `subNatNat`. Half the
  coefficients in this problem are negative.
* **multiplying an 80,000-bit number by one costs 170,162 instructions** — the
  constructor analysis and nothing else, against 2,860,000 for a real
  multiplication at that width (90,089,227 against the control's 56,056,802
  over 200 steps). So the specification's 276 multiplications by one per case
  are worth about 2% and no more: GMP copies, it does not multiply.

A list recursion is flat in the list's length: 2,304 elements cost the same
whether the list is 24, 48 or 96 long, so the kernel's structural recursion is
not quadratic here.

## Which half of `costmodel.py` to cut: measured, not inferred

`costmodel.py` puts 55% of the operations at the hardest size in the
coefficient setup and 95% of the bit-work in the subresultant loop. Operation
count is the currency, so the operation split is the relevant one — and it
still points at the wrong half, because the setup's operations are narrow `Nat`
operations and the loop's are `Int` operations, which cost 5.4x more each.

That argument was settled by measuring the two parts separately rather than
reasoning about them. Each file asserts a small residue, so the figure is the
computation and not the comparison of a 24,000-figure literal: `polyOf n`
summed, the loop run on a polynomial supplied as a literal so that it performs
no setup at all, and the specification end to end.

| | setup alone | loop alone | whole | setup's share |
| :--- | ---: | ---: | ---: | ---: |
| k = 15 | 67,284,224 | 1,429,655,763 | 1,485,178,304 | **4.5%** |
| k = 205 | 80,983,619 | 1,431,950,527 | 1,503,688,242 | **5.4%** |
| k = 3,484 | 291,518,041 | 2,098,779,872 | 2,377,781,111 | **12.3%** |

The two parts add to the whole within 0.8%, so nothing material is missing from
the split. **55% of the operations are 12% of the cost**, and the loop is
88% to 96% of it. Note also that the loop costs the same 1.43 billion at k=15
and at k=205 — it does not care about the coefficient width — and 2.10 billion
at k=3,484, which is the only place the widest intermediates bite.

So the target is **`Int` operations inside the subresultant loop**, about 4,700
of them in every judged case regardless of difficulty. The setup is worth
having second: at the hardest size it is 291 million, which matters only once
the loop is below about a billion.

## Measured negatives, kept because they cost rounds to establish

**`Nat.pow` is not the problem.** The specification's `collectCoeffWord`
computes `2 ^ shift` with `shift` running to 3,456, and a hardest case needs
814,848 decrements of that exponent if the kernel reduces `Nat.pow` by
unfolding. Counted against the leaderboard figure, 1,734,128 such unfoldings
over the six cases would be 5,952 instructions each: one kernel step, a fit to
within 1%. It is a coincidence. Measured directly, `2 ^ 3456` reduced by the
kernel costs **327,248 instructions in total**, the same as any other single
operation on a wide number, so the kernel computes it with the bignum library.
The "exponent 298 exceeds the threshold 256, exponentiation operation was not
evaluated" warning that prompted the theory is an **elaborator** limit, and it
has no bearing on the kernel. A candidate that replaced those powers with
multiplication chains was written and discarded unsubmitted: it would have
replaced 24 accelerated powers with about 1,600 multiplications, which this
cost model prices as strictly worse.

Every other primitive a packed design would need is accelerated too, each about
one operation: `Nat.shiftLeft` by 83,616 (507,664), `Nat.shiftRight` of an
80,000-bit number (611,539), `Nat.land` against a lane mask (529,290),
`Nat.lor` (535,380), `Nat.gcd` of two 80,000-bit numbers (439,099).

**The live entry is worth 0.79%, not 3%.** Submission 1610, which replaced the
exactness test with a multiplication back, measured against the starter on the
same runner in the same job:

| case | starter | submission 1610 | |
| :--- | ---: | ---: | ---: |
| 2^18, k=15 | 1,483,351,202 | 1,499,390,542 | +1.08% |
| 2^25, k=15 | 1,485,120,760 | 1,500,772,184 | +1.05% |
| 2^37, k=205 | 1,502,591,447 | 1,516,542,249 | +0.93% |
| 2^45, k=205 | 1,502,797,221 | 1,518,683,295 | +1.06% |
| 2^57, k=3484 | 2,375,274,780 | 2,299,773,925 | **−3.18%** |
| 2^62, k=3484 | 2,367,116,536 | 2,296,122,830 | **−3.00%** |
| total | 10,716,251,946 | 10,631,285,025 | **−0.79%** |

It wins 3% where the operands are wide and **loses 1% on the four cases where
they are not**, because it trades a remainder for a multiplication and at
narrow widths the multiplication is the dearer of the two. Net 0.79%. The "3%"
recorded here before was a wall-clock figure from the hardest difficulty only,
and the bit-length model that predicted a fifth was wrong in the other
direction. **Do not score anything by bit length, and do not quote a figure
from one difficulty as the entry's improvement.**

## Packing: 16x on the arithmetic, and why it still does not reach the podium

The decisive pair in `instrument.py` performs identical arithmetic two ways:
`lcG * c - lcR * d` over a 24-element list of 3,484-bit integers, against the
same thing on one packed integer of 24 slots.

| | kernel instructions per pass |
| :--- | ---: |
| list of 24 coefficients, 72 `Int` operations | 27,266,668 |
| one packed integer, 3 `Int` operations | **1,680,894** |
| | **16.2x** |

`fused.py` then runs the whole loop that way and checks it, so this is a
verified design and not a hope: packed integers, the base started from the
input bound and doubled when the propagated bound outgrows half a slot, the
leading and second coefficients recovered by division. **All six judged
resultants agree**, with **five rebasings** over the 23 steps and a final slot
of 303,476 bits at the hardest difficulty. The alignment that makes it work is
worth writing down, because getting it wrong is silent: the `A` term takes `f`
without its leading coefficient, the `B'` term takes `g` without its leading
coefficient shifted up one slot, and the `C` term takes **`g` entire** — that
last one is what makes the top slot vanish, since `A*f1 - B'*g1 - C*g0` is
identically zero. Using `g`'s tail there instead leaves `g0*C` in the top slot
and the answer is wrong.

So a Kronecker-style packed representation is worth about an order of
magnitude on the loop, which is where the cost is, and the operand width it
costs is nearly free. That is the only route measured here that could reach the
leaders. **It is also the one that cannot be proved cheaply.** The arithmetic
on `P(B)` is exact for any base and needs no bounds; what needs a bound is
recovering the leading coefficient and the degree at each step, because the
evaluation map is injective only on coefficient lists bounded by `B/2`.
Bounding the subresultant coefficients a priori is a Hadamard-style argument
over the Sylvester matrix, and this package has no Mathlib. Three ways around
it were considered and all fail:

* unpack and repack at each step to verify the bound: the pack and unpack are
  `O(L)` operations per step, which is what the list arithmetic already costs,
  so the win collapses to a small constant;
* a second evaluation point to cross-check a recovered list: a difference of
  two lists that vanishes at both points is possible for length 3 and up, and
  ruling it out needs the same a priori bound;
* a bound propagated from the actual data each step rather than from a theorem:
  this does track the truth to within about `k` bits per step and is provable,
  but using it means changing the base each step, which again costs the `O(L)`
  repacking.

The third of those is the one to pursue, and it is better than it looks. The
bound at step `i + 1` is

    M' = (|A| + |B| + |C|) * max(Mf, Mg) / f0^2

computed from the leading coefficients actually in hand, which is about six
`Nat` operations **per step**, not per coefficient. Because `A`, `B` and `C`
are the real values and the division really is exact, the bound does not
compound. `fused.py` propagates it through all 23 steps of every judged case
and checks at each step that it really bounds the coefficients:

| case | true final width | propagated bound | factor |
| :--- | ---: | ---: | ---: |
| 2^18 | 570 bits | 1,105 bits | 1.94 |
| 2^37 | 4,881 bits | 9,188 bits | 1.88 |
| 2^57 | 80,736 bits | 151,737 bits | **1.88** |

Within a factor of 1.88 everywhere, starting from `|a_i| <= 2^(k-1)`, which is
provable from `centeredNonzeroCoeff` itself. **No Hadamard argument is needed**,
which is the opposite of what the first pass through this reasoning concluded.

One correction to that, also measured. The base cannot be fixed before the run
starts: an a priori bound on the *final* coefficient would need the Hadamard
argument after all, and propagating one from the input alone, without the
leading coefficients in hand, compounds doubly exponentially and is useless. It
can be fixed **adaptively** — start from the input bound and double the slot
whenever the propagated bound outgrows half of it, which costs one unpack and
one repack when it happens. `fused.py` counts those: **five, over 23 steps**,
at every judged difficulty. At about 48 operations each that is 240 operations
per case, which is noise beside the 4,700 the loop costs now.

What it would be worth, from `predict.py --packed`, priced at the measured
250,000 instructions per operation and GMP's `N * S^0.585` for an unbalanced
product:

| design | predicted total | against the board |
| :--- | ---: | ---: |
| loop packed, bound propagated from the data | 3,678,419,868 | 2.8x |
| loop packed, bound tight to the coefficient size | 3,189,958,752 | 3.2x |
| loop packed **and** the generator advanced by doubling jumps | **1,581,419,868** | **6.5x** |

The ordering in that table is the useful part. Packing the loop alone is worth
2.8x and stops there, because once the loop is cheap the **coefficient setup
becomes the bottleneck**: 4,435 operations at the hardest size, which at
250,000 each is 1.1 billion of the 1.59 billion that remains. So the setup is
the right second target and the wrong first one. Cutting it means advancing the
generator by doubling jumps — composing the LCG's `(A, C)` jump parameters and
stepping every packed lane at once — which replaces 697 sequential states with
about ten doublings, and needs `Nat.land` against a lane mask, measured above
at one operation.

Both together predict 1.58 billion, which is rank 10 or 11 on the published
board. Rank 3 at 1,119,039,536 needs the tight bound as well. All of it is one
formalisation project of perhaps thirty elementary lemmas — balanced-digit
recovery, `Int.natAbs` monotonicity, the evaluation homomorphism — written
against 45-minute CI rounds with no local toolchain. It is days of work, not an
afternoon, and it is the only route measured here that reaches the leaders.

## What this entry changes

Two redundant `Int` operations per coefficient, in the loop, where the cost is.

**One division where the specification does two.** `exactDividePolynomial`
tests `coefficient % divisor != 0` and then divides again for the quotient.
This computes the quotient once, binds it, and checks it by multiplying back.
Correctness rests on one identity, `c % d = 0` if and only if `c / d * d = c`,
proved from `Int.ediv_mul_cancel_of_emod_eq_zero` and `Int.emod_def`; it needs
no hypothesis about the inputs and holds for a zero divisor too, where both
sides say `c = 0`. Already live as submission 1610.

**No multiplication by one.** `pseudoRemainderGo` finishes with
`scalePolynomial ((divisor.headD 0) ^ remaining) dividend`. In the normal case
— every judged input — the dividend has exactly one coefficient more than the
divisor, so `remaining` starts at 2, two cancellation steps run, and the
factor is `lc ^ 0 = 1`. The specification multiplies every coefficient of the
widest intermediate it ever holds by one: **276 multiplications and 276 list
cells per judged case**. `scaleP` returns the list unchanged when the factor is
one and calls the specification's own `scalePolynomial` otherwise, so nothing
is assumed about `remaining`: an abnormal degree drop, where the factor really
is `lc` or `lc ^ 2`, still scales. The obligation is one lemma, that
multiplying a list by one returns it.

Everything else is the specification's own: the coefficient stream, the
derivative, the two cancellation passes, the exact division, the trimming, the
fuel, and the Bareiss fallback.

## Measured, with the method stated

Instrument as above: callgrind instruction counts, one process per case, kernel
check isolated by differencing against `debug.skipKernelTC`, in the real
problem package at pinned commit `940f0a2ead23ef70ab1387edabb347e629111edd`,
starter and candidate built and measured on the same runner in the same job.

The instrument's own reproducibility, which bounds what any figure below can
mean: the shipped starter measured **10,716,251,946** in one CI run and
**10,717,732,851** in another, on different runners, a difference of
**0.014%**. Anything larger than that is signal.

| judged case | shipped starter | this entry | |
| :--- | ---: | ---: | ---: |
| 2^18, k=15 | 1,482,800,494 | 1,398,747,059 | **−5.67%** |
| 2^25, k=15 | 1,482,583,183 | 1,398,631,936 | **−5.66%** |
| 2^37, k=205 | 1,502,783,276 | 1,417,114,611 | **−5.70%** |
| 2^45, k=205 | 1,504,740,830 | 1,417,680,925 | **−5.79%** |
| 2^57, k=3484 | 2,377,037,902 | 2,199,291,242 | **−7.48%** |
| 2^62, k=3484 | 2,367,787,166 | 2,195,366,494 | **−7.28%** |
| total | 10,717,732,851 | **10,026,832,267** | **−6.45%** |

Faster on every case, by more than 400 times the instrument's reproducibility.
Scaled to the board's figure for the starter, that predicts
**9,657,187,286**, which on the board published 18 October 2026 is **rank 27**,
up from rank 32.

`#print axioms Submission.impl_correct` reports `[propext, Quot.sound]`, inside
the permitted set and without `Classical.choice`.

**Both changes are kept, and that was checked rather than assumed.** Since the
division change loses 1% on the four narrow cases, it was worth asking whether
to drop it. Decomposing the two measurements: the scaling change on its own
would give 10,109,559,092, against 10,026,832,267 for the two together. Keeping
both is **0.82% better**, because the division change's 3% win at the two
hardest sizes outweighs its 1% loss at the other four.

The saving is larger than the multiplications alone account for — 276
multiplications by one at 170,162 each would be 47 million, and the measured
saving at the easiest size is 84 million. The rest is the list machinery that
went with them: `scalePolynomial` is a structural recursion over the whole
polynomial, so skipping it removes 276 matcher steps and 276 cons cells as
well as the arithmetic. **The operation count was right about the direction and
low by half about the size**, which is the usual direction for an operation
count that charges one unit per arithmetic operation and nothing for the
traversal carrying it.

## What is not worth trying, with numbers

| change | operations saved per case | priced at |
| :--- | ---: | ---: |
| `List.length` tests replaced by a parallel walk | ~1,800 list cells, each paying a matcher, four instance unfoldings for `+ 1` and a `Nat.add` | ~11%, and the cheap half of it is `remainder.length + 1 == g.length`, a `Bool` test with no `Decidable` instance to juggle; the `dividend.length < divisor.length` half needs `if_pos`/`if_neg` on both sides because the two `ite`s carry different instances |
| fuse the two cancellation passes | 2 of 9 `Int` ops per coefficient | ~1.2x overall, and `fused.py` verifies the algebra; the proof is the expensive part, see below |
| carry the list lengths instead of recomputing them | ~2,700 list cells | ~3% |
| `derivHL` without its quadratic `getD` walk | 276 list cells | ~0.2% |
| replace the setup's powers of two with multiplications | **negative**, adds ~1,600 operations | discarded, see above |
| a hand-rolled sign-magnitude `Int` | — | the measured 5.4x `Int` penalty is the cost of a constructor case analysis, which any signed representation also pays |

### The fused step, if someone wants the 1.2x

`fused.py` composes the two cancellation passes into

    u[i] = A*f[i+1] - B*g[i+1] - C*g[i],
    A = g0^2,  B = g0*f0,  C = g0*f[1] - f0*g[1]

and checks it against the specification's own route on all six judged
difficulties: **138 steps, all agreeing, all six discriminants correct**, and
the guard refuses rather than answers on a polynomial built to drop a degree.
Seven `Int` operations per output coefficient instead of nine, and the
multiplication by one disappears with them.

The algebra is therefore settled and the cost is the proof. It needs the step
to be guarded at runtime on five conditions, each one comparison — `f0 != 0`,
`g0 != 0`, `f.length == g.length + 1`, `C != 0`, and the result's own leading
coefficient nonzero — with anything else falling back to
`normalResultantGo` itself, so only the successful path has to be proved. That
path needs about eight lemmas:

1. `(cancelPseudoLeading a b cs ds).length = cs.length`
2. `trimLeading (c :: cs) = c :: cs` when `c != 0`
3. the two-pass composition identity, by induction on the two lists
4. `scalePolynomial 1 x = x` (already written, in `Candidate.lean`)
5. `exactDividePolynomial` agreeing with a quotient computed and checked by
   multiplying back (already written, in `Candidate.lean`)
6. three unfoldings of `pseudoRemainderGo` with the length tests resolved from
   the guard
7. the length of the fused output, for the `remainder.length + 1 == g.length`
   test
8. the fuel induction tying the fast loop to the specification's

Three to five CI rounds at the current turnaround. Worth it only after the
packed route above has been judged too expensive, because the packed route is
worth 6.5x for perhaps four times the work.
