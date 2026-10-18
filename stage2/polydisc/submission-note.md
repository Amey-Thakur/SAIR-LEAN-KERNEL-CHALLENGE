# Submission note — `polydisc`

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

Within 4%, and the residual is explained: the counter also sees the kernel
checking the few declarations the benchmark file itself adds.

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
| one `Nat` operation, 64-bit | ~24,000 |
| one `Int` operation, 64-bit | ~132,000 |
| one `Int` operation, 3,484-bit | ~209,000 |
| one `Int` operation, 20,000-bit | ~537,000 |
| one `Int` operation, 80,000-bit | ~2,900,000 |
| one list cell: match, cons and an `Int` add | ~15,000 |

**An `Int` operation costs 5.4x a `Nat` operation of the same width**, because
`Int` is an inductive type with two constructors and every operation is a case
analysis before it is arithmetic. A list recursion is flat in the list's
length: 2,304 elements cost the same whether the list is 24, 48 or 96 long, so
the kernel's structural recursion is not quadratic here.

## Which half of `costmodel.py` to cut, and why it is not the setup

`costmodel.py` puts 55% of the operations at the hardest size in the
coefficient setup. That is true and it is still the wrong half to cut, for two
measured reasons.

1. The setup's operations are narrow `Nat` operations at ~24,000 each; the
   loop's are `Int` operations at 209,000 and up. About 4,300 setup operations
   price at roughly 1x10^8, which is **4%** of the hardest case.
2. The easiest judged case has a setup 15x smaller than the hardest — 290
   operations against 4,300 — and still costs **62%** of it. What the two
   cases share is the subresultant loop, whose operation count does not depend
   on the coefficient width at all. If the setup were the cost, the easy cases
   would be nearly free. They are not.

So the target is **`Int` operations inside the subresultant loop**, which is
about 4,700 operations in every judged case regardless of difficulty.

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

**A bit-length proxy is not just inaccurate here, it is inverted.** Scoring a
division at `a_bits + b_bits` put the removed exactness test at a fifth of the
cost. Priced by operation count it is 253 operations of about 4,700 in the
loop, and the measurement agrees: the entry that removed it (submission 1610)
measures 1,499,390,542 against the starter's 1,483,351,202 at the easy sizes
and 2,299,773,925 against 2,375,274,780 at the hardest — about 3% at the
hardest size and nothing at the easy sizes, where the division it replaced was
narrow. Do not score anything by bit length.

## Packing: 16x on the arithmetic, and why it still does not reach the podium

The decisive pair in `instrument.py` performs identical arithmetic two ways:
`lcG * c - lcR * d` over a 24-element list of 3,484-bit integers, against the
same thing on one packed integer of 24 slots.

| | kernel instructions per pass |
| :--- | ---: |
| list of 24 coefficients, 72 `Int` operations | 27,266,668 |
| one packed integer, 3 `Int` operations | **1,680,894** |
| | **16.2x** |

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

Proof cost is unranked and the leaders on other problems in this competition
spend tens of billions of units on it, so a Hadamard bound in core Lean is
where the podium on this problem lives. It is a formalisation project, not an
afternoon.

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
starter and candidate on the same runner in the same job.

<!-- ROUND 2 RESULTS GO HERE -->

## What is not worth trying, with numbers

| change | operations saved per case | priced at |
| :--- | ---: | ---: |
| fuse the two cancellation passes | 2 of 9 `Int` ops per coefficient | ~1.14x overall; the fused form's three products are all at the wider operand size, so it pays back only where width is free |
| carry the list lengths instead of recomputing them | ~2,700 list cells | ~3% |
| `derivHL` without its quadratic `getD` walk | 276 list cells | ~0.2% |
| replace the setup's powers of two with multiplications | **negative**, adds ~1,600 operations | discarded, see above |
| a hand-rolled sign-magnitude `Int` | — | the measured 5.4x `Int` penalty is the cost of a constructor case analysis, which any signed representation also pays |
