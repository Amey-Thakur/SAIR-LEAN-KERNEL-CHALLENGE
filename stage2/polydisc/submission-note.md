# Submission note — `polydisc`

Paste the block below into the **Submission note** field.

```
Approach: the specification's own algorithm, with one redundant big-integer division removed.

The shipped starter is `impl := discSpec`, the specification itself, so nothing about it had been measured. Transcribing it and counting shows where its work goes: about 9,250 kernel operations at the hardest judged difficulty, of which 55% are the coefficient setup and 45% the subresultant loop, while 95% of the total bit-length flowing through the multiplications and divisions is in the loop.

Inside that loop, `exactDividePolynomial` divides every coefficient of the pseudo-remainder by the square of the previous leading coefficient, and it does so like this: `if divisor == 0 || coefficient % divisor != 0 then none else ... coefficient / divisor ...`. That is two full divisions of the same pair, one to decide whether the division is exact and the same division again for the quotient. `%` on `Int` is not cheaper than `/`; `Int.emod_def` says `a % b = a - b * (a / b)`.

This entry computes the quotient once, binds it, and checks it by multiplying back: one division and one multiplication instead of two divisions, on operands that reach about eighty thousand bits at the hardest difficulty. The guard is preserved exactly, so a non-exact division still returns `none` and the Bareiss fallback is still selected on the same inputs. Nothing else changes: the polynomial, the derivative, the pseudo-remainder and the fallback are the specification's own.

Correctness rests on one identity, `c % d = 0` if and only if `c / d * d = c`, proved from `Int.ediv_mul_cancel_of_emod_eq_zero` and `Int.emod_def`. It needs no hypothesis about the inputs and holds for a zero divisor too, where both sides say `c = 0`. The two guards are then equal as Booleans, the bodies around them are already identical, and the rest of the chain follows by induction on the loop's fuel.

impl_correct is proved for every n. `#print axioms Submission.impl_correct` reports `[propext, Quot.sound]`, which is inside the permitted set and does not use `Classical.choice`.

No precomputed answers. There is no table of discriminants, no hardcoded value and no input-dependent branch carrying an answer; every value is computed at reduction time from the specification's own LCG stream.

Acknowledgements and references. No Contributor Network item and no external source was used. The subresultant PRS and the Bareiss fallback are the specification's, not this entry's. What is specific here is the observation that the exactness test and the quotient are the same division performed twice, and the identity that lets one of them go.
```

## The other fields

| Field | Value |
|---|---|
| Problem | **polydisc** |
| Submission source | **Upload Submission.lean** |
| File | `stage2/polydisc/Submission.lean` |
| Reference | leave empty; nothing from the Contributor Network was used |

## Measured before submitting

Run `.github/workflows/polydisc.yml`, challenge pinned at
`940f0a2ead23ef70ab1387edabb347e629111edd`, starter and candidate built and
timed in the same job on the same runner.

| | starter | this entry |
| :--- | ---: | ---: |
| eleven cases, one process each | 12.73 s | **12.59 s** |
| eight hardest cases, one process | 6.57 s | **6.36 s** |
| cases reduced | 11 of 11 | **11 of 11** |

The eleven expected values were computed by the specification and confirmed
against Bareiss elimination on the full Sylvester matrix, which shares no code
with the subresultant route: no PRS, no monic reduction, no exact division.

## What the measurement corrected

`costmodel.py` predicted about a fifth of the bit-work would go, and the
measured saving at the hardest difficulty is **about 3%**. The model
overstated it, and the reason is worth keeping: it scored a division at
`a_bits + b_bits`, which is a poor proxy. The dividend here is only about
twice the divisor, so the quotient is short and the division is far cheaper
than its operand lengths suggest. **A bit-length proxy overestimates the cost
of a division by a nearly equal divisor.**

A per-case measurement cannot see a change this size: Lean start-up is 0.95 s
of every figure, the largest judged case is about 1.1 s of work, and two cases
at the same difficulty differed from each other by 0.5 s. `bulk.py` exists for
that reason, putting eight distinct hardest-difficulty inputs in one process so
start-up is paid once against about six seconds of work.

## Why this was submitted and the `fib` experiment was not

Both were correct and admissible; only this one measured faster. It also
differs in kind. The `fib` candidate exchanged one formulation for another of
the same cost, so there was nothing to gain. This removes 253 big-integer
divisions per hardest case and adds 253 multiplications by a short quotient,
which no instruction counter can charge more for. The direction is the same
under the model and under the clock.

## What this does not do

It does not approach a podium. Rank 3 on this problem is 1,118,777,367 against
this entry's 10,321,620,511, a factor of **9.2**, and a 3% saving is not that.
It is the cheapest honest improvement available, and it leaves the
infrastructure — the transcription, the independent check, the cost model, the
workflow and the bulk timer — in place for the next one. The costmodel says
where to look: 43% of the bit-work is the pseudo-remainder's two products per
coefficient, and 55% of the operations are the coefficient setup, which is
almost free in bit-work and so is the place to cut if the judge charges per
operation rather than per bit.
