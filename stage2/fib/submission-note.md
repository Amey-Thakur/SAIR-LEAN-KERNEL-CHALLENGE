# `fib` — a measured negative result, and why the starter stands

The live entry for `fib` is the shipped starter, `Nat.fastFib`, unmodified. It
is 13.9x its leader and it stays, because the obvious explanation for that gap
was tested on 17 October 2026 and is false.

## The hypothesis

`Nat.fastFibAux` in the pinned Mathlib is

```lean
Nat.binaryRec (fib 0, fib 1) fun b _ p =>
  if b then (p.2 ^ 2 + p.1 ^ 2, p.2 * (2 * p.1 + p.2))
  else (p.1 * (2 * p.2 - p.1), p.2 ^ 2 + p.1 ^ 2)
```

Two things in it look like they should cost the kernel more than they need to.

`p.2 ^ 2` is `HPow.hPow`, which on `Nat` resolves through `Monoid.npow`. That
is a structure projection and a recursion rather than the kernel's GMP
multiplication, and at the judged sizes the operands are tens of thousands of
bits wide: `F(150000)` has 31,348 digits. `p.1 * p.1` is one primitive.

`Nat.binaryRec` is general-purpose recursion carrying its own motive. Well-
founded recursion is exactly what stops the kernel reducing the `primecount`
and `mertens` starters at all, so it was a reasonable suspect here too.

## What was built

`SubmissionFastDouble.lean`: the same pair recurrence, with every product
written as a product, the recursion structural in an explicit fuel that halves
the index, and the odd branch reusing the even one so that `fib (2k+2)` is an
addition rather than the starter's third multiplication. Fifty-four
multiplications over eighteen bits at `n = 150000`.

It is correct and it is admissible. `lake build` closes in the real problem
package, `#print axioms Submission.impl_correct` reports exactly
`[propext, Classical.choice, Quot.sound]`, and it reduces all 13 cases. The
algorithm was checked against the plain two-term recurrence on every `n` below
600 and at 5,000, 20,000 and 150,000 before any of it was written in Lean.

## What it measured

Run `39083879520` of `.github/workflows/mathlib-problems.yml`, both designs in
the same job on the same runner:

| `n` | starter | fast-double | difference |
| ---: | ---: | ---: | ---: |
| 80,000 | 1.844 s | 1.841 s | 0.003 s |
| 150,000 | 2.076 s | 2.082 s | -0.006 s |
| total, 13 cases | 23.31 s | 23.17 s | 0.14 s |

About 1.74 s of every figure is Lean start-up, which the `n = 0` case measures
directly. The work at `n = 150000` is therefore 0.336 s against 0.342 s: the
two designs are the same to within two per cent, on signal ten times the
timer's noise.

**So neither suspect is real.** The kernel reduces `x ^ 2` on `Nat` and
`Nat.binaryRec` about as cheaply as the hand-written forms. Three
multiplications a bit against two makes no measurable difference either, which
says the per-operation overhead is not what dominates at these widths.

## Why nothing was submitted

The competition evaluates the latest entry per problem rather than the best, so
a submission with no measured gain is a pure risk: it replaces a working entry
to buy nothing. This programme has already paid once for submitting on an
unmeasured hypothesis, losing a factor of 26 on `partition`, and the rule drawn
from it was to measure first. The measurement says there is nothing here, so
`Submission.lean` remains byte-identical to the live entry, digest
`cb177ad713f320dde351dd49`.

`SubmissionFastDouble.lean` is kept because a negative result that cost a build
is worth more on the record than in a deleted file: it removes two explanations
for the 13.9x gap, and whatever the leader is doing, it is not this.
