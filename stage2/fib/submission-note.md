# `fib` — the old measurement was invalid, and 2.0x is what is actually there

The live entry for `fib` is still the shipped starter, `Nat.fastFib`,
unmodified: 96,290,412 instructions, rank 47 of 47, with rank 3 at 7,121,194,
a gap of 13.5x.

On 17 October 2026 this file recorded that a hand-written fast-doubling design
measured identically to the starter, and concluded that neither `Monoid.npow`
nor `Nat.binaryRec` was real. **That conclusion was wrong, and it was wrong
for a reason worth keeping.** Re-measured on 18 October at the boundary the
judge actually uses, the same design is 1.42x the starter and a further change
takes it to 2.0x. Top 3 is still out of reach, and the measurements below say
why in terms of what the kernel charges for.

## 1. Why the old number measured nothing

`rules/evaluation.md` is explicit about what is counted: *"In three separate
processes, count only the target declaration's kernel check, which reduces
`impl n` and compares it with `v`."* Not parsing. Not elaboration. Not the
`rfl` tactic's own reduction.

`timecases.py` times a whole `lake env lean` process on a file asserting
`impl n = <expected literal>`. At `n = 150000` that literal is 31,348 decimal
digits. Five files separate what the figure is made of — run
[`39156926574`](https://github.com/Amey-Thakur/SAIR-LEAN-KERNEL-CHALLENGE/actions/runs/39156926574),
whole-process wall clock, best of two, `n = 150000` throughout:

| file | what it contains | seconds | above start-up |
| --- | --- | ---: | ---: |
| `T0` | the import and nothing else | 1.53 | — |
| `T1` | the 31,348-digit literal alone, no `impl` anywhere | 1.81 | **0.28** |
| `T2` | the same value as a hex literal, alone | 1.74 | 0.21 |
| `T3` | `impl 150000 % (2^64 - 59)`, which forces the whole reduction | 1.52 | **0.00** |
| `T4` | `impl 150000 = <31,348-digit literal>` — what `timecases.py` does | 1.81 | **0.28** |

`T4` and `T1` are the same number, and `T1` never mentions `impl`. `T3` forces
exactly the same computation as `T4` and costs nothing measurable. **The
0.336 s this file recorded as "the work at n = 150000" was Lean reading its own
expected answer.** The kernel's reduction of `impl 150000`, measured directly,
is 2.1 ms: the old harness was reporting a quantity about a hundred times
larger than the one it meant to report, and identical in both designs by
construction.

The n-scaling said so at the time and was not read: the recorded "work" rose
3.2x from `n = 80000` to `n = 150000`, which is the 3.5x of a quadratic decimal
parse, not anything the kernel does.

## 2. The instrument that does work

`set_option profiler true` reports a cumulative `type checking` figure, and
type checking is `Environment.addDecl`, which is the kernel. That is the judged
boundary exactly. `bulk.py` emits twelve distinct inputs per judged group with
the cheap right-hand side above, so start-up is paid once, nothing is served
from the kernel's cache, and the three groups separately give the scaling.
`measure.sh` runs every design through it in one job on one runner.

Runners differ by up to 40% between runs, so only ratios measured inside one
job are used. Three independent runs:

| design | f1 | f2 | f3 | judged total | vs starter |
| --- | ---: | ---: | ---: | ---: | ---: |
| starter | 2.88 | 3.33 | 3.54 | 19.5 ms | — |
| `Candidate.lean` — structural fuel, specialised top | 2.09 | 2.43 | 2.45 | 13.9 ms | **1.40x** |
| `CandidateRaw.lean` — the above, plus raw `Nat.*` | 1.44 | 1.69 | 2.07 | 10.4 ms | **1.87x** |
| `CandidateLean.lean` — the above, `ite` replaced by matches | 1.70 | 1.89 | 2.31 | 11.8 ms | 1.65x |

Milliseconds of kernel time per case; the judged total is `2 × (f1 + f2 + f3)`,
the plan's two cases per group. Run
[`39171426699`](https://github.com/Amey-Thakur/SAIR-LEAN-KERNEL-CHALLENGE/actions/runs/39171426699).
`CandidateRaw` measured 2.18x in run `39169669760` and 2.02x in
`39170346845`: **2.0x, reproduced three times.**

## 3. What the kernel charges for

Four things were priced, each by a file whose statement is the same shape as a
real case so that nothing is being compared against a measurement floor.

**Big multiplications are about a fifth of the cost.**
`CandidateExtraMul.lean` is `Candidate.lean` with two extra products a level
that provably contribute nothing — `(a * b - a * b)` is zero, but the kernel
cannot know that without reducing both arguments to literals, so it performs
them. At `n = 150000` that is 52 products becoming 88, a rise of **69%**, with
the recursion, the `Prod`, the `ite`, the depth, the statement and the expected
literal all identical. It cost **13%** (16.55 ms against 14.67 ms, run
`39170346845`).

So multiplication count is *not* the currency for `fib`, and this is where the
`ca-rule110` result does not transfer. The consequence is immediate: **a
Lucas-sequence formulation is not worth building.** Two products a doubling
instead of three is a 33% cut in a fifth of the cost — about 6% — against a
proof of Cassini's identity and the parity-dependent `L(2k) = L(k)^2 ∓ 2` in
truncated `Nat` subtraction.

**Operand width is nearly free.** The specialised top level computes `fib n`
instead of the pair `(fib n, fib (n+1))`, which removes two of the three
widest products in the whole computation: 45% of the bit-work by a
`max(width)^1.585` model, 1.80x at `n = 150000`. Measured against the
unspecialised pair in the same job it is worth nothing at f1 and f2. The floor
files agree from the other side: 25 products on 348-bit operands and 49 on
operands up to 52,069 bits differ by a factor of two, not of 150.

**The fuel's size is free.** `fibAux fuel n` needs `fuel` only as large as the
number of halvings, 18 at `n = 150000`, but `impl` passes `n` because `n` is
the only bound available without a logarithm and `Nat.log2` is itself
well-founded. `fibAux 24 n` and `fibAux n n` measure the same, in both
designs, in three runs. The recursion is structural and the kernel unfolds one
step a level however large the literal is.

**What is left is the per-level term machinery.** `floortiny` performs the real
product set on operands `2 ^ w - 1` written as
`Nat.sub (Nat.shiftLeft 1 w) 1`, so a statement is 1.5 KB instead of 157 KB and
cannot itself be the cost: 0.51, 0.71, 0.68, 1.77, 1.46 ms for 25, 34, 40, 46,
49 products. That is a flat **≈4 µs for every elementary `Nat` operation the
kernel reduces**, plus perhaps 0.5 ms of real GMP work at the largest size. A
level of `CandidateRaw` reduces roughly 25 such operations, of which about 10
are the arithmetic; the rest is `Prod`, `ite`, `Decidable`, the `Nat.rec` step
and the `let` instantiations.

## 4. What the 2.0x is made of, and one more negative

Two changes, in order of what they are worth:

1. **Raw `Nat.*` arithmetic, ≈1.4x.** `a * b` on `Nat` is
   `@HMul.hMul Nat Nat Nat instHMul a b`, and the kernel unfolds `instHMul`,
   `Mul.mul` and `instMulNat` before reaching `Nat.mul` and its accelerator.
   Nine operations a level each pay that chain; `Nat.mul a b` has nothing to
   unfold. The definitions use `Nat.mul` and the bridging lemmas restate them
   in `*` notation, which is definitionally the same term, so every Mathlib
   identity about `Nat.fib` applies unchanged and each bridge is `rfl`.
2. **No `WellFounded.fix`, ≈1.4x.** `Nat.binaryRec` carries
   `termination_by if n = 0 then 0 else n.log2.succ` in the pinned Mathlib, so
   it is well-founded recursion, and `Nat.log2` is well-founded too. A
   structural fuel avoids it. Writing the recursion as an explicit `Nat.rec`
   rather than leaving it to the structural-recursion compiler avoids
   `Nat.brecOn` and its `Nat.below` motive as well — `#print` confirms the
   compiler produced `Nat.brecOn` for the pattern-matching form and a plain
   `Nat.rec` for this one.

And one change that **made it worse**: `CandidateLean.lean` replaces
`if n = 0` and `if n % 2 = 1` with matches on `Nat`, expecting to save the
`Decidable` unfolding. It is 1.65x against `CandidateRaw`'s 1.87x. Matching a
`Nat` literal on `0`/`_` makes the kernel materialise it in constructor form —
a decrement and a fresh literal — where `if n = 0` goes straight to the `beq`
accelerator and never builds a constructor. The `Decidable` chain is cheaper
than the literal-to-constructor conversion it was meant to replace.

## 5. Verdict

`CandidateRaw.lean` compiles in the real problem package, reports exactly
`[propext, Classical.choice, Quot.sound]`, reduces every judged size, and is
**2.0x the starter at the judged boundary, reproduced in three runs**. On the
only available calibration — our own live 96,290,412 against the starter's
measured kernel total — that is about 48M instructions.

**Top 3 is not reachable this way, and the measurements say why.** Rank 3 needs
13.5x. The arithmetic is a fifth of the cost, so no reformulation of it can
give more than about 1.25x; width is free, so narrowing operands gives nothing;
the fuel is free; and what dominates is roughly 25 elementary kernel operations
a level at 4 µs each, of which perhaps eight could be removed by the leanest
level body that still proves — and the one attempt at that went backwards.
Every lever measured here is a factor between 1.0 and 1.4, and the product of
the ones that work is 2.0.

`Submission.lean` is left byte-identical to the live entry. Nothing is staged
where it could be sent unmeasured.
