import Spec

/-!
# fib — fast doubling that stops one component short

This is `SubmissionFastDouble.lean` with one change, and the change is the only
thing in this file worth measuring: **the top of the recursion computes `fib n`
instead of the pair `(fib n, fib (n + 1))`.**

Fast doubling carries a pair because the step needs both components. The answer
does not. `impl n` therefore asks the recursion for the pair at `n / 2` and
spends one product on the component it was asked for:

    n = 2k      fib n = fib k * (2 * fib (k+1) - fib k)      one product
    n = 2k + 1  fib n = fib k ^ 2 + fib (k+1) ^ 2            two squarings

The pair recurrence spends three products at every level, and the widths
double with each one, so the last level is the majority of all the arithmetic
in the computation. Dropping two of its three products removes about 45% of the
bit-work: counting every product as `max(width)^1.585` and charging a squaring
as a full multiplication, `n = 150000` falls from 134.6 to 74.8 width-units,
**1.80x**, and an odd `n` such as 150001 falls to 104.7, 1.29x. Both are
measured by `stage2/fib/bulk.py`'s model and checked against the specification's
own recurrence at every `n` below 600 before any of this was written in Lean.

Everything else is as before: every product is written as a product rather than
through `HPow`, and the recursion is structural in an explicit fuel so the
kernel unfolds one definition a level instead of reducing through
`WellFounded.fix`. `Nat.binaryRec`, which the starter uses, carries
`termination_by n.log2.succ`, and `Nat.log2` is itself well-founded.

No precomputed answers: `impl` computes from `n` alone, with no table and no
input-dependent branch carrying a value.
-/

namespace Submission

/-- `(fib n, fib (n+1))`, by halving `n`.

`fuel` only bounds the recursion so that it is structural and the kernel will
unfold it; the index halves every level, so the depth actually reached is the
bit length of `n`. -/
def fibAux : Nat → Nat → Nat × Nat
  | 0, _ => (0, 1)
  | fuel + 1, n =>
      if n = 0 then (0, 1)
      else
        let p := fibAux fuel (n / 2)
        let a := p.1
        let b := p.2
        let c := a * (2 * b - a)
        let d := a * a + b * b
        if n % 2 = 1 then (d, c + d) else (c, d)

/-- The answer, and only the answer: the pair at `n / 2`, then one product. -/
def impl (n : Nat) : Nat :=
  let p := fibAux n (n / 2)
  let a := p.1
  let b := p.2
  if n % 2 = 1 then a * a + b * b else a * (2 * b - a)

/-- The pair recurrence, with the fuel discharged by `n ≤ fuel`. -/
theorem fibAux_eq : ∀ fuel n, n ≤ fuel →
    fibAux fuel n = (Nat.fib n, Nat.fib (n + 1)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro n hn
    have : n = 0 := Nat.le_zero.mp hn
    subst this
    simp [fibAux]
  | succ f ih =>
    intro n hn
    rw [fibAux]
    by_cases h0 : n = 0
    · subst h0; simp
    · have hpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr h0
      have hhalf : n / 2 ≤ f := by omega
      simp only [h0, if_false]
      rw [ih (n / 2) hhalf]
      set k := n / 2 with hk
      by_cases hodd : n % 2 = 1
      · have hn2 : n = 2 * k + 1 := by omega
        rw [if_pos hodd, hn2]
        have h1 : Nat.fib (2 * k + 1) = Nat.fib k * Nat.fib k
            + Nat.fib (k + 1) * Nat.fib (k + 1) := by
          rw [Nat.fib_two_mul_add_one]; ring
        have h2 : Nat.fib (2 * k + 1 + 1)
            = Nat.fib k * (2 * Nat.fib (k + 1) - Nat.fib k)
              + (Nat.fib k * Nat.fib k
                 + Nat.fib (k + 1) * Nat.fib (k + 1)) := by
          rw [show 2 * k + 1 + 1 = 2 * k + 2 from rfl, Nat.fib_add_two,
              Nat.fib_two_mul, h1]
        simp [h1, h2]
      · have hn2 : n = 2 * k := by omega
        rw [if_neg hodd, hn2]
        have h1 : Nat.fib (2 * k)
            = Nat.fib k * (2 * Nat.fib (k + 1) - Nat.fib k) :=
          Nat.fib_two_mul k
        have h2 : Nat.fib (2 * k + 1) = Nat.fib k * Nat.fib k
            + Nat.fib (k + 1) * Nat.fib (k + 1) := by
          rw [Nat.fib_two_mul_add_one]; ring
        simp [h1, h2]

theorem impl_correct : ∀ n, impl n = Nat.fib n := by
  intro n
  have hp : fibAux n (n / 2) = (Nat.fib (n / 2), Nat.fib (n / 2 + 1)) :=
    fibAux_eq n (n / 2) (Nat.div_le_self n 2)
  show (if n % 2 = 1 then
          (fibAux n (n / 2)).1 * (fibAux n (n / 2)).1
            + (fibAux n (n / 2)).2 * (fibAux n (n / 2)).2
        else
          (fibAux n (n / 2)).1
            * (2 * (fibAux n (n / 2)).2 - (fibAux n (n / 2)).1)) = Nat.fib n
  simp only [hp]
  set k := n / 2 with hkdef
  by_cases hodd : n % 2 = 1
  · rw [if_pos hodd]
    have hn2 : n = 2 * k + 1 := by omega
    rw [hn2, Nat.fib_two_mul_add_one]
    ring
  · rw [if_neg hodd]
    have hn2 : n = 2 * k := by omega
    rw [hn2, Nat.fib_two_mul]

end Submission
