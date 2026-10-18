import Spec

/-!
# fib — a diagnostic, not a candidate

This file is `Candidate.lean` with **two extra big multiplications per level**
that provably contribute nothing to the answer:

    e := (a * b - a * b) + ((a + b) * (a + b) - (a + b) * (a + b))

`e` is zero, so `impl` computes exactly `Nat.fib n` and the proof is the same
proof. But the kernel cannot know that `a * b - a * b` is zero without
reducing `Nat.sub` to a literal, and it cannot do that without reducing both
of its arguments to literals, so it performs the products. Two more a level,
on operands of exactly the widths the real products have: at n = 150000 the
design goes from 52 products to 88, a rise of 69%, with the recursion, the
`Prod`, the `ite`, the depth, the statement and the expected literal all
identical.

**Why it is needed.** `stage2/fib/bulk.py`'s `calib` prices the arithmetic by
performing the same products on literal operands, and it reported 28.6
microseconds a product against the candidate's 28.7 -- which would say the
candidate is exactly at the arithmetic floor. That comparison is not safe. A
`calib` statement carries 157 KB of hex literals, and the kernel type checks
the statement before it reduces anything, so its figure may be the cost of
reading its own enormous type rather than of the multiplications in it. The
same objection sank the earlier wall-clock comparison for this problem, in the
same way: a quantity measured against a floor is not a measurement.

This design has no such confound. Its statement is `impl n % M = r`, byte for
byte the shape the real candidate is measured with, so the difference between
the two figures is the price of 36 multiplications and nothing else.

If the rise is near 69%, multiplication count is the currency and a
Lucas-sequence formulation -- two products a doubling rather than three -- is
worth about 1.4x. If the rise is near zero, the products are nearly free, the
cost is elsewhere, and reducing the count cannot help.
-/

namespace Submission

def fibAux : Nat → Nat → Nat × Nat
  | 0, _ => (0, 1)
  | fuel + 1, n =>
      if n = 0 then (0, 1)
      else
        let p := fibAux fuel (n / 2)
        let a := p.1
        let b := p.2
        let c := a * (2 * b - a)
        let e := (a * b - a * b) + ((a + b) * (a + b) - (a + b) * (a + b))
        let d := a * a + b * b + e
        if n % 2 = 1 then (d, c + d) else (c, d)

def impl (n : Nat) : Nat :=
  let p := fibAux n (n / 2)
  let a := p.1
  let b := p.2
  if n % 2 = 1 then a * a + b * b else a * (2 * b - a)

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
