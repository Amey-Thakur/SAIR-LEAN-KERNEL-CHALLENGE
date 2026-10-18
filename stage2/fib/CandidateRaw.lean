import Spec

/-!
# fib — the same algorithm, with nothing between it and the kernel

Measured on 18 October 2026, with Lean's profiler reporting the kernel's own
`type checking` phase rather than the whole process:

* the starter costs the kernel 2.10 ms a case at the hardest judged size;
* `Candidate.lean`, structural and specialised, costs 1.49 ms;
* and performing *only* the big multiplications that `Candidate.lean` performs,
  on literal operands, with no recursion, no `Prod` and no `ite` anywhere in
  the file, costs **28.6 microseconds a product**, against the candidate's
  28.7. The candidate is already at that floor: the recursion around the
  arithmetic is free, and the whole cost is the per-product one.

So the question is what a product costs, and the answer cannot be the
multiplication itself: the floor is flat in operand width, 28.6 microseconds
whether the operands are 348 bits or 52,069.

This file removes the one thing left between a product and the kernel's own
arithmetic. `a * b` on `Nat` is `@HMul.hMul Nat Nat Nat instHMul a b`, and the
kernel unfolds `instHMul`, `Mul.mul` and `instMulNat` before it reaches
`Nat.mul` and its own accelerator. Written as `Nat.mul a b` there is nothing
to unfold. The same for `Nat.add`, `Nat.sub`, `Nat.div` and `Nat.mod`: eight
arithmetic operations a level, each saving its instance chain.

The recursion is also written as an explicit `Nat.rec` rather than left to the
structural-recursion compiler, which produced `Nat.brecOn` with a `Nat.below`
motive. `Nat.rec` reduces by one iota step a level with no `below` structure
at all.

Everything that is proved here is proved by `rfl` first and Mathlib second: the
definitions use `Nat.mul` and the bridging lemmas state the same thing in `*`
notation, which is definitionally the same term, so every Mathlib identity
about `Nat.fib` applies unchanged.

No precomputed answers: `impl` computes from `n` alone, with no table and no
input-dependent branch carrying a value.
-/

namespace Submission

/-- One doubling level, from the pair at `n / 2` to the pair at `n`. -/
def level (p : Nat × Nat) (n : Nat) : Nat × Nat :=
  let a := p.1
  let b := p.2
  let c := Nat.mul a (Nat.sub (Nat.mul 2 b) a)
  let d := Nat.add (Nat.mul a a) (Nat.mul b b)
  if Nat.mod n 2 = 1 then (d, Nat.add c d) else (c, d)

/-- The top of the recursion, where only `fib n` is wanted. One product for an
even `n`, two squarings for an odd one, rather than the three a pair costs. -/
def top (p : Nat × Nat) (n : Nat) : Nat :=
  let a := p.1
  let b := p.2
  if Nat.mod n 2 = 1 then Nat.add (Nat.mul a a) (Nat.mul b b)
  else Nat.mul a (Nat.sub (Nat.mul 2 b) a)

/-- The body of one level of the recursion, with the recursive call passed in. -/
def step (ih : Nat → Nat × Nat) (n : Nat) : Nat × Nat :=
  if n = 0 then (0, 1) else level (ih (Nat.div n 2)) n

/-- `(fib n, fib (n+1))` for every `n ≤ fuel`, by explicit `Nat.rec`: one iota
step a level, and the index halves every level, so the depth reached is the bit
length of `n` however large the fuel is. -/
def fibAux : Nat → Nat → Nat × Nat :=
  Nat.rec (motive := fun _ => Nat → Nat × Nat) (fun _ => (0, 1))
    (fun _ ih => step ih)

def impl (n : Nat) : Nat := top (fibAux n (Nat.div n 2)) n

/-! ### The definitions, restated in notation. Each one is `rfl`. -/

theorem level_eq (a b n : Nat) :
    level (a, b) n =
      (if n % 2 = 1 then (a * a + b * b, a * (2 * b - a) + (a * a + b * b))
       else (a * (2 * b - a), a * a + b * b)) := rfl

theorem top_eq (a b n : Nat) :
    top (a, b) n = (if n % 2 = 1 then a * a + b * b else a * (2 * b - a)) :=
  rfl

theorem step_eq (ih : Nat → Nat × Nat) (n : Nat) :
    step ih n = if n = 0 then (0, 1) else level (ih (n / 2)) n := rfl

theorem fibAux_succ (f : Nat) : fibAux (f + 1) = step (fibAux f) := rfl

theorem impl_eq (n : Nat) : impl n = top (fibAux n (n / 2)) n := rfl

/-! ### Correctness -/

theorem fibAux_eq : ∀ fuel n, n ≤ fuel →
    fibAux fuel n = (Nat.fib n, Nat.fib (n + 1)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro n hn
    have h : n = 0 := Nat.le_zero.mp hn
    subst h
    rfl
  | succ f ih =>
    intro n hn
    rw [fibAux_succ, step_eq]
    by_cases h0 : n = 0
    · subst h0
      rfl
    · rw [if_neg h0, ih (n / 2) (by omega), level_eq]
      set k := n / 2 with hkdef
      by_cases hodd : n % 2 = 1
      · rw [if_pos hodd]
        have hn2 : n = 2 * k + 1 := by omega
        rw [hn2]
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
      · rw [if_neg hodd]
        have hn2 : n = 2 * k := by omega
        rw [hn2]
        have h1 : Nat.fib (2 * k)
            = Nat.fib k * (2 * Nat.fib (k + 1) - Nat.fib k) :=
          Nat.fib_two_mul k
        have h2 : Nat.fib (2 * k + 1) = Nat.fib k * Nat.fib k
            + Nat.fib (k + 1) * Nat.fib (k + 1) := by
          rw [Nat.fib_two_mul_add_one]; ring
        simp [h1, h2]

theorem impl_correct : ∀ n, impl n = Nat.fib n := by
  intro n
  rw [impl_eq, fibAux_eq n (n / 2) (Nat.div_le_self n 2), top_eq]
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
