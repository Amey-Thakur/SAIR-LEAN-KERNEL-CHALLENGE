import Spec

/-!
# mertens — step 1 of 3, the `minFac` bridge

The measured starting point: the shipped starter reduces none of the five
judged sizes. `mertensSpec` sums Mathlib's `ArithmeticFunction.moebius`, which
is defined through `Squarefree` and the prime factorisation; both reach
`Nat.minFac`, which is well-founded recursion the kernel cannot unfold. A probe
confirmed the diagnosis rather than assuming it: `decide` cannot settle
`ArithmeticFunction.moebius 6 = 1`, so the blocker is at moebius itself and not
in the summation around it.

The repair has to go one layer deeper than `primecount`, where replacing a
single predicate was enough. Here the whole factorisation is unreducible, so
the plan is:

  1. a structural `minFacFast`, proved equal to `Nat.minFac`        <- this file
  2. a structural `factorsFast`, proved equal to `Nat.primeFactorsList`
  3. moebius from that, through `moebius_apply_of_squarefree`,
     `moebius_eq_zero_of_not_squarefree` and `cardFactors_apply`

Step 1 is the crux. `Nat.minFac_eq` states
`n.minFac = if 2 ∣ n then 2 else n.minFacAux 3`, so replacing `minFacAux` with
a structural equal replaces `minFac`, and Mathlib's entire factorisation API
then applies to the replacement for free.

`impl` and `impl_correct` are still the starter's, so this file remains a valid
submission while the machinery is built up. It is not yet an improvement, and
is not submitted in this state.
-/

namespace Submission

/-! ## A structural `minFacAux`

`Nat.minFacAux` recurses on `sqrt n + 2 - k`, which is well founded and so
opaque to the kernel. The same walk with an explicit fuel is structural. The
fuel is never exhausted in practice because the `n < k * k` test stops the
search at the square root; `minFacAuxFast_eq` states exactly how much fuel is
enough. -/

def minFacAuxFast (n : Nat) : Nat → Nat → Nat
  | 0,        _ => n
  | fuel + 1, k =>
      if n < k * k then n
      else if n % k == 0 then k
      else minFacAuxFast n fuel (k + 2)

def minFacFast (n : Nat) : Nat :=
  if n % 2 == 0 then 2 else minFacAuxFast n n 3

/-- The fuel is enough exactly when the walk would reach past the square root
before running out: `k + 2 * fuel` is where the walk stops. -/
theorem minFacAuxFast_eq (n : Nat) :
    ∀ fuel k, n < (k + 2 * fuel) * (k + 2 * fuel) →
      minFacAuxFast n fuel k = Nat.minFacAux n k := by
  intro fuel
  induction fuel with
  | zero =>
    intro k hk
    simp only [Nat.mul_zero, Nat.add_zero] at hk
    rw [minFacAuxFast, Nat.minFacAux]
    simp [hk]
  | succ f ih =>
    intro k hk
    rw [minFacAuxFast, Nat.minFacAux]
    by_cases hlt : n < k * k
    · simp [hlt]
    · simp only [hlt, if_false]
      by_cases hdvd : n % k == 0
      · have : k ∣ n := Nat.dvd_iff_mod_eq_zero.mpr (by simpa using hdvd)
        simp [hdvd, this]
      · have hnd : ¬ (k ∣ n) := by
          intro h
          exact absurd (Nat.dvd_iff_mod_eq_zero.mp h) (by simpa using hdvd)
        simp only [hdvd, if_false, hnd]
        refine ih (k + 2) ?_
        have : k + 2 + 2 * f = k + 2 * (f + 1) := by omega
        rw [this]
        exact hk

theorem minFacFast_eq (n : Nat) : minFacFast n = Nat.minFac n := by
  rw [minFacFast, Nat.minFac_eq]
  by_cases h2 : n % 2 == 0
  · have : 2 ∣ n := Nat.dvd_iff_mod_eq_zero.mpr (by simpa using h2)
    simp [h2, this]
  · have hnd : ¬ (2 ∣ n) := by
      intro h
      exact absurd (Nat.dvd_iff_mod_eq_zero.mp h) (by simpa using h2)
    simp only [h2, if_false, hnd]
    refine minFacAuxFast_eq n n 3 ?_
    -- 3 + 2n squared is comfortably past n for every n
    have : n < (3 + 2 * n) := by omega
    calc n < 3 + 2 * n := this
      _ ≤ (3 + 2 * n) * (3 + 2 * n) := Nat.le_mul_of_pos_left _ (by omega)

/-! ## Step 2: a structural factorisation

`Nat.primeFactorsList` recurses on `n / minFac n`, which is well founded. With
`minFacFast_eq` in hand the same walk can be written with a fuel, and the two
agree as long as the fuel lasts. Each step at least halves `n`, so `n` itself
is far more fuel than needed. -/

def factorsFast : Nat → Nat → List Nat
  | 0,        _ => []
  | fuel + 1, n =>
      if n < 2 then []
      else
        let p := minFacFast n
        p :: factorsFast fuel (n / p)

theorem factorsFast_eq :
    ∀ fuel n, n ≤ fuel → factorsFast fuel n = Nat.primeFactorsList n := by
  intro fuel
  induction fuel with
  | zero =>
    intro n hn
    have hn0 : n = 0 := by omega
    subst hn0
    -- `Nat.primeFactorsList 0` is well-founded recursion and does not reduce
    -- definitionally, so `rfl` cannot see through it; the equation lemma can.
    rw [Nat.primeFactorsList_zero]
    rfl
  | succ f ih =>
    intro n hn
    rw [factorsFast]
    by_cases hsmall : n < 2
    · -- `if_neg`/`if_pos`, not `if_false`: the condition is `n < 2`, not `False`
      rw [if_pos hsmall]
      have : n = 0 ∨ n = 1 := by omega
      rcases this with h | h <;> subst h
      · exact (Nat.primeFactorsList_zero).symm
      · exact (Nat.primeFactorsList_one).symm
    · rw [if_neg hsmall]
      have h2 : 2 ≤ n := by omega
      have hne1 : n ≠ 1 := by omega
      have hp : Nat.Prime (Nat.minFac n) := Nat.minFac_prime hne1
      have hp2 : 2 ≤ Nat.minFac n := hp.two_le
      have hpos : 0 < n := by omega
      -- the tail argument shrinks, which is what makes the fuel enough
      have hdiv : n / Nat.minFac n ≤ f := by
        have : n / Nat.minFac n ≤ n / 2 := Nat.div_le_div_left hp2 (by omega)
        omega
      rw [minFacFast_eq]
      match n, h2 with
      | (k + 2), _ =>
        rw [Nat.primeFactorsList]
        exact congrArg _ (ih _ (by rw [minFacFast_eq] at hdiv ⊢; exact hdiv))

/-! ## Step 3: moebius, and the sum

With a reducible factorisation, Mathlib's own characterisation of moebius
applies directly: zero when the argument is not squarefree, and the sign of the
factor count when it is. -/

def muFast (n : Nat) : Int :=
  if n = 0 then 0
  else
    let fs := factorsFast n n
    if fs.Nodup then (-1) ^ fs.length else 0

theorem muFast_eq (n : Nat) :
    muFast n = (ArithmeticFunction.moebius n : Int) := by
  rw [muFast]
  by_cases hz : n = 0
  · subst hz
    simp
  · simp only [hz, if_false]
    have hfs : factorsFast n n = Nat.primeFactorsList n :=
      factorsFast_eq n n (Nat.le_refl n)
    rw [hfs]
    by_cases hnd : (Nat.primeFactorsList n).Nodup
    · have hsq : Squarefree n :=
        (Nat.squarefree_iff_nodup_primeFactorsList hz).mpr hnd
      rw [if_pos hnd, ArithmeticFunction.moebius_apply_of_squarefree hsq,
          ArithmeticFunction.cardFactors_apply]
    · have hsq : ¬ Squarefree n := fun h =>
        hnd ((Nat.squarefree_iff_nodup_primeFactorsList hz).mp h)
      rw [if_neg hnd, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]

/-- The Mertens sum, accumulated structurally. -/
def sumMu : Nat → Int
  | 0     => muFast 0
  | k + 1 => sumMu k + muFast (k + 1)

def impl (n : Nat) : Int := sumMu n

theorem impl_correct : ∀ n, impl n = mertensSpec n := by
  intro n
  show sumMu n = mertensSpec n
  induction n with
  | zero =>
    show muFast 0 = mertensSpec 0
    rw [muFast_eq, mertensSpec]
    simp
  | succ k ih =>
    -- peel one term off the spec's own sum rather than rewriting it twice
    have hstep : mertensSpec (k + 1)
        = mertensSpec k + (ArithmeticFunction.moebius (k + 1) : Int) := by
      rw [mertensSpec, mertensSpec, Finset.sum_range_succ]
    show sumMu k + muFast (k + 1) = mertensSpec (k + 1)
    rw [hstep, ih, muFast_eq]

end Submission
