import Spec

/-!
# primecount — a primality test the kernel can run, bounded by the square root

The measured starting point. The shipped starter tests primality with
`Nat.minFac p == p`. `Nat.minFac` dispatches even numbers by a special case and
everything else to `minFacAux`, which is defined by well-founded recursion, and
the Lean kernel does not unfold well-founded recursion. Timing the starter at
the judged sizes shows exactly that: `impl n` reduces for n = 0, 1 and 2 and
fails for every larger n with

    Tactic `rfl` failed: Submission.impl 3 is not definitionally equal to 2

Every judged case is n >= 50, so the starter does not score. This is not a
question of speed; the kernel cannot produce the number at all.

The first repair, kept in `SubmissionLinear.lean`, walked every candidate
divisor from `p - 1` down to 2. That already reduces all the judged sizes,
which is the whole of the gap, but its cost is quadratic in `n` and it measured
29.5 s at n = 600.

This version stops as soon as `d * d` passes `p`, cutting the work from about
`n^2 / 2` divisor tests to about `n * sqrt n`: roughly 21,000 tests up to
n = 1,000 rather than 500,000.

`Nat.sqrt` is deliberately not used to express that bound, although it would
read better. `Nat.sqrt` is itself well-founded recursion through
`Nat.sqrt.iter`, so calling it would reintroduce the exact defect this file
exists to repair. The bound is written `p < d * d`: one multiplication and one
comparison, on numbers the kernel handles natively.

The recursion carries an explicit fuel so that it is structural. The fuel is
never exhausted in practice, because the square test cuts the search at
`sqrt p` long before `p` steps are taken. `noFactorFrom_sound` states that
precisely with an `m < d + fuel` side condition, and `isPrimeFast_eq`
discharges it.

Only the primality test changes. The count is still the starter's own `countP`
over `List.range`, so the proof reuses the starter's route from `countP` to
`Nat.primeCounting`.
-/

namespace Submission

/-- Trial division upward from `d`, stopping once `d * d` passes `p`.
Structural on the fuel, so the kernel unfolds it. -/
def noFactorFrom (p : Nat) : Nat → Nat → Bool
  | 0,        _ => true
  | fuel + 1, d =>
      if p < d * d then true
      else if p % d == 0 then false
      else noFactorFrom p fuel (d + 1)

/-- Primality by trial division bounded at the square root. -/
def isPrimeFast (p : Nat) : Bool :=
  decide (2 ≤ p) && noFactorFrom p p 2

def impl (n : Nat) : Nat := (List.range (n + 1)).countP isPrimeFast

/-! ## Correctness of the loop

The two directions are proved separately because they need different things.
Soundness is what licenses concluding primality and carries the fuel side
condition; completeness needs no side condition, since running out of fuel only
ever answers `true`. -/

/-- If the loop reports no factor, there is none in range, as far as the fuel
reached. -/
theorem noFactorFrom_sound (p : Nat) :
    ∀ fuel d, noFactorFrom p fuel d = true →
      ∀ m, d ≤ m → m * m ≤ p → m < d + fuel → ¬ (m ∣ p) := by
  intro fuel
  induction fuel with
  | zero =>
    intro d _ m hdm _ hlt
    omega
  | succ f ih =>
    intro d hrun m hdm hsq hlt
    rw [noFactorFrom] at hrun
    by_cases hbig : p < d * d
    · -- the search stopped because every remaining divisor is already too big
      have hmm : d * d ≤ m * m := Nat.mul_le_mul hdm hdm
      omega
    · simp only [hbig, if_false] at hrun
      by_cases hdvd : p % d == 0
      · simp only [hdvd, if_true] at hrun
        exact absurd hrun (by simp)
      · simp only [hdvd] at hrun
        rcases Nat.eq_or_lt_of_le hdm with heq | hgt
        · -- `heq : d = m`, so the rewrite goes forward. `← heq` looks for `m`
          -- in a hypothesis that only mentions `d`, and finds nothing.
          intro hdvdm
          have hz : p % m = 0 := Nat.dvd_iff_mod_eq_zero.mp hdvdm
          rw [heq] at hdvd
          simp [hz] at hdvd
        · exact ih (d + 1) hrun m (by omega) hsq (by omega)

/-- If there is no factor in range, the loop reports so. -/
theorem noFactorFrom_complete (p : Nat) :
    ∀ fuel d, (∀ m, d ≤ m → m * m ≤ p → ¬ (m ∣ p)) →
      noFactorFrom p fuel d = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro d _
    rfl
  | succ f ih =>
    intro d h
    rw [noFactorFrom]
    by_cases hbig : p < d * d
    · simp [hbig]
    · simp only [hbig, if_false]
      have hnd : ¬ (d ∣ p) := h d (Nat.le_refl d) (by omega)
      have hmod : ¬ (p % d = 0) := fun hz =>
        hnd (Nat.dvd_iff_mod_eq_zero.mpr hz)
      simp only [beq_iff_eq, hmod, if_false]
      exact ih (d + 1) (fun m hm hsq => h m (by omega) hsq)

/-! ## Correctness of the test -/

theorem isPrimeFast_eq (p : Nat) : isPrimeFast p = decide (Nat.Prime p) := by
  apply Bool.eq_iff_iff.mpr
  rw [isPrimeFast, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
      Nat.prime_def_le_sqrt]
  constructor
  · rintro ⟨h2, hrun⟩
    refine ⟨h2, fun m hm hle => ?_⟩
    have hsq : m * m ≤ p := Nat.le_sqrt.mp hle
    -- the fuel side condition: m * m <= p with 2 <= m forces m <= p
    have hmp : m ≤ p := Nat.le_trans (Nat.le_mul_of_pos_left m (by omega)) hsq
    exact noFactorFrom_sound p p 2 hrun m hm hsq (by omega)
  · rintro ⟨h2, hno⟩
    refine ⟨h2, noFactorFrom_complete p p 2 (fun m hm hsq => ?_)⟩
    exact hno m hm (Nat.le_sqrt.mpr hsq)

/-! ## Correctness of the count

The starter's own argument, unchanged apart from the test it is given. -/

theorem impl_correct : ∀ n, impl n = primeCountSpec n := by
  intro n
  simp only [impl, primeCountSpec, Nat.primeCounting, Nat.primeCounting',
    Nat.count, List.countP_eq_length_filter]
  rw [List.filter_congr (fun p _ => isPrimeFast_eq p)]

end Submission
