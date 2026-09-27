import Spec

/-!
# primecount — a primality test the kernel can actually run

The measured starting point. The shipped starter tests primality with
`Nat.minFac p == p`. `Nat.minFac` dispatches even numbers by a special case
and everything else to `minFacAux`, which is defined by well-founded
recursion, and the Lean kernel does not unfold well-founded recursion. Timing
the starter at the judged sizes shows exactly that shape: `impl n` reduces for
n = 0, 1 and 2, and fails for every larger n with

    Tactic `rfl` failed: Submission.impl 3 is not definitionally equal to 2

Every judged case is n >= 50, so the starter does not score. This is not a
problem of speed; the kernel cannot produce the number at all.

The replacement uses structural recursion, which the kernel unfolds happily.
`noFactorUpto p k` walks the candidate divisors downward from `k`, so it
recurses on a constructor rather than through a termination proof.

`Nat.sqrt` is deliberately not used, although it would cut the work from
`O(p)` to `O(sqrt p)` per number: `Nat.sqrt` is itself well-founded recursion
through `Nat.sqrt.iter`, so it would reintroduce the exact defect being fixed.
Trial division to `p - 1` costs about 500,000 kernel steps for the whole range
up to 1,000, which the measurement can confirm is affordable. If it is not,
the answer is a structural square-root bound, not `Nat.sqrt`.

Only the primality test changes. The count is still the starter's own
`countP` over `List.range`, so the proof reuses the starter's route from
`countP` to `Nat.primeCounting` and the one new obligation is that this test
agrees with `Nat.Prime`.
-/

namespace Submission

/-- `noFactorUpto p k` is true when no `d` with `2 ≤ d ≤ k` divides `p`.

The recursion steps `k + 1` to `k`, so it is plain structural recursion: the
kernel unfolds it, and `induction k` applies to it directly. A version
matching on `k + 2` would need a functional induction principle for no gain.
Divisors below 2 are skipped by the guard rather than by the pattern. -/
def noFactorUpto (p : Nat) : Nat → Bool
  | 0     => true
  | k + 1 => (decide (k + 1 < 2) || (p % (k + 1) != 0)) && noFactorUpto p k

/-- Primality by trial division. The bound is `p - 1` rather than `p`, because
`p` divides itself. -/
def isPrimeFast (p : Nat) : Bool :=
  decide (2 ≤ p) && noFactorUpto p (p - 1)

def impl (n : Nat) : Nat := (List.range (n + 1)).countP isPrimeFast

/-! ## Correctness of the test -/

/-- What the loop means: exactly the absence of a divisor in `[2, k]`. -/
theorem noFactorUpto_iff (p : Nat) (k : Nat) :
    noFactorUpto p k = true ↔ ∀ m, 2 ≤ m → m ≤ k → ¬ (m ∣ p) := by
  induction k with
  | zero =>
    simp only [noFactorUpto]
    constructor
    · intro _ m hm hle
      omega
    · intro _
      rfl
  | succ k ih =>
    rw [noFactorUpto, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨hguard, hrest⟩ m hm hle
      rcases Nat.lt_or_ge m (k + 1) with h | h
      · exact hrest m hm (by omega)
      · have hmk : m = k + 1 := by omega
        subst hmk
        intro hdvd
        have hmod : p % m = 0 := (Nat.dvd_iff_mod_eq_zero m p (by omega)).mp hdvd
        simp only [Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hguard
        rcases hguard with hlt | hne
        · omega
        · exact hne hmod
    · intro h
      refine ⟨?_, fun m hm hle => h m hm (by omega)⟩
      simp only [Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
      rcases Nat.lt_or_ge (k + 1) 2 with hsmall | hbig
      · exact Or.inl hsmall
      · refine Or.inr ?_
        intro hmod
        exact h (k + 1) hbig (by omega)
          ((Nat.dvd_iff_mod_eq_zero (k + 1) p (by omega)).mpr hmod)

theorem isPrimeFast_eq (p : Nat) : isPrimeFast p = decide (Nat.Prime p) := by
  apply Bool.eq_iff_iff.mpr
  rw [isPrimeFast, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq,
      noFactorUpto_iff, Nat.prime_def_lt']
  constructor
  · rintro ⟨h2, hno⟩
    exact ⟨h2, fun m hm hlt => hno m hm (by omega)⟩
  · rintro ⟨h2, hno⟩
    exact ⟨h2, fun m hm hle => hno m hm (by omega)⟩

/-! ## Correctness of the count

The starter's own argument, unchanged apart from the test it is given. -/

theorem impl_correct : ∀ n, impl n = primeCountSpec n := by
  intro n
  simp only [impl, primeCountSpec, Nat.primeCounting, Nat.primeCounting',
    Nat.count, List.countP_eq_length_filter]
  rw [List.filter_congr (fun p _ => isPrimeFast_eq p)]

end Submission
