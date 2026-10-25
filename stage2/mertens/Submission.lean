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

/-! ### The same walk, with nothing between it and the kernel

`k * k` on `Nat` elaborates to `@HMul.hMul Nat Nat Nat instHMul k k`, and the
kernel unfolds `instHMul`, `Mul.mul` and `instMulNat` before it reaches
`Nat.mul` and its own accelerator; the same holds for `%` and `+`. Three such
operations run on every iteration of this walk, and the walk is the innermost
loop of the whole problem: once per trial divisor, per factorisation, per `n`.

The recursion is also written as an explicit `Nat.rec` rather than left to the
equation compiler, which produces `Nat.brecOn` with a `Nat.below` motive.

Both changes were measured on `fib` in this repository on 18 October 2026, at
about 1.4x each, on the judged metric rather than on wall clock. Neither
changes the walk: `minFacAuxRaw_eq` proves the two equal, so every lemma above
is reused untouched. -/

/-- Bridging the notation to the kernel's own operations. Each is `rfl`, but a
rewrite needs them stated: `rw` finishes with `rfl` at *reducible*
transparency, which cannot see through the instance chain. -/
theorem mul_def (a b : Nat) : a * b = Nat.mul a b := rfl

theorem mod_def (a b : Nat) : a % b = Nat.mod a b := rfl

theorem add_def (a b : Nat) : a + b = Nat.add a b := rfl

/-- One step of the walk, with the recursive call passed in. -/
def mfBody (n : Nat) (ih : Nat → Nat) (k : Nat) : Nat :=
  if n < Nat.mul k k then n
  else if Nat.mod n k == 0 then k
  else ih (Nat.add k 2)

/-- The walk by explicit `Nat.rec`: one iota step a level, and no `Nat.below`
structure built around it. -/
def minFacAuxRaw (n : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => n)
    (fun _ ih => mfBody n ih)

theorem minFacAuxRaw_eq (n : Nat) :
    ∀ fuel k, minFacAuxRaw n fuel k = minFacAuxFast n fuel k := by
  intro fuel
  induction fuel with
  | zero => intro _; rfl
  | succ f ih =>
    intro k
    show mfBody n (minFacAuxRaw n f) k = minFacAuxFast n (f + 1) k
    rw [mfBody, minFacAuxFast, mul_def, mod_def, add_def, ih (Nat.add k 2)]

def minFacFast (n : Nat) : Nat :=
  if n % 2 == 0 then 2 else minFacAuxRaw n n 3

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
    rw [minFacAuxRaw_eq]
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
        -- `hdiv` is already stated with `Nat.minFac`, and the goal here is
        -- literally it; rewriting again looks for a `minFacFast` that the
        -- earlier rewrite has already removed.
        exact congrArg _ (ih _ hdiv)

/-! ## Step 3: moebius, and the sum

With a reducible factorisation, Mathlib's own characterisation of moebius
applies directly: zero when the argument is not squarefree, and the sign of the
factor count when it is. -/

/-! ### The sign, by parity rather than by a power -/

/-- `(-1 : Int) ^ k` goes through `Monoid.npow`, which performs k
multiplications. The parity of k decides the answer in one `Nat.mod`, and this
runs once for every n up to the judged size. -/
def signOf (k : Nat) : Int := if Nat.mod k 2 = 0 then 1 else -1

theorem signOf_eq (k : Nat) : signOf k = (-1 : Int) ^ k := by
  rw [signOf]
  -- the split has to be on the RAW form, because `rw` matches syntactically
  -- and the goal reads `k.mod 2`, not `k % 2`
  by_cases h : Nat.mod k 2 = 0
  · have he : Even k := Nat.even_iff.mpr h
    rw [if_pos h]
    exact he.neg_one_pow.symm
  · have h' : ¬ (k % 2 = 0) := h
    have ho : Odd k := Nat.odd_iff.mpr (by omega)
    rw [if_neg h]
    exact ho.neg_one_pow.symm

def muFast (n : Nat) : Int :=
  if n = 0 then 0
  else
    let fs := factorsFast n n
    if fs.Nodup then signOf fs.length else 0

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
      -- `signOf` only becomes reachable once this `if` is resolved
      rw [if_pos hnd, signOf_eq,
          ArithmeticFunction.moebius_apply_of_squarefree hsq,
          ArithmeticFunction.cardFactors_apply]
    · have hsq : ¬ Squarefree n := fun h =>
        hnd ((Nat.squarefree_iff_nodup_primeFactorsList hz).mp h)
      rw [if_neg hnd, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]

/-- The Mertens sum, accumulated structurally. -/
def sumMu : Nat → Int
  | 0     => muFast 0
  | k + 1 => sumMu k + muFast (k + 1)

/-! ### The outer sum, by explicit recursor

`sumMu` recurses n times and is the outermost loop of the problem, so whatever
the equation compiler adds per level is paid n times. It adds `Nat.brecOn` with
a `Nat.below` motive; `Nat.rec` reduces by one iota step with no `below`
structure at all. The accumulation is written `Int.add` for the same reason the
inner walk is written `Nat.mul`: `a + b` on `Int` elaborates through
`instHAdd`, `Add.add` and `instAddInt` first. -/

/-- `a + b` on `Int`, stated so a rewrite can cross the instance chain that
`rfl` at reducible transparency cannot see through. -/
theorem int_add_def (a b : Int) : a + b = Int.add a b := rfl

def sumMuRaw : Nat → Int :=
  Nat.rec (motive := fun _ => Int) (muFast 0)
    (fun k ih => Int.add ih (muFast (Nat.succ k)))

theorem sumMuRaw_eq : ∀ n, sumMuRaw n = sumMu n := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    show Int.add (sumMuRaw k) (muFast (Nat.succ k)) = sumMu k + muFast (k + 1)
    rw [int_add_def, ih]

def impl (n : Nat) : Int := sumMuRaw n

theorem impl_correct : ∀ n, impl n = mertensSpec n := by
  intro n
  show sumMuRaw n = mertensSpec n
  rw [sumMuRaw_eq]
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
