import Spec

/-!
# The foundation for the lane-packed initial row

`lanes.py` settles the algorithm: give every cell a lane inside one `Nat`, run
the whole 32-bit mixing hash on all 256 cells at once, then gather one bit per
lane back down. What is left is the proof.

Lanes are assembled with `+`, not `|||`. The first version of this file used
`|||`, because `Nat.testBit_or` turns a bit of the whole into a disjunction of
bits of the parts with no carry reasoning at all, which made `testBit_pack`
short. It is the wrong choice all the same: the mixing hash multiplies, and
multiplication distributes over `+` and not over `|||`. Core Lean has no
`or_eq_add_of_and_eq_zero` to convert between them, so the sum is the
definition and the no-carry argument is paid once, here, where the lane bound
`f k < 2 ^ w` does the work.

This file is not the submission. It compiles on its own in CI so a wrong
lemma name or a broken induction is reported by itself, and so the live entry
is never at risk while this is being built.
-/

-- names this file is unsure of, reported by themselves
#check @Nat.testBit_mod_two_pow
#check @Nat.div_eq_of_lt
#check @Nat.pow_add
#check @Nat.succ_mul
#check @Nat.mul_le_mul_right
#check @Nat.add_mul_mod_self_right
#check @Nat.add_mul_div_right
#check @Nat.mod_eq_of_lt
#check @Nat.eq_of_testBit_eq
#check @Nat.div_add_mod
#check @Nat.div_lt_iff_lt_mul
#check @Nat.mod_lt
#check @Nat.mul_right_comm

namespace Lane

/-- `n` lanes of width `w`, lane `k` holding `f k`. -/
def pack (w : Nat) (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => pack w f k + f k * 2 ^ (w * k)

/-- A value below `2 ^ w` has no bits at or above `w`. The core lemma gives
this only at the index `w` itself. -/
theorem testBit_eq_false_of_lt_pow {x w i : Nat} (hx : x < 2 ^ w) (hi : w ≤ i) :
    x.testBit i = false := by
  have h2 : (2 : Nat) ^ w ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) hi
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx h2)

/-- `n` lanes of width `w` occupy `w * n` bits. This is what stops a lane
carrying into its neighbour. -/
theorem pack_lt (w : Nat) (f : Nat → Nat) (hf : ∀ k, f k < 2 ^ w) :
    ∀ n, pack w f n < 2 ^ (w * n) := by
  intro n
  induction n with
  | zero => simp [pack]
  | succ k ih =>
    have hstep : w * (k + 1) = w * k + w := Nat.mul_succ w k
    have hpow : (2 : Nat) ^ (w * k + w) = 2 ^ (w * k) * 2 ^ w := Nat.pow_add 2 _ _
    have hfk : f k + 1 ≤ 2 ^ w := hf k
    have hmul : (f k + 1) * 2 ^ (w * k) ≤ 2 ^ w * 2 ^ (w * k) :=
      Nat.mul_le_mul_right _ hfk
    have hexp : (f k + 1) * 2 ^ (w * k) = f k * 2 ^ (w * k) + 2 ^ (w * k) :=
      Nat.succ_mul (f k) (2 ^ (w * k))
    have hcomm : (2 : Nat) ^ w * 2 ^ (w * k) = 2 ^ (w * k) * 2 ^ w :=
      Nat.mul_comm _ _
    rw [pack, hstep, hpow]
    omega

/-- The lemma everything else rests on: a bit inside lane `i` of the packed
number is that bit of lane `i`'s value. -/
theorem testBit_pack (w : Nat) (f : Nat → Nat) (hf : ∀ k, f k < 2 ^ w) :
    ∀ n i b, b < w → i < n →
      (pack w f n).testBit (w * i + b) = (f i).testBit b := by
  intro n
  induction n with
  | zero => intro _ _ _ hin; omega
  | succ k ih =>
    intro i b hb hin
    rcases Nat.lt_or_ge i k with hlt | hge
    · -- the bit sits in an earlier lane, below everything the new term adds
      have hlow : w * i + b < w * k := by
        have h1 : w * (i + 1) ≤ w * k := Nat.mul_le_mul_left w hlt
        have h2 : w * (i + 1) = w * i + w := Nat.mul_succ w i
        omega
      -- `testBit_mod_two_pow` states the masked read, so the new lane is
      -- removed by taking the sum modulo the top of the earlier lanes
      have hmod : (pack w f k + f k * 2 ^ (w * k)) % 2 ^ (w * k) = pack w f k := by
        rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (pack_lt w f hf k)]
      have hbit := Nat.testBit_mod_two_pow
        (pack w f k + f k * 2 ^ (w * k)) (w * k) (w * i + b)
      have hdec : decide (w * i + b < w * k) = true := by simp [hlow]
      rw [hmod, hdec, Bool.true_and] at hbit
      rw [pack, ← hbit]
      exact ih i b hb hlt
    · -- the bit sits in the newest lane, and the earlier ones are all below it
      have hik : i = k := by omega
      subst hik
      have hdiv : (pack w f i + f i * 2 ^ (w * i)) / 2 ^ (w * i) = f i := by
        rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos (w * i)),
            Nat.div_eq_of_lt (pack_lt w f hf i), Nat.zero_add]
      have hshift := Nat.testBit_shiftRight (i := w * i) (j := b)
        (pack w f i + f i * 2 ^ (w * i))
      rw [Nat.shiftRight_eq_div_pow, hdiv] at hshift
      rw [pack]
      exact hshift.symm

/-! ## The lane algebra

Two shapes of lemma, and the split between them is the whole design.

`*` and `+` mix bits between positions, so they are handled at the level of
the packing itself, where distributivity does the work and no bound on the
lanes is needed. `^^^`, `&&&` and `>>>` do not mix bits, so they are handled
one bit at a time by the core `testBit` lemmas and need nothing new here.
`testBit_pack` above is the hinge between the two views.
-/

/-- A scalar multiplies every lane, with no side condition whatever. The
lanes are a sum precisely so that this is true: `*` distributes over `+`,
and Core Lean has no lemma that would let it distribute over `|||`. -/
theorem pack_mul (w : Nat) (f : Nat → Nat) (c : Nat) :
    ∀ n, pack w f n * c = pack w (fun k => f k * c) n := by
  intro n
  induction n with
  | zero => simp [pack]
  | succ k ih =>
    show (pack w f k + f k * 2 ^ (w * k)) * c
        = pack w (fun j => f j * c) k + f k * c * 2 ^ (w * k)
    rw [Nat.add_mul, ih, Nat.mul_right_comm]

/-- Two packings add lane by lane, again with no side condition. The sum of
two lanes may well overflow `2 ^ w`; this says only that the arithmetic is
faithful, and a bound is reimposed where one is needed. -/
theorem pack_add (w : Nat) (f g : Nat → Nat) :
    ∀ n, pack w f n + pack w g n = pack w (fun k => f k + g k) n := by
  intro n
  induction n with
  | zero => simp [pack]
  | succ k ih =>
    show pack w f k + f k * 2 ^ (w * k) + (pack w g k + g k * 2 ^ (w * k))
        = pack w (fun j => f j + g j) k + (f k + g k) * 2 ^ (w * k)
    rw [← ih, Nat.add_mul]
    omega

/-- Extensionality in the lane view: two numbers that fit in `n` lanes are
equal as soon as their lanes agree. This is what turns a value built by
shifting and masking back into a packing, which is the only way `pack_mul`
can then be applied to it. -/
theorem eq_of_lanes {w n x y : Nat} (hw : 0 < w)
    (hx : x < 2 ^ (w * n)) (hy : y < 2 ^ (w * n))
    (h : ∀ i b, i < n → b < w →
      x.testBit (w * i + b) = y.testBit (w * i + b)) :
    x = y := by
  apply Nat.eq_of_testBit_eq
  intro j
  rcases Nat.lt_or_ge j (w * n) with hj | hj
  · -- inside the lanes: name the lane and the offset by division
    have hd : w * (j / w) + j % w = j := by
      rw [Nat.mul_comm]
      exact Nat.div_add_mod j w
    have hb : j % w < w := Nat.mod_lt _ hw
    have hi : j / w < n := by
      rw [Nat.div_lt_iff_lt_mul hw, Nat.mul_comm]
      exact hj
    rw [← hd]
    exact h _ _ hi hb
  · -- above the lanes: both sides are zero, by the bound each one carries
    rw [testBit_eq_false_of_lt_pow hx hj, testBit_eq_false_of_lt_pow hy hj]

end Lane
