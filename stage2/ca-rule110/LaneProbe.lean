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
  | zero => intro _ _ _ _ hin; omega
  | succ k ih =>
    intro i b hb hin
    rcases Nat.lt_or_ge i k with hlt | hge
    · -- the bit sits in an earlier lane, below everything the new term adds
      have hlow : w * i + b < w * k := by
        have h1 : w * (i + 1) ≤ w * k := Nat.mul_le_mul_left w hlt
        have h2 : w * (i + 1) = w * i + w := Nat.mul_succ w i
        omega
      rw [pack, ← ih i b hb hlt,
          ← Nat.testBit_mod_two_pow _ _ _ hlow,
          ← Nat.testBit_mod_two_pow _ _ _ hlow,
          Nat.add_mul_mod_self_left]
    · -- the bit sits in the newest lane, and the earlier ones are all below it
      have hik : i = k := by omega
      subst hik
      have hdiv : (pack w f i + f i * 2 ^ (w * i)) / 2 ^ (w * i) = f i := by
        rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos (w * i)),
            Nat.div_eq_of_lt (pack_lt w f hf i), Nat.zero_add]
      have hshift := Nat.testBit_shiftRight (i := w * i) (j := b)
        (pack w f i + f i * 2 ^ (w * i))
      rw [Nat.shiftRight_eq_div_pow, hdiv] at hshift
      rw [pack]
      exact hshift.symm

end Lane
