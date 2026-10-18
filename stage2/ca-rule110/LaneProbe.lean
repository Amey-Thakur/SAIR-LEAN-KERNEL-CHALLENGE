import Spec

/-!
# The foundation for the lane-packed initial row

`lanes.py` settles the algorithm: give every cell a lane inside one `Nat`, run
the whole 32-bit mixing hash on all 256 cells at once, then gather one bit per
lane back down. What is left is the proof, and all of it rests on one lemma:
reading a bit of a packed number gives the corresponding bit of the lane it
falls in.

Lanes are assembled with `|||` rather than `+` deliberately. The values are
disjoint either way, but `Nat.testBit_or` turns a bit of the whole into a
disjunction of bits of the parts with no carry reasoning at all, while `+`
would need a carry argument for the same fact. Core Lean has no
`or_eq_add_of_and_eq_zero`, so `+` would mean proving that too.

This file is not the submission. It compiles on its own in CI so that a wrong
lemma name or a broken induction is reported by itself rather than buried in
the real proof, and so that the live entry is never at risk while this is
being built.
-/

namespace Lane

/-- `n` lanes of width `w`, lane `k` holding `f k`. -/
def pack (w : Nat) (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => pack w f k ||| (f k <<< (w * k))

/-- A value below `2 ^ w` has no bits at or above `w`. The core lemma gives
this only at the index `w` itself. -/
theorem testBit_eq_false_of_lt_pow {x w i : Nat} (hx : x < 2 ^ w) (hi : w ≤ i) :
    x.testBit i = false := by
  have h2 : (2 : Nat) ^ w ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) hi
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx h2)

/-- Nothing is packed at or above the top of the last lane. -/
theorem testBit_pack_high (w : Nat) (f : Nat → Nat)
    (hf : ∀ k, f k < 2 ^ w) :
    ∀ n j, w * n ≤ j → (pack w f n).testBit j = false := by
  intro n
  induction n with
  | zero => intro j _; simp [pack]
  | succ k ih =>
    intro j hj
    have hwk : w * k ≤ j := by
      have : w * k ≤ w * (k + 1) := Nat.mul_le_mul_left w (by omega)
      omega
    rw [pack, Nat.testBit_or, ih j hwk, Nat.testBit_shiftLeft]
    have hge : w ≤ j - w * k := by
      have : w * (k + 1) = w * k + w := Nat.mul_succ w k
      omega
    rw [testBit_eq_false_of_lt_pow (hf k) hge]
    simp

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
    rw [pack, Nat.testBit_or, Nat.testBit_shiftLeft]
    rcases Nat.lt_or_ge i k with hlt | hge
    · -- the bit is in an earlier lane, so the newest lane contributes nothing
      rw [ih i b hb hlt]
      have : w * i + b < w * k := by
        have h1 : w * (i + 1) ≤ w * k := Nat.mul_le_mul_left w hlt
        have h2 : w * (i + 1) = w * i + w := Nat.mul_succ w i
        omega
      simp [Nat.not_le_of_lt this]
    · -- the bit is in the newest lane, so everything before it is below
      have hik : i = k := by omega
      subst hik
      rw [testBit_pack_high w f hf i (w * i + b) (by omega)]
      have hle : w * i ≤ w * i + b := by omega
      simp [hle]

end Lane
