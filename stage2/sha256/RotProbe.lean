import Spec

/-!
# Rotating a 32-bit word with one multiplication

The specification rotates with two shifts, an or and a mask:

    rotr32 x n = ((x >>> n) ||| (x <<< (32 - n))) &&& w32

Four operations, and a sigma is three rotations and two exclusive ors, so
fourteen. `model.py` counts the whole problem at 4,528 operations per chained
step and says where they are: replacing those rotations is worth 1.48x, while
deferring the mask across a chain of additions is worth 1.04x and folding the
padding's zero words out of the message schedule is worth 1.5%. So only the
rotation is attacked here, and the other two are left alone deliberately.

The idea. For `x < 2 ^ 32`, `x * 0x100000001` is `x + x * 2 ^ 32`, which is `x`
placed twice side by side with nothing between. Every rotation of `x` is then a
single shift of that doubled word, and because masking distributes over
exclusive or, the three rotations of a sigma share one mask at the end instead
of carrying one each. Fourteen operations becomes seven: one multiply, three
shifts, two xors, one mask.

This file is not the submission. It compiles on its own in CI so a wrong lemma
name is reported by itself, and so the live entry is never at risk while the
proof is being built.
-/

-- names this file is unsure of, reported by themselves
#check @Nat.testBit_and
#check @Nat.testBit_xor
#check @Nat.testBit_or
#check @Nat.testBit_shiftRight
#check @Nat.testBit_shiftLeft
#check @Nat.testBit_two_pow_sub_one
#check @Nat.testBit_mod_two_pow
#check @Nat.testBit_lt_two_pow
#check @Nat.eq_of_testBit_eq
#check @Nat.add_mul_mod_self_right
#check @Nat.add_mul_div_right
#check @Nat.div_eq_of_lt
#check @Nat.mod_eq_of_lt
#check @Nat.shiftRight_eq_div_pow

namespace Rot

set_option maxRecDepth 100000

/-- The specification's mask is `2 ^ 32 - 1`. -/
theorem w32_eq : w32 = 2 ^ 32 - 1 := by rfl

/-- Masking to 32 bits is reduction modulo `2 ^ 32`. -/
theorem and_w32 (x : Nat) : x &&& w32 = x % 2 ^ 32 := by
  rw [w32_eq]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
  exact Bool.and_comm _ _

/-- A value below `2 ^ 32` has no bits at or above 32. -/
theorem testBit_high {x : Nat} (hx : x < 2 ^ 32) {j : Nat} (hj : 32 ≤ j) :
    x.testBit j = false := by
  have h2 : (2 : Nat) ^ 32 ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) hj
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx h2)

/-- `x` placed twice side by side, in one multiplication. -/
def dbl (x : Nat) : Nat := x * 0x100000001

/-- The doubled word is the sum the multiplication stands for. -/
theorem dbl_eq (x : Nat) : dbl x = x + x * 2 ^ 32 := by
  rw [dbl]
  have h : (0x100000001 : Nat) = 1 + 2 ^ 32 := by rfl
  rw [h, Nat.mul_add, Nat.mul_one]

/-- The low half of the doubled word is `x` itself. -/
theorem dbl_mod (x : Nat) (hx : x < 2 ^ 32) : dbl x % 2 ^ 32 = x := by
  rw [dbl_eq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]

/-- The high half of the doubled word is `x` again. -/
theorem dbl_shift (x : Nat) (hx : x < 2 ^ 32) : dbl x >>> 32 = x := by
  rw [Nat.shiftRight_eq_div_pow, dbl_eq,
      Nat.add_mul_div_right _ _ (Nat.two_pow_pos 32), Nat.div_eq_of_lt hx,
      Nat.zero_add]

/-- Every bit of the doubled word, which is the whole content of the trick:
below 32 it is a bit of `x`, at or above 32 it is that same bit of `x` again. -/
theorem testBit_dbl {x : Nat} (hx : x < 2 ^ 32) (j : Nat) :
    (dbl x).testBit j = if j < 32 then x.testBit j else x.testBit (j - 32) := by
  by_cases hj : j < 32
  · have h := Nat.testBit_mod_two_pow (dbl x) 32 j
    rw [dbl_mod x hx] at h
    have hd : decide (j < 32) = true := by simp [hj]
    rw [hd, Bool.true_and] at h
    rw [if_pos hj, h]
  · have hk : j = 32 + (j - 32) := by omega
    have h := Nat.testBit_shiftRight (i := 32) (j := j - 32) (dbl x)
    rw [dbl_shift x hx] at h
    rw [if_neg hj, hk, ← h]

/-- A rotation is one shift of the doubled word, and one mask. -/
theorem rotr32_eq {x n : Nat} (hx : x < 2 ^ 32) (hn : 0 < n) (hn32 : n < 32) :
    rotr32 x n = (dbl x >>> n) &&& w32 := by
  rw [rotr32, and_w32, and_w32]
  apply Nat.eq_of_testBit_eq
  intro b
  rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow, Nat.testBit_or,
      Nat.testBit_shiftRight, Nat.testBit_shiftRight, Nat.testBit_shiftLeft]
  by_cases hb : b < 32
  · have hd : decide (b < 32) = true := by simp [hb]
    rw [hd, Bool.true_and, Bool.true_and, testBit_dbl hx]
    by_cases hnb : n + b < 32
    · -- the bit still lies in the low copy, so the plain shift supplies it
      have h1 : decide (32 - n ≤ b) = false := by
        have : ¬ (32 - n ≤ b) := by omega
        simp [this]
      rw [if_pos hnb, h1, Bool.false_and, Bool.or_false]
    · -- the bit has crossed into the high copy, which is the wrap
      have h1 : decide (32 - n ≤ b) = true := by
        have : 32 - n ≤ b := by omega
        simp [this]
      have h2 : x.testBit (n + b) = false := testBit_high hx (by omega)
      have h3 : b - (32 - n) = n + b - 32 := by omega
      rw [if_neg hnb, h1, Bool.true_and, h2, Bool.false_or, h3]
  · have hd : decide (b < 32) = false := by simp [hb]
    rw [hd, Bool.false_and, Bool.false_and]

/-- Masking distributes over exclusive or, which is what lets the three
rotations of a sigma share one mask instead of carrying one each. -/
theorem xor_and_w32 (a b : Nat) :
    (a &&& w32) ^^^ (b &&& w32) = (a ^^^ b) &&& w32 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_and, Nat.testBit_and, Nat.testBit_and,
      Nat.testBit_xor]
  cases hw : (w32 : Nat).testBit j <;> simp [hw]

/-! ## The four sigmas, each in seven operations instead of fourteen -/

theorem bigSigma0_eq {x : Nat} (hx : x < 2 ^ 32) :
    bigSigma0 x
      = ((dbl x >>> 2) ^^^ (dbl x >>> 13) ^^^ (dbl x >>> 22)) &&& w32 := by
  rw [bigSigma0, rotr32_eq hx (by omega) (by omega),
      rotr32_eq hx (by omega) (by omega), rotr32_eq hx (by omega) (by omega),
      xor_and_w32, xor_and_w32]

theorem bigSigma1_eq {x : Nat} (hx : x < 2 ^ 32) :
    bigSigma1 x
      = ((dbl x >>> 6) ^^^ (dbl x >>> 11) ^^^ (dbl x >>> 25)) &&& w32 := by
  rw [bigSigma1, rotr32_eq hx (by omega) (by omega),
      rotr32_eq hx (by omega) (by omega), rotr32_eq hx (by omega) (by omega),
      xor_and_w32, xor_and_w32]

/-- The small sigmas end in a plain shift rather than a rotation. It is already
below `2 ^ 32`, so masking it changes nothing and it joins the shared mask. -/
theorem shiftRight_and_w32 {x : Nat} (hx : x < 2 ^ 32) (k : Nat) :
    (x >>> k) &&& w32 = x >>> k := by
  rw [and_w32, Nat.mod_eq_of_lt]
  exact Nat.lt_of_le_of_lt (Nat.shiftRight_le x k) hx

theorem smallSigma0_eq {x : Nat} (hx : x < 2 ^ 32) :
    smallSigma0 x
      = ((dbl x >>> 7) ^^^ (dbl x >>> 18) ^^^ (x >>> 3)) &&& w32 := by
  rw [smallSigma0, rotr32_eq hx (by omega) (by omega),
      rotr32_eq hx (by omega) (by omega), ← shiftRight_and_w32 hx 3,
      xor_and_w32, xor_and_w32]

theorem smallSigma1_eq {x : Nat} (hx : x < 2 ^ 32) :
    smallSigma1 x
      = ((dbl x >>> 17) ^^^ (dbl x >>> 19) ^^^ (x >>> 10)) &&& w32 := by
  rw [smallSigma1, rotr32_eq hx (by omega) (by omega),
      rotr32_eq hx (by omega) (by omega), ← shiftRight_and_w32 hx 10,
      xor_and_w32, xor_and_w32]

end Rot
