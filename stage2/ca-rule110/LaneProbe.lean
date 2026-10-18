import Spec

/-!
Which `Nat` bit lemmas core Lean provides, for the lane-packed initial row.

`lanes.py` settles the algorithm: give every cell a 128-bit lane inside one
`Nat`, run the whole 32-bit mixing hash on all 256 cells at once, then gather
one bit per lane back down. It is 99 operations against the specification's
5,348 and it agrees with the specification on 2,014 seeds and every published
case.

What is not settled is the proof, and the proof is entirely about `Nat` bits.
This package has no Mathlib, so only core's API is available, and every lemma
name written without a toolchain is a guess. The probe is cheap and the guess
is not.

The architecture this is choosing between:

  * bitwise — state everything through `Nat.testBit` and finish with
    extensionality. Needs `Nat.eq_of_testBit_eq` and the `testBit` lemmas for
    shift, and, or and xor.
  * arithmetic — state the packing as a sum of `a i * 2 ^ (w * i)` and prove
    the multiply and the add by distributivity, falling back to bits only for
    xor and for the mask.

The second is much the easier if it is available, because the multiply is the
step that carries the lane-independence argument.
-/

-- extensionality: the whole bitwise route depends on this one
#check @Nat.eq_of_testBit_eq

-- testBit against each operation the mix uses
#check @Nat.testBit_shiftLeft
#check @Nat.testBit_shiftRight
#check @Nat.testBit_or
#check @Nat.testBit_and
#check @Nat.testBit_xor
#check @Nat.testBit_two_pow_sub_one
#check @Nat.testBit_mul_two_pow
#check @Nat.testBit_add_one

-- shifts as arithmetic, which is what lets the multiply be proved by algebra
#check @Nat.shiftLeft_eq
#check @Nat.shiftRight_eq_div_pow
#check @Nat.mul_add_lt_is_or

-- bounds, for the lane-independence argument
#check @Nat.lt_two_pow_iff
#check @Nat.testBit_lt_two_pow
#check @Nat.testBit_eq_false_of_lt
#check @Nat.two_pow_pos
#check @Nat.pow_lt_pow_right

-- masking a lane down to its live width
#check @Nat.and_two_pow_sub_one_eq_mod
#check @Nat.mod_two_pow_eq_and
#check @Nat.and_pow_two_sub_one_eq_mod

-- the or that assembles disjoint lanes, as an add
#check @Nat.or_eq_add_of_and_eq_zero
#check @Nat.add_eq_or_of_and_eq_zero
#check @Nat.land_eq_zero_iff

-- division and modulus facts the gather needs
#check @Nat.div_add_mod
#check @Nat.mul_div_cancel_left
#check @Nat.add_mul_div_left
#check @Nat.add_mul_mod_self_left
