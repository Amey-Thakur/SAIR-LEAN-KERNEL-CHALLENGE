import Spec

/-!
Which `Int` division lemmas core Lean actually provides.

polydisc has no Mathlib dependency, so only core's `Int` API is available,
and every lemma name in a proof written without a toolchain is a guess. The
first attempt guessed `Int.ediv_add_emod` and it does not exist here. This
compiles the guesses on their own so a wrong name is reported by itself
rather than buried in the real proof's errors.

`#check` prints the statement as well as resolving the name, which matters:
two of these differ in the order of the product and that decides which way
the rewrite goes.
-/

-- the division identity, in the orders it might be stated
#check @Int.emod_add_ediv
#check @Int.ediv_add_emod
#check @Int.emod_def
#check @Int.emod_emod_of_dvd

-- divisibility against a zero remainder
#check @Int.dvd_of_emod_eq_zero
#check @Int.emod_eq_zero_of_dvd
#check @Int.dvd_iff_emod_eq_zero
#check @Int.emod_eq_zero_iff_dvd

-- cancelling a division against its divisor
#check @Int.ediv_mul_cancel
#check @Int.mul_ediv_cancel'
#check @Int.ediv_mul_cancel_of_emod_eq_zero

-- the `Nat` side, for the coefficient setup
#check @Nat.div_add_mod
#check @Nat.mod_add_div

-- multiplying a list by one, for the scaling the specification always does
#check @Int.one_mul
#check @Int.mul_one

-- turning `(a == b) = true` into `a = b`, which `scaleP` needs
#check @eq_of_beq
#check @of_decide_eq_true
#check @beq_iff_eq

-- the exponent laws, if a power ever has to be rebuilt by hand
#check @Nat.pow_succ
#check @Nat.pow_zero
#check @Nat.pow_add
#check @Nat.pow_mul
#check @Nat.shiftRight_eq_div_pow
#check @Nat.shiftLeft_eq
