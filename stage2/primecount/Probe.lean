import Spec

/-!
# Lemma inventory probe for `primecount`

The measured starting point: the shipped starter reduces `impl n` for
n = 0, 1 and 2 and fails for every larger n, because `Nat.minFac` is defined by
well-founded recursion through `minFacAux` and the kernel cannot unfold it.
Every judged case is n >= 50, so the starter scores nothing.

The replacement is trial division with an explicit fuel, which is structural
and therefore reducible. This file checks the names that proof will need,
before the proof is written against guesses.
-/

section PrimalityCharacterisations

-- The characterisation the trial-division bound rests on: a composite has a
-- divisor no larger than its square root.
#check @Nat.prime_def_le_sqrt
#check @Nat.prime_def_lt'
#check @Nat.prime_def_lt

-- Converting `m <= sqrt p` into `m * m <= p`, which is what the loop tests.
#check @Nat.le_sqrt
#check @Nat.le_sqrt'
#check @Nat.sqrt_lt
#check @Nat.sqrt_lt'

-- Divisibility as a decidable test, since the loop works with `p % d == 0`.
#check @Nat.dvd_iff_mod_eq_zero
#check @Nat.mod_eq_zero_iff_dvd

end PrimalityCharacterisations

section CountingShape

-- The starter's own route from countP to Nat.primeCounting. Reusing it means
-- the only new obligation is that the fast test agrees with Nat.Prime.
#check @Nat.primeCounting
#check @Nat.primeCounting'
#check @Nat.count
#check @List.countP_eq_length_filter
#check @List.filter_congr
#check @List.countP_congr

end CountingShape

section BoolAndDecide

#check @Bool.eq_iff_iff
#check @decide_eq_true_eq
#check @Bool.and_eq_true
#check @Bool.not_eq_true

end BoolAndDecide

section Behaviour

-- Confirm the starter's own definitions really are what the measurement said.
-- `Nat.minFac 3` is the first value that needs minFacAux; if this `decide`
-- succeeds the diagnosis is wrong and the starter is merely slow.
example : Nat.minFac 2 = 2 := by rfl

-- The specification's shape, to confirm what impl must equal.
#check @primeCountSpec
example : primeCountSpec 10 = Nat.primeCounting 10 := by rfl

end Behaviour
