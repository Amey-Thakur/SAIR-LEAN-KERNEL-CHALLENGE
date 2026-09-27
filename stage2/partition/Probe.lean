import Spec

/-!
# Lemma inventory probe for `partition`

Occasioned by the live leaderboard, which ranks this entry 14th of 24 at
132,036,341 units of kernel work against a leader at 1,429,499. A cost model
that charges by operand SIZE rather than by operation count puts 78% of the
packed design's cost in one place: the reduction

    ... % (1 <<< (width n * (n + 1)))

is a division by a 2,701-bit constant, performed once per row, on an operand
that has grown to roughly twice the row width by the time it is reduced.

Two changes follow from that, and this probe is for the second.

  1. Build the constant once instead of once per row. That is a refactor with
     no new lemma and it is already made.
  2. Replace the division by a bitwise AND against `2^k - 1`, which is linear
     in the operand rather than quadratic. That needs the lemma below to
     exist, in whatever name this toolchain gives it.
  3. Reduce INSIDE the sweep rather than only at the end, so operands never
     grow past the row width. That needs the two homomorphism facts at the
     bottom.
-/

section ModVersusAnd

-- The identity the second change rests on, in the shapes it might be stated.
#check @Nat.and_two_pow_sub_one_eq_mod
#check @Nat.and_pow_two_sub_one
#check @Nat.mod_two_pow_eq_and_sub_one
#check @Nat.shiftLeft_eq
#check @Nat.testBit_mod_two_pow
#check @Nat.mod_two_pow

-- and as an executable check, which is what actually decides it
example (x k : Nat) : x % (2 ^ k) = x &&& (2 ^ k - 1) := by
  simp [Nat.and_two_pow_sub_one_eq_mod]

end ModVersusAnd

section ReduceInsideTheSweep

/- Reducing inside the sweep is sound because truncation to `2^k` commutes
with both operations the sweep performs. These are the two facts; if they are
awkward here they are still elementary, and the win is that no operand ever
grows past the row width. -/

example (a b k : Nat) : (a + b) % 2 ^ k = ((a % 2 ^ k) + (b % 2 ^ k)) % 2 ^ k := by
  simp [Nat.add_mod]

example (a s k : Nat) : (a <<< s) % 2 ^ k = ((a % 2 ^ k) <<< s) % 2 ^ k := by
  simp [Nat.shiftLeft_eq, Nat.mul_mod]

#check @Nat.add_mod
#check @Nat.mul_mod
#check @Nat.pow_succ

end ReduceInsideTheSweep

section Shapes

-- confirm the refactored definitions still reduce as the proof expects
#check @Submission.rowMod
#check @Submission.rowsPM
#check @Submission.rowsP

example (n : Nat) : Submission.rowMod n = 1 <<< (Submission.width n * (n + 1)) := by
  rfl

end Shapes
