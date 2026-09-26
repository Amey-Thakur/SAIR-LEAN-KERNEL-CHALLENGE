import Spec

/-!
# Lemma inventory probe

There is no Lean toolchain on the authoring machine, so every name used in a
proof is a guess until a build says otherwise. Guessing them inside a
250-line proof produces a wall of errors that hides which guesses were wrong;
the packed-row entry for `partition` cost sixteen rounds that way.

So this file guesses nothing silently. Each `#check` below is a lemma the
ca-rule110 proof intends to use. A wrong name fails here, by itself, with the
name in the message, and one build settles the whole inventory.

Nothing in this file is submitted. It exists only to be compiled.
-/

section BitwiseTestBit

-- Reading a bit through each bitwise operation.
#check @Nat.testBit_or
#check @Nat.testBit_and
#check @Nat.testBit_xor
#check @Nat.testBit_shiftLeft
#check @Nat.testBit_shiftRight

-- Two numbers agreeing on every bit are equal. This is the spine of the
-- correspondence proof: it turns an equation between packed rows into a
-- statement about one cell at a time.
#check @Nat.eq_of_testBit_eq

-- Bits above a number's width are zero, which is what makes the rotations
-- wrap correctly rather than leak.
#check @Nat.testBit_lt_two_pow
#check @Nat.lt_two_pow_iff_testBit_eq_false

-- The mask is 2^256 - 1, so every bit below 256 is set.
#check @Nat.testBit_two_pow_sub_one

-- Splitting testBit at zero and successor, used on the encodeRow induction.
#check @Nat.testBit_zero
#check @Nat.testBit_succ

end BitwiseTestBit

section ListFacts

-- getD through map and range, for reading a cell of a stepped row.
#check @List.getD_eq_getElem?_getD
#check @List.getElem?_map
#check @List.getElem?_range
#check @List.length_map
#check @List.length_range

end ListFacts

section SpecShape

-- The specification's own definitions, to confirm the names and shapes this
-- proof will unfold.
#check @rule110
#check @stepRow
#check @iterRow
#check @encodeRow
#check @initRowFor
#check @caSpecN
#check @caSteps
#check @caSeed
#check ruleWidth

-- The exact reduction behaviour of encodeRow on a cons, which the induction
-- in the real proof pattern-matches on.
example (b : Bool) (rest : List Bool) :
    encodeRow (b :: rest) = 2 * encodeRow rest + (if b then 1 else 0) := by
  rfl

-- And that ruleWidth really is 256, so `ruleWidth - 1` is 255 definitionally.
example : ruleWidth = 256 := by rfl
example : ruleWidth - 1 = 255 := by rfl

-- The Rule 110 table as a formula. If this fails the whole design is wrong,
-- not just the proof, so it is checked before anything is built on it.
example (l c r : Bool) : rule110 l c r = ((c || r) && !(l && c && r)) := by
  cases l <;> cases c <;> cases r <;> rfl

end SpecShape

section TacticsAvailable

-- Core-only toolchain: confirm which tactics the real proof may lean on.
example (a b : Nat) (h : a < b) : a ≤ b := by omega
example (a : Nat) : a + 0 = a := by simp
example (b : Bool) : (b && true) = b := by cases b <;> rfl
example : (2 : Nat) ^ 3 = 8 := by decide

end TacticsAvailable
