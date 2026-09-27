import Spec

/-!
# Lemma inventory probe for `permanent`

The guard in the specification is `entry = 0 || used.testBit j`, where the left
half is a Prop and the right a Bool, so Lean inserts a `decide`. Every failed
attempt at the correspondence proof so far has been about that coercion: a
`have` stating the guard in source syntax does not match the elaborated goal,
and `simp [hz]` on the isolated `if` leaves goals.

So this settles which names exist for collapsing `decide` under a hypothesis,
before another proof is written against guesses.
-/

section DecideCollapse

#check @decide_eq_true_eq
#check @decide_eq_false_iff_not
#check @Bool.false_or
#check @Bool.true_or
#check @Bool.or_eq_true

-- the two directions the proof needs, as executable checks rather than names
example (p : Prop) [Decidable p] (h : p) : decide p = true := by simp [h]
example (p : Prop) [Decidable p] (h : ¬ p) : decide p = false := by simp [h]

-- and the guard itself, in both branches, in the shape the goal has
example (e : Nat) (b : Bool) (h : e = 0) :
    (decide (e = 0) || b) = true := by simp [h]
example (e : Nat) (b : Bool) (h : ¬ (e = 0)) :
    (decide (e = 0) || b) = b := by simp [h]

-- whether an `if` on that guard collapses the same way
example (e acc x : Nat) (b : Bool) (h : e = 0) :
    (if e = 0 || b then acc else x) = acc := by simp [h]
example (e acc x : Nat) (b : Bool) (h : ¬ (e = 0)) :
    (if e = 0 || b then acc else x) = (if b then acc else x) := by simp [h]

end DecideCollapse

section ListShape

#check @List.filterMap_cons_none
#check @List.filterMap_cons_some
#check @List.foldl_cons

end ListShape
