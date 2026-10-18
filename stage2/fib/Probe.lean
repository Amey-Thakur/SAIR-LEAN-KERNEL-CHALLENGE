import Submission

/-!
# fib — which names exist, and what the starter actually is

Every lemma name written without a toolchain is a guess. This file compiles the
guesses on their own so that a wrong one is reported by itself, and `#check`
prints each statement so the direction of a rewrite is known before it is used.

Two questions are asked here.

1. The identities a specialised top level needs: `fib (2k)` and `fib (2k+1)` in
   terms of `fib k` and `fib (k+1)`, and the pieces a Lucas-sequence
   formulation would need, since the pinned Mathlib has no Lucas sequence of
   its own (`Mathlib/Data/Nat/Fib/` holds only `Basic` and `Zeckendorf`) and
   `L n = 2 * fib (n+1) - fib n` would have to be defined and its identities
   proved from `Nat.fib_add`.
2. What `Nat.binaryRec` is after compilation. Its source carries
   `termination_by if n = 0 then 0 else n.log2.succ`, so the starter should
   reduce through `WellFounded.fix` with a measure of about eighteen rather
   than of `n`, and `Nat.log2` is itself well-founded. Printing it says what
   the kernel is actually handed.
-/

-- 1. The doubling identities the pinned Mathlib does carry.
#check @Nat.fib_two_mul
#check @Nat.fib_two_mul_add_one
#check @Nat.fib_two_mul_add_two
#check @Nat.fib_add
#check @Nat.fib_add_two
#check @Nat.fib_add_one
#check @Nat.fib_le_fib_succ
#check @Nat.fib_mono
#check @Nat.div_le_self
#check @if_pos
#check @if_neg

-- The starter's own pieces.
#check @Nat.fastFib
#check @Nat.fastFibAux
#check @Nat.fastFib_eq
#check @Nat.binaryRec
#check @Nat.binaryRec_eq
#check @Nat.bit

-- 2. What the kernel is asked to reduce for the starter.
#print Nat.fastFibAux
#print Nat.binaryRec
#print Nat.log2

-- The axioms the live entry rests on, for the record.
#print axioms Submission.impl_correct
