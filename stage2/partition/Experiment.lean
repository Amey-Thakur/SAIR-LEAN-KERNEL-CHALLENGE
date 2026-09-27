import Submission

/-!
# Does the kernel reduce the previous row once, or once per reference?

The measurement that occasioned this. The packed entry performs about 2,801
`Nat` operations across the six judged sizes and the judge measured it at
132,036,341 units of work, which is roughly 47,000 units per operation. A
separate probe then timed each primitive on its own and found every one of them
free: `shiftLeft`, `shiftRight`, `add`, `mul` and `mod` all cost bare process
startup at 2,701 bits and still cost bare process startup at 43,216 bits,
sixteen times the row width. So the cost is not arithmetic. It is reduction
steps, and something is making far more of them than the operation count says.

The suspect. In

    sweep s R (J + 1) = R + (sweep s R J) <<< s

the previous row `R` appears in every one of the `J + 1` unfoldings. The caller
names it once,

    let prev := rowsPM n M k

but a `let` the kernel zeta-expands puts the whole unreduced `rowsPM n M k` term
back at each occurrence, and then the previous row is computed again for every
term of the sweep rather than once. Row `k` costs `n / k` times what it should,
recursively, which is a multiplier no reduction in the operation count can
touch. That would explain a factor this large; nothing else measured so far
does.

The change under test. `sweep` can be written so `R` occurs exactly once. The
sweep multiplies its argument by a fixed bit pattern -- ones spaced `s` apart --
and that pattern does not mention `R` at all:

    sweepMul s 0       = 1
    sweepMul s (J + 1) = 1 + (sweepMul s J) <<< s
    sweep s R J        = R * sweepMul s J

which is an identity, not an approximation:

    sweep s R 0       = R                      = R * 1
    sweep s R (J + 1) = R + (sweep s R J) <<< s
                      = R + (R * sweepMul s J) <<< s
                      = R * (1 + (sweepMul s J) <<< s)
                      = R * sweepMul s (J + 1)

using only that shifting left by `s` is multiplication by `2 ^ s`. It also turns
`J` shifts and `J` additions on a row-sized operand into one multiplication,
which the primitive probe measured as free.

This file carries no proof. It is here to answer one question -- whether the
duplication is real and how much it costs -- before a proof is written for it.
If the two implementations time the same, the suspect is innocent and the
`sweepMul` form is not worth proving. The judged sizes are far too fast to time
on a shared runner, so the comparison is made at n = 200 and n = 300, where the
existing entry takes 0.14 s and 0.33 s and a real difference will show.
-/

namespace Alt

/-- The bit pattern the sweep multiplies by: `J + 1` ones, spaced `s` apart.
Built without reference to any row, so nothing about a row can be duplicated
into it. -/
def sweepMul (s : Nat) : Nat → Nat
  | 0     => 1
  | J + 1 => 1 + (sweepMul s J) <<< s

/-- The row recursion, with the previous row occurring exactly once. -/
def rowsPM (n : Nat) (M : Nat) : Nat → Nat
  | 0     => 1
  | k + 1 => rowsPM n M k * sweepMul (Submission.width n * (k + 1)) (n / (k + 1)) % M

def rowsP (n : Nat) (k : Nat) : Nat := rowsPM n (Submission.rowMod n) k

def impl (n : Nat) : Nat :=
  rowsP n n / (1 <<< (Submission.width n * n)) % (1 <<< Submission.width n)

end Alt

-- Reducing `Alt.impl 36` goes deeper than the elaborator's default recursion
-- limit, and the first run of this file failed on exactly that: `maximum
-- recursion depth has been reached` at the n = 36 example. That is the
-- elaborator giving up on checking the answer, not the kernel failing to
-- compute it, and it is the same confusion this repository has already made
-- three times. Both limits are lifted here so a failure below means what it
-- says. `timecases.py` and `primitives.py` set the same two options.
set_option maxRecDepth 8000000
set_option maxHeartbeats 0

/-- Agreement at small inputs, checked by the kernel. This is not a proof for
every `n`; it is a guard against timing a variant that computes the wrong thing,
which is the one way a speed-up here could be meaningless. -/
example : Alt.impl 0 = 1 := by rfl
example : Alt.impl 1 = 1 := by rfl
example : Alt.impl 5 = 7 := by rfl
example : Alt.impl 10 = 42 := by rfl
example : Alt.impl 13 = 101 := by rfl
example : Alt.impl 36 = 17977 := by rfl
