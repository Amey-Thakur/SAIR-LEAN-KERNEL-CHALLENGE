/-
The trusted specification.

A specification is written to be obviously right, not fast. It is the thing the
judge compares against, so it recurses on the structure of its input and pays
whatever that costs. Doubling stands in here for a real problem: the point is
that evaluating it at `n` forces the kernel through `n` unfoldings.
-/
namespace Stage1.Spec

/-- Doubling by structural recursion. Obviously correct, and linear in `n`
for anything that has to evaluate it. -/
def double : Nat → Nat
  | 0 => 0
  | n + 1 => double n + 2

end Stage1.Spec
