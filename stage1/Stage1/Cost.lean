/-
What the kernel actually pays.

Every claim in this file is checked by the kernel when the file is built, which
is the only reason to write them as proofs rather than as comments.
-/
import Stage1.Impl
import Stage1.Spec

namespace Stage1.Cost

/-- The implementation on a large input. One multiplication on literals, which
the kernel does with GMP-backed arithmetic. -/
example : Impl.double 1000000 = 2000000 := by rfl

/-- Literal arithmetic the kernel accelerates: addition, multiplication,
division, remainder and equality on `Nat`. -/
example : 123456789 * 987654321 = 121932631112635269 := by rfl
example : 121932631112635269 % 1000000007 = 121932631112635269 % 1000000007 := by rfl

/-- The specification on a small input, for contrast. The kernel unfolds this
once per unit, so the cost is linear in the number rather than in its size. -/
example : Spec.double 64 = 128 := by rfl

/-
The axiom list is the audit. A finished artifact should depend on nothing
beyond Lean's three standard axioms, and in particular not on
`Lean.ofReduceBool`, which is what `native_decide` adds when it steps outside
the kernel.
-/
#print axioms Stage1.impl_eq_spec

end Stage1.Cost
