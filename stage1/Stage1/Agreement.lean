/-
Agreement between the implementation and the specification, on every input.

The judge checks this before it measures anything, so it is the part that must
exist. `sorry` is not a submission, and neither is `native_decide`: it discharges
the goal outside the kernel and leaves `Lean.ofReduceBool` behind in the axiom
list, which is exactly what a scoring rule based on kernel work excludes.
-/
import Stage1.Spec
import Stage1.Impl

namespace Stage1

/-- The implementation and the specification agree at every natural number. -/
theorem impl_eq_spec (n : Nat) : Impl.double n = Spec.double n := by
  induction n with
  | zero => rfl
  | succ k ih =>
    simp only [Impl.double, Spec.double] at ih ⊢
    omega

/-- The same fact at one concrete input, settled by the kernel rather than by
the proof above. This is the cheap check that the two definitions really are
about the same function. -/
example : Impl.double 100 = Spec.double 100 := by decide

end Stage1
