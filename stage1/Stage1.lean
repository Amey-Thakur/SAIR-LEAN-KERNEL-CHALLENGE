/-
A Stage 1 submission has three parts, and they are kept in three files so that
the boundaries stay honest:

  Spec       the trusted specification, which the organisers supply
  Impl       an implementation written to be cheap for the kernel to check
  Agreement  a machine-checked proof that Impl agrees with Spec on every input

The problems themselves are announced at the official launch on 15 September
2026. What is here is the shape a submission takes, with one worked example,
so that a problem can be dropped in rather than designed around.
-/
import Stage1.Spec
import Stage1.Impl
import Stage1.Agreement
import Stage1.Cost
