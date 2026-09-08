/-
The implementation.

The only thing being optimised is what Lean's kernel has to do when it checks
the artifact. That is a different objective from run time: the compiler is not
involved, so a fast `#eval` is no evidence at all. What helps is arriving at an
answer the kernel can reach in a few steps on values it handles natively.
-/
namespace Stage1.Impl

/-- Doubling as one multiplication. The kernel has GMP-backed arithmetic for
`Nat` literals, so this costs about the same whatever `n` is. -/
def double (n : Nat) : Nat := 2 * n

end Stage1.Impl
