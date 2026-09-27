import Spec

/-!
# Lemma inventory probe for `mertens`

The measured starting point: the shipped starter reduces none of the five
judged sizes. `mertensSpec` sums Mathlib's `ArithmeticFunction.moebius`, which
is defined through `Squarefree` and the prime factorisation, and those reach
`Nat.minFac`, which is well-founded recursion the kernel cannot unfold. The
same defect that stops `primecount`, one layer further down.

So the whole of `moebius` has to be recomputed with structural recursion and
proved equal to Mathlib's. That is a much larger obligation than `primecount`,
where only the primality test had to be replaced, and it is worth finding out
which route Mathlib actually supports before committing to one.

Three candidate routes, in decreasing order of preference:

  A. `moebius n` unfolds to `if Squarefree n then (-1) ^ cardFactors n else 0`.
     If `Squarefree` has a decidable instance that does not route through
     `minFac`, and `cardFactors` can be reached from a structural
     factorisation, this is the shortest path.
  B. Prove a structural `minFacFast = Nat.minFac`, then reuse Mathlib's whole
     factorisation API on top of it. Longer, but every later lemma is free.
  C. Characterise `moebius` by its defining sum, `∑ d ∣ n, moebius d = if n = 1
     then 1 else 0`, and derive the values from that. Avoids factorisation
     entirely but needs the inversion machinery.

Nothing here is submitted; this file exists only to be compiled.
-/

section MoebiusShape

#check @ArithmeticFunction.moebius
#check @ArithmeticFunction.moebius_apply_of_squarefree
#check @ArithmeticFunction.moebius_eq_zero_of_not_squarefree
#check @ArithmeticFunction.moebius_apply_one
#check @ArithmeticFunction.moebius_apply_prime
#check @ArithmeticFunction.cardFactors
#check @ArithmeticFunction.cardDistinctFactors

end MoebiusShape

section RouteA

-- Is squarefreeness decidable without going through minFac?
#check @Nat.squarefree_iff_prime_squarefree
#check @Nat.squarefree_iff_nodup_primeFactorsList
#check @Nat.minSqFac

-- The factor count the sign comes from.
#check @Nat.primeFactorsList

end RouteA

section RouteB

-- If minFac can be replaced by a structural equal, Mathlib's API comes with it.
#check @Nat.minFac
#check @Nat.minFac_dvd
#check @Nat.minFac_prime
#check @Nat.minFac_le
#check @Nat.minFac_eq
#check @Nat.prime_def_minFac

end RouteB

section RouteC

-- The defining property, if the other two routes are worse than they look.
#check @ArithmeticFunction.moebius_mul_coe_zeta
#check @ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq
#check @Nat.sum_divisors_eq_sum_properDivisors_add_self

end RouteC

section Summation

-- The spec's own shape: a Finset.range sum of an Int-valued function.
#check @mertensSpec
#check @Finset.sum_range_succ
#check @Finset.range_zero
#check @Finset.sum_congr

example : mertensSpec 0 = 0 := by rfl
example : mertensSpec 1 = 1 := by decide

end Summation

section Diagnosis

-- Confirms the diagnosis rather than assuming it: if this reduces, the
-- blocker is somewhere other than where this file claims.
example : (ArithmeticFunction.moebius 6 : Int) = 1 := by decide

end Diagnosis

section RouteBDetail

/- The probe's diagnosis example FAILED, which is the confirmation it was
placed for: `decide` cannot settle `ArithmeticFunction.moebius 6 = 1`, so the
blocker really is at moebius itself and not somewhere in the summation.

Route B is therefore the plan: replace `Nat.minFac` with a structural equal,
then `Nat.primeFactorsList` follows, and Mathlib's squarefree and factor-count
API comes with it for free. These are the names that route needs. -/

-- The definitional shape of minFac, which a structural replacement must match.
#check @Nat.minFacAux
#check @Nat.minFac_eq
#check @Nat.minFacAux_has_prop
#check @Nat.minFac_sq_le_self
#check @Nat.minFac_pos

-- primeFactorsList is defined by well-founded recursion on n / minFac n;
-- these are the equation lemmas a mirroring induction needs.
#check @Nat.primeFactorsList
#check @Nat.primeFactorsList_zero
#check @Nat.primeFactorsList_one
#check @Nat.primeFactorsList_succ_succ
#check @Nat.prod_primeFactorsList
#check @Nat.mem_primeFactorsList

-- Strong induction, since the recursion decreases by division not subtraction.
#check @Nat.strong_induction_on
#check @Nat.strongRecOn
#check @Nat.div_lt_self

-- And what moebius becomes once a factorisation is available.
#check @ArithmeticFunction.cardFactors_apply
#check @Nat.squarefree_iff_nodup_primeFactorsList

end RouteBDetail
