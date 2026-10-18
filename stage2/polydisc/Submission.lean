import Spec

/-!
# polydisc — one big division where the specification does two

The specification's subresultant step divides every coefficient of the
pseudo-remainder by the square of the previous leading coefficient, and
`exactDividePolynomial` does it like this:

    if divisor == 0 || coefficient % divisor != 0 then none
    else ... coefficient / divisor ...

That is two full big-integer divisions of the same pair: one to decide
whether the division is exact, and the same division again for the quotient.
`%` on `Int` is not cheaper than `/`; `Int.emod_def` says as much,
`a % b = a - b * (a / b)`.

At the largest judged size the coefficients reach about eighty thousand bits,
and `costmodel.py` counts the divisibility test alone at a fifth of all the
bit-length flowing through the multiplications and divisions of the whole
computation. This file computes the quotient once, binds it, and checks it by
multiplying back: one division and one multiplication instead of two
divisions. The binding is what makes that true rather than cosmetic, since
the kernel shares a value it has already reduced.

The guard is kept exactly, so a non-exact division still returns `none` and
the Bareiss fallback is still selected on the same inputs. Nothing else
changes: the polynomial, the derivative, the pseudo-remainder and the
fallback are the specification's own, so the only obligation is that the new
division agrees with the old one everywhere. That is proved from
divisibility, and it holds for a zero divisor too, where `c / 0 * 0 = 0` and
both sides say `c = 0`.
-/

namespace Submission

/-- `exactDividePolynomial`, with the divisibility test done by multiplying
the quotient back rather than by a second division. -/
def exactDivide (divisor : Int) : List Int → Option (List Int)
  | [] => some []
  | coefficient :: coefficients =>
      let quotient := coefficient / divisor
      if divisor == 0 || quotient * divisor != coefficient then none
      else
        match exactDivide divisor coefficients with
        | none => none
        | some rest => some (quotient :: rest)

/-- The test this file replaces, as an identity on `Int`. -/
theorem emod_zero_iff (c d : Int) : c % d = 0 ↔ c / d * d = c := by
  constructor
  · intro h
    exact Int.ediv_mul_cancel_of_emod_eq_zero h
  · intro h
    rw [Int.emod_def, Int.mul_comm, h]
    omega

/-- The two guards decide the same thing, so the bodies around them are
already identical. -/
theorem guard_eq (c divisor : Int) :
    (divisor == 0 || c / divisor * divisor != c)
      = (divisor == 0 || c % divisor != 0) := by
  by_cases hz : divisor = 0
  · simp [hz]
  · have key : (c / divisor * divisor == c) = (c % divisor == 0) := by
      by_cases h : c % divisor = 0
      · simp [h, Int.ediv_mul_cancel_of_emod_eq_zero h]
      · have hne : ¬ (c / divisor * divisor = c) := fun hh =>
          h ((emod_zero_iff c divisor).mpr hh)
        simp [h, hne]
    simp only [bne, key]

theorem exactDivide_eq (divisor : Int) :
    ∀ p, exactDivide divisor p = exactDividePolynomial divisor p := by
  intro p
  induction p with
  | nil => rfl
  | cons c cs ih =>
    rw [exactDivide, exactDividePolynomial, guard_eq, ih]

/-- As functions, so the substitution below is a rewrite. -/
theorem exactDivide_eq_fun : exactDivide = exactDividePolynomial := by
  funext d p
  exact exactDivide_eq d p

/-- The specification's subresultant loop, with the new division. -/
def resultantGo : Nat → Bool → List Int → List Int → Option Int
  | 0, _, _, _ => none
  | fuel + 1, initial, f, g =>
      match pseudoRemainder f g with
      | none => none
      | some raw =>
          let divided :=
            if initial then some raw
            else exactDivide ((f.headD 0) ^ 2) raw
          match divided with
          | none => none
          | some coefficients =>
              match trimLeading coefficients with
              | [] => some 0
              | remainder =>
                  if remainder.length + 1 == g.length then
                    match remainder with
                    | [constant] => some constant
                    | _ => resultantGo fuel false g remainder
                  else
                    none

/-- Both bodies are the same once the division is rewritten, so the induction
closes by rewriting rather than by taking the matches apart. -/
theorem resultantGo_eq : ∀ fuel initial f g,
    resultantGo fuel initial f g = normalResultantGo fuel initial f g := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _; rfl
  | succ n ih =>
    intro initial f g
    rw [resultantGo, normalResultantGo, exactDivide_eq_fun]
    -- the bodies are now the same except for the recursive call, which the
    -- induction hypothesis supplies; the matches are opened rather than
    -- rewritten through, because `simp only` will not reduce under them
    cases pseudoRemainder f g with
    | none => rfl
    | some raw =>
      cases (if initial then some raw
             else exactDividePolynomial ((f.headD 0) ^ 2) raw) with
      | none => rfl
      | some coefficients =>
        cases trimLeading coefficients with
        | nil => rfl
        | cons a as =>
          by_cases hl : ((a :: as).length + 1 == g.length) = true
          · rw [if_pos hl]
            cases as with
            | nil => rfl
            | cons b bs => exact ih false g (a :: b :: bs)
          · rw [if_neg hl]

def resultant (f g : List Int) : Option Int :=
  let f := trimLeading f
  let g := trimLeading g
  if f.length == g.length + 1 && !g.isEmpty then
    resultantGo (g.length + 1) true f g
  else
    none

theorem resultant_eq (f g : List Int) : resultant f g = normalResultant f g := by
  rw [resultant, normalResultant, resultantGo_eq]

def resultantOf (p : List Int) : Int :=
  let derivative := derivHL p
  match resultant p derivative with
  | some r => r
  | none => bareissDet (monicReducedSylvester p derivative)

theorem resultantOf_eq (p : List Int) : resultantOf p = resultantFromPoly p := by
  rw [resultantOf, resultantFromPoly, resultant_eq]

def impl (n : Nat) : Int :=
  let p := polyOf n
  let degree := p.length - 1
  let sign : Int := if degree * (degree - 1) / 2 % 2 = 0 then 1 else -1
  sign * resultantOf p

theorem impl_correct : ∀ n, impl n = discSpec n := by
  intro n
  rw [impl, discSpec, discriminantFromPoly, resultantOf_eq]

end Submission
