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
`%` on `Int` is not cheaper than `/`; it computes the quotient to find the
remainder.

At the largest judged size the coefficients reach about eighty thousand bits,
and `costmodel.py` counts the divisibility test alone at a fifth of all the
bit-length flowing through the multiplications and divisions of the whole
computation. This file computes the quotient once and checks it by
multiplying back: one division and one multiplication instead of two
divisions. The guard is kept exactly, so a non-exact division still returns
`none` and the Bareiss fallback is still selected on the same inputs.

Nothing else changes. The polynomial, the derivative, the pseudo-remainder
and the fallback are the specification's own, so the only obligation is that
the new division agrees with the old one everywhere. That is proved from
divisibility rather than from any property of the inputs, and it holds for a
zero divisor too: there `c / 0 * 0 = 0`, and both sides say `c = 0`.
-/

namespace Submission

/-- `exactDividePolynomial`, with the divisibility test done by multiplying
the quotient back rather than by a second division. -/
def exactDivide (divisor : Int) : List Int → Option (List Int)
  | [] => some []
  | coefficient :: coefficients =>
      if divisor == 0 then none
      else
        let quotient := coefficient / divisor
        if quotient * divisor == coefficient then
          match exactDivide divisor coefficients with
          | none => none
          | some rest => some (quotient :: rest)
        else none

/-- The test this file replaces, as an identity on `Int`. -/
theorem emod_zero_iff (c d : Int) : c % d = 0 ↔ c / d * d = c := by
  constructor
  · intro h
    exact Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero h)
  · intro h
    exact Int.emod_eq_zero_of_dvd ⟨c / d, by rw [← h]; exact Int.mul_comm _ _⟩

theorem exactDivide_eq (divisor : Int) :
    ∀ p, exactDivide divisor p = exactDividePolynomial divisor p := by
  intro p
  induction p with
  | nil => rfl
  | cons c cs ih =>
    rw [exactDivide, exactDividePolynomial]
    by_cases hz : divisor = 0
    · subst hz; simp
    · have hb : (divisor == 0) = false := by simp [hz]
      by_cases hdvd : c % divisor = 0
      · have h1 : (c / divisor * divisor == c) = true := by
          simp [(emod_zero_iff c divisor).mp hdvd]
        have h2 : (c % divisor != 0) = false := by simp [hdvd]
        simp only [hb, h1, h2, Bool.false_or, if_false, if_true]
        rw [ih]
      · have h1 : (c / divisor * divisor == c) = false := by
          have hne : ¬ (c / divisor * divisor = c) := fun h =>
            hdvd ((emod_zero_iff c divisor).mpr h)
          simp [hne]
        have h2 : (c % divisor != 0) = true := by simp [hdvd]
        simp [hb, h1, h2]

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
theorem resultantGo_eq : resultantGo = normalResultantGo := by
  funext fuel
  induction fuel with
  | zero => funext initial f g; rfl
  | succ n ih =>
    funext initial f g
    rw [resultantGo, normalResultantGo, exactDivide_eq_fun]
    simp only [ih]

def resultant (f g : List Int) : Option Int :=
  let f := trimLeading f
  let g := trimLeading g
  if f.length == g.length + 1 && !g.isEmpty then
    resultantGo (g.length + 1) true f g
  else
    none

theorem resultant_eq : resultant = normalResultant := by
  funext f g
  rw [resultant, normalResultant, resultantGo_eq]

def resultantOf (p : List Int) : Int :=
  let derivative := derivHL p
  match resultant p derivative with
  | some r => r
  | none => bareissDet (monicReducedSylvester p derivative)

theorem resultantOf_eq : resultantOf = resultantFromPoly := by
  funext p
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
