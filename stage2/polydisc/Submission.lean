import Spec

/-!
# polydisc — one big division where the specification does two

The specification's subresultant step divides every coefficient of the
pseudo-remainder by the square of the previous leading coefficient, and
`exactDividePolynomial` does it like this:

    if divisor == 0 || coefficient % divisor != 0 then none
    else ... coefficient / divisor ...

That is two full big-integer divisions of the same pair: one to decide
whether the division is exact, and then the same division again for the
quotient. `%` on `Int` is not cheaper than `/`; it computes the quotient to
find the remainder.

At the largest judged size the coefficients reach about eighty thousand bits,
and `costmodel.py` counts the divisibility test alone at a fifth of all the
bit-length flowing through the multiplications and divisions of the whole
computation. This file computes the quotient once and checks it by
multiplying back, which is one division and one multiplication instead of two
divisions. The guard is kept exactly: a non-exact division still returns
`none`, so the Bareiss fallback is still selected on the same inputs.

Nothing else is changed. The polynomial, the derivative, the pseudo-remainder
and the fallback are the specification's own, so the only obligation is that
the new division agrees with the old one everywhere, which
`exactDivide_eq` proves from the division identity rather than from any
property of the inputs.
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
theorem emod_eq_zero_iff (c d : Int) (hd : d ≠ 0) :
    c % d = 0 ↔ c / d * d = c := by
  constructor
  · intro h
    have := Int.ediv_add_emod c d
    rw [h, Int.add_zero] at this
    rw [Int.mul_comm]
    exact this
  · intro h
    have := Int.ediv_add_emod c d
    rw [Int.mul_comm d (c / d), h] at this
    omega

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
      rw [hb]
      simp only [Bool.false_or, if_false]
      by_cases hdvd : c % divisor = 0
      · have h1 : (c / divisor * divisor == c) = true := by
          simp [(emod_eq_zero_iff c divisor hz).mp hdvd]
        have h2 : (c % divisor != 0) = false := by simp [hdvd]
        rw [h1, h2]
        simp only [if_true, if_false, Bool.false_eq_true]
        rw [ih]
      · have h1 : (c / divisor * divisor == c) = false := by
          have : ¬ (c / divisor * divisor = c) := fun h =>
            hdvd ((emod_eq_zero_iff c divisor hz).mpr h)
          simp [this]
        have h2 : (c % divisor != 0) = true := by simp [hdvd]
        rw [h1, h2]
        simp

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

theorem resultantGo_eq :
    ∀ fuel initial f g,
      resultantGo fuel initial f g = normalResultantGo fuel initial f g := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _; rfl
  | succ n ih =>
    intro initial f g
    rw [resultantGo, normalResultantGo]
    cases hpr : pseudoRemainder f g with
    | none => rfl
    | some raw =>
      simp only [exactDivide_eq]
      cases hdiv : (if initial then some raw
          else exactDividePolynomial ((f.headD 0) ^ 2) raw) with
      | none => rfl
      | some coefficients =>
        cases htrim : trimLeading coefficients with
        | nil => rfl
        | cons a as =>
          by_cases hlen : (a :: as).length + 1 == g.length = true
          · simp only [hlen, if_true]
            cases as with
            | nil => rfl
            | cons b bs => exact ih false g (a :: b :: bs)
          · simp only [hlen, if_false, Bool.false_eq_true]
            rfl

def resultant (f g : List Int) : Option Int :=
  let f := trimLeading f
  let g := trimLeading g
  if f.length == g.length + 1 && !g.isEmpty then
    resultantGo (g.length + 1) true f g
  else
    none

theorem resultant_eq (f g : List Int) : resultant f g = normalResultant f g := by
  rw [resultant, normalResultant]
  split <;> simp [resultantGo_eq]

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
