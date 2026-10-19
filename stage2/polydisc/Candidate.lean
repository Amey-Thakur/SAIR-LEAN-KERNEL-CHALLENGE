import Spec

/-!
# polydisc — the multiplication by one that the specification always performs

Measured facts this file is built on, all from the instruction counter in
`.github/workflows/polydisc.yml`, which reproduces the leaderboard figure for
the shipped starter to within 4%:

* the metric is the number of kernel reduction steps, and the width of the
  operands is nearly free. The easiest judged case costs 1,483,351,202 and the
  hardest 2,375,274,780, a ratio of 1.60, where the operand widths differ by a
  factor of 140. Only an operation count predicts that; a bit-length proxy
  predicts 97 and a schoolbook proxy 8,205.
* an `Int` operation costs 5.4x a `Nat` operation of the same width, because
  `Int` is an inductive type and every operation is a case analysis before it
  is arithmetic.
* the coefficient setup is therefore the wrong half to cut. It is 55% of the
  operations at the hardest size but they are narrow `Nat` operations, and the
  easiest judged case, whose setup is 15x smaller, still costs 62% of the
  hardest. What the two cases share is the subresultant loop, whose operation
  count does not depend on the coefficient width at all.

So the target is `Int` operations inside the loop, and the specification
performs one per coefficient that it does not need.

`pseudoRemainderGo` finishes with

    some (scalePolynomial ((divisor.headD 0) ^ remaining) dividend)

where `remaining` counts down from `dividend.length - divisor.length + 1`. In
the normal case, which is the case every judged input takes, the dividend has
exactly one more coefficient than the divisor, so `remaining` starts at 2, two
cancellation steps run, and the scaling factor is `lc ^ 0 = 1`. The
specification then multiplies every coefficient of the widest intermediate it
ever holds by one: 276 multiplications and 276 list cells per judged case,
performed on the pseudo-remainder before the exact division shrinks it.

`scaleP` returns the list unchanged when the factor is one and calls the
specification's own `scalePolynomial` otherwise, so nothing is assumed about
`remaining`: an abnormal degree drop, where the factor really is `lc` or
`lc ^ 2`, still scales. The obligation is one lemma, that multiplying a list
by one returns it.

The division removed from `exactDividePolynomial` in the previous entry is
kept: the specification tests `coefficient % divisor != 0` and then divides
again for the quotient, and one division plus one multiplication by the short
quotient does both.
-/

namespace Submission

/-! ## Which function each notation resolves to

`a * b` on `Int` is `@HMul.hMul Int Int Int instHMul a b`, and the kernel must
unfold the `HMul.hMul` projection, `instHMul`, the `Mul.mul` projection and
`Int.instMul` before it reaches an operation it can compute. The arguments
differ at every use, so no cache helps, and the subresultant loop performs
about 2,500 of these per judged case.

Writing the function directly skips that, and costs nothing in correctness
because the two are the same term up to unfolding. These four lines check that
claim rather than assuming it: if `/` on `Int` were truncating division rather
than `Int.ediv`, the third would fail by name instead of the proof failing
somewhere less obvious. -/

example (a b : Int) : a * b = Int.mul a b := rfl
example (a b : Int) : a - b = Int.sub a b := rfl
example (a b : Int) : a / b = Int.ediv a b := rfl
example (a b : Int) : a % b = Int.emod a b := rfl

/-! ## The scaling that is usually by one -/

/-- `scalePolynomial`, which returns its argument when the factor is one. -/
def scaleP (factor : Int) (p : List Int) : List Int :=
  if factor == 1 then p else scalePolynomial factor p

theorem scalePolynomial_one : ∀ p, scalePolynomial 1 p = p := by
  intro p
  induction p with
  | nil => rfl
  | cons c cs ih =>
    show (1 : Int) * c :: scalePolynomial 1 cs = c :: cs
    rw [ih, Int.one_mul]

theorem scaleP_eq (factor : Int) (p : List Int) :
    scaleP factor p = scalePolynomial factor p := by
  by_cases h : (factor == 1) = true
  · have hf : factor = 1 := eq_of_beq h
    -- the order matters and `simp only` gets it wrong: rewriting `factor` to
    -- one first turns the condition into `1 == 1`, which leaves `if c then p
    -- else p` with no rule to collapse it and makes `if_pos h` unused, which
    -- this package reports as an error. `rw` takes the branch first.
    show (if factor == 1 then p else scalePolynomial factor p)
        = scalePolynomial factor p
    rw [if_pos h, hf, scalePolynomial_one]
  · show (if factor == 1 then p else scalePolynomial factor p)
        = scalePolynomial factor p
    rw [if_neg h]

/-! ## The pseudo-remainder, with that scaling guarded

The shape is the specification's, so the proof is one rewrite at each step
rather than a case analysis on the two lists. -/

/-- `cancelPseudoLeading` with the arithmetic written as the functions the
notation resolves to. Two multiplications and a subtraction per coefficient,
about 1,750 of them per judged case, each one four fewer unfoldings. -/
def cancelFast (lcG lcR : Int) : List Int → List Int → List Int
  | coefficient :: coefficients, divisor :: divisors =>
      Int.sub (Int.mul lcG coefficient) (Int.mul lcR divisor) ::
        cancelFast lcG lcR coefficients divisors
  | coefficient :: coefficients, [] =>
      Int.mul lcG coefficient :: cancelFast lcG lcR coefficients []
  | [], _ => []

theorem cancelFast_eq (lcG lcR : Int) : ∀ (cs ds : List Int),
    cancelFast lcG lcR cs ds = cancelPseudoLeading lcG lcR cs ds := by
  intro cs
  induction cs with
  | nil => intro ds; rfl
  | cons c cs ih =>
    intro ds
    cases ds with
    | nil => show Int.mul lcG c :: cancelFast lcG lcR cs [] = _
             rw [ih []]
    | cons d ds =>
      show Int.sub (Int.mul lcG c) (Int.mul lcR d)
             :: cancelFast lcG lcR cs ds = _
      rw [ih ds]

def premGo : Nat → Nat → List Int → List Int → Option (List Int)
  | 0, _, _, _ => none
  | fuel + 1, remaining, divisor, dividend =>
      let dividend := trimLeading dividend
      if dividend.length < divisor.length then
        some (scaleP ((divisor.headD 0) ^ remaining) dividend)
      else
        match divisor, dividend with
        | lcG :: divisorTail, lcR :: dividendTail =>
            let next :=
              trimLeading (cancelFast lcG lcR dividendTail divisorTail)
            premGo fuel (remaining - 1) divisor next
        | _, _ => none

theorem premGo_eq : ∀ (fuel remaining : Nat) (divisor dividend : List Int),
    premGo fuel remaining divisor dividend
      = pseudoRemainderGo fuel remaining divisor dividend := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _; rfl
  | succ n ih =>
    intro remaining divisor dividend
    simp only [premGo, pseudoRemainderGo, scaleP_eq, cancelFast_eq, ih]
    -- what is left is the same match under two auto-generated matchers,
    -- which only full transparency sees through
    all_goals rfl

def prem (dividend divisor : List Int) : Option (List Int) :=
  let dividend := trimLeading dividend
  let divisor := trimLeading divisor
  if divisor.isEmpty then none
  else if dividend.length < divisor.length then some dividend
  else
    premGo (dividend.length + 1)
      (dividend.length - divisor.length + 1) divisor dividend

theorem prem_eq (dividend divisor : List Int) :
    prem dividend divisor = pseudoRemainder dividend divisor := by
  simp only [prem, pseudoRemainder, premGo_eq]

theorem prem_eq_fun : prem = pseudoRemainder := by
  funext a b
  exact prem_eq a b

/-! ## One division where the specification does two -/

def exactDivide (divisor : Int) : List Int → Option (List Int)
  | [] => some []
  | coefficient :: coefficients =>
      let quotient := Int.ediv coefficient divisor
      if divisor == 0 || Int.mul quotient divisor != coefficient then none
      else
        match exactDivide divisor coefficients with
        | none => none
        | some rest => some (quotient :: rest)

theorem emod_zero_iff (c d : Int) : c % d = 0 ↔ c / d * d = c := by
  constructor
  · intro h
    exact Int.ediv_mul_cancel_of_emod_eq_zero h
  · intro h
    rw [Int.emod_def, Int.mul_comm, h]
    omega

theorem guard_eq (c divisor : Int) :
    (divisor == 0 || Int.mul (Int.ediv c divisor) divisor != c)
      = (divisor == 0 || c % divisor != 0) := by
  -- stated with the functions, because that is what `exactDivide` contains,
  -- and proved in the notation, because that is what the core lemmas are
  -- stated in. The two are the same term up to unfolding.
  show (divisor == 0 || c / divisor * divisor != c)
      = (divisor == 0 || c % divisor != 0)
  by_cases h : c % divisor = 0
  · have h1 : c / divisor * divisor = c :=
      Int.ediv_mul_cancel_of_emod_eq_zero h
    have e1 : (c / divisor * divisor != c) = false := by simp [h1]
    have e2 : (c % divisor != 0) = false := by simp [h]
    rw [e1, e2]
  · have hne : ¬ (c / divisor * divisor = c) := fun hh =>
      h ((emod_zero_iff c divisor).mpr hh)
    have e1 : (c / divisor * divisor != c) = true := by simp [hne]
    have e2 : (c % divisor != 0) = true := by simp [h]
    rw [e1, e2]

theorem exactDivide_eq (divisor : Int) :
    ∀ p, exactDivide divisor p = exactDividePolynomial divisor p := by
  intro p
  induction p with
  | nil => rfl
  | cons c cs ih =>
    simp only [exactDivide, exactDividePolynomial, guard_eq, ih]
    all_goals rfl

theorem exactDivide_eq_fun : exactDivide = exactDividePolynomial := by
  funext d p
  exact exactDivide_eq d p

/-- `lc ^ 2` unfolds to `1 * lc * lc`, so the specification multiplies by one
here as well, once per step on top of the per-coefficient ones. -/
theorem sq_eq (h : Int) : Int.mul h h = h ^ 2 := by
  show Int.mul h h = 1 * h * h
  rw [Int.one_mul]

/-! ## The specification's subresultant loop, with both changes -/

def resultantGo : Nat → Bool → List Int → List Int → Option Int
  | 0, _, _, _ => none
  | fuel + 1, initial, f, g =>
      match prem f g with
      | none => none
      | some raw =>
          let divided :=
            if initial then some raw
            else exactDivide (Int.mul (f.headD 0) (f.headD 0)) raw
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

theorem resultantGo_eq : ∀ fuel initial f g,
    resultantGo fuel initial f g = normalResultantGo fuel initial f g := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _; rfl
  | succ n ih =>
    intro initial f g
    rw [resultantGo, normalResultantGo, exactDivide_eq_fun, prem_eq_fun,
      sq_eq]
    -- Each side's matches compile to their own matcher, so `split` takes the
    -- two apart independently and invents a separate variable for the same
    -- scrutinee. Every shared scrutinee is therefore generalised by hand.
    cases hpr : pseudoRemainder f g with
    | none => rfl
    | some raw =>
      try dsimp only
      by_cases hi : initial = true
      · simp only [if_pos hi]
        try dsimp only
        cases htr : trimLeading raw with
        | nil => rfl
        | cons a as =>
          try dsimp only
          cases as with
          | nil => split <;> rfl
          | cons b bs =>
            by_cases hl : ((a :: b :: bs).length + 1 == g.length) = true
            · simp only [if_pos hl]
              exact ih false g (a :: b :: bs)
            · simp only [if_neg hl]
      · simp only [if_neg hi]
        try dsimp only
        cases hed : exactDividePolynomial (f.headD 0 ^ 2) raw with
        | none => rfl
        | some coeffs =>
          try dsimp only
          cases htr : trimLeading coeffs with
          | nil => rfl
          | cons a as =>
            try dsimp only
            cases as with
            | nil => split <;> rfl
            | cons b bs =>
              by_cases hl : ((a :: b :: bs).length + 1 == g.length) = true
              · simp only [if_pos hl]
                exact ih false g (a :: b :: bs)
              · simp only [if_neg hl]

def resultant (f g : List Int) : Option Int :=
  let f := trimLeading f
  let g := trimLeading g
  if f.length == g.length + 1 && !g.isEmpty then
    resultantGo (g.length + 1) true f g
  else
    none

theorem resultant_eq (f g : List Int) :
    resultant f g = normalResultant f g := by
  rw [resultant, normalResultant, resultantGo_eq]

def resultantOf (p : List Int) : Int :=
  let derivative := derivHL p
  match resultant p derivative with
  | some r => r
  | none => bareissDet (monicReducedSylvester p derivative)

theorem resultantOf_eq (p : List Int) :
    resultantOf p = resultantFromPoly p := by
  rw [resultantOf, resultantFromPoly, resultant_eq]
  all_goals rfl

def impl (n : Nat) : Int :=
  let p := polyOf n
  let degree := p.length - 1
  let sign : Int := if degree * (degree - 1) / 2 % 2 = 0 then 1 else -1
  sign * resultantOf p

theorem impl_correct : ∀ n, impl n = discSpec n := by
  intro n
  rw [impl, discSpec, discriminantFromPoly, resultantOf_eq]

end Submission
