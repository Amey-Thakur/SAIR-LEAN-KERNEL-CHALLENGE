import Spec

/-!
# ca-rule110 — a whole row in one natural number

The specification holds the row as a `List Bool` of length 256 and reads each
neighbour with `getD`, which walks the list. Three reads per cell and 256 cells
make one step quadratic, and the judge asks for up to eight of them.

This submission keeps the specification's automaton exactly and changes only
where the row lives. Cell `i` becomes bit `i` of a single `Nat`, and the whole
row steps at once:

    new = (c ||| r) &&& ~~~(l &&& c &&& r)

where `l` is the row rotated one place up and `r` one place down. That identity
is the Rule 110 table, proved in `rule110_eq` rather than assumed.

Nothing else is optimised. The initial row is still built by the
specification's own `initRowFor` and encoded once by its own `encodeRow`, which
costs a few hundred steps against the hundreds of thousands the stepping costs,
and which means this file needs no lemma about how the row is created.

Core Lean only; the problem package has no Mathlib dependency.
-/

namespace Submission

/-! ## The packed row -/

/-- All 256 low bits set: the width the specification fixes. -/
def rowMask : Nat := (1 <<< ruleWidth) - 1

/-- The left neighbour of every cell at once. Bit `i` of the result is bit
`i - 1` of `R`, cyclically. -/
def rotL (R : Nat) : Nat :=
  ((R <<< 1) ||| (R >>> (ruleWidth - 1))) &&& rowMask

/-- The right neighbour of every cell at once. Bit `i` of the result is bit
`i + 1` of `R`, cyclically. -/
def rotR (R : Nat) : Nat :=
  ((R >>> 1) ||| ((R &&& 1) <<< (ruleWidth - 1))) &&& rowMask

/-- One Rule 110 step on the packed row: eight `Nat` operations, whatever the
row's length. -/
def pStep (R : Nat) : Nat :=
  (R ||| rotR R) &&& (rowMask ^^^ (rotL R &&& R &&& rotR R))

/-- `t` steps. -/
def pIter : Nat → Nat → Nat
  | 0,     R => R
  | t + 1, R => pIter t (pStep R)

/-! ## The implementation -/

def impl (n : Nat) : Nat :=
  pIter (caSteps n) (encodeRow (initRowFor (caSeed n)))

/-! ## The Rule 110 table as a formula -/

/-- The specification's three-case table is this boolean expression. Eight
patterns, so the case split settles it. -/
theorem rule110_eq (l c r : Bool) :
    rule110 l c r = ((c || r) && !(l && c && r)) := by
  cases l <;> cases c <;> cases r <;> rfl

/-! ## The mask -/

/-- `rowMask` is `2 ^ 256 - 1`, which is the form the bit lemmas are stated in. -/
theorem rowMask_eq : rowMask = 2 ^ ruleWidth - 1 := by
  show (1 <<< ruleWidth) - 1 = 2 ^ ruleWidth - 1
  rw [Nat.shiftLeft_eq, Nat.one_mul]

theorem testBit_rowMask (i : Nat) :
    rowMask.testBit i = decide (i < ruleWidth) := by
  rw [rowMask_eq, Nat.testBit_two_pow_sub_one]

/-! ## `encodeRow` read one bit at a time

This is the only fact about `encodeRow` the proof needs, and it is what makes
the packed row and the list row the same object seen two ways. -/

/-- Dropping the low bit of an encoded cons gives back the tail's encoding. -/
theorem half_cons (e : Nat) (b : Bool) :
    (2 * e + (if b then 1 else 0)) / 2 = e := by
  cases b
  · show (2 * e + 0) / 2 = e
    omega
  · show (2 * e + 1) / 2 = e
    omega

/-- Bit `i` of an encoded row is the row's `i`th cell. -/
theorem testBit_encodeRow (row : List Bool) :
    ∀ i, (encodeRow row).testBit i = row.getD i false := by
  induction row with
  | nil =>
    intro i
    show (0 : Nat).testBit i = false
    simp
  | cons b rest ih =>
    intro i
    show (2 * encodeRow rest + (if b then 1 else 0)).testBit i
        = (b :: rest).getD i false
    match i with
    | 0 =>
      show (2 * encodeRow rest + (if b then 1 else 0)).testBit 0 = b
      rw [Nat.testBit_zero]
      cases b
      · show decide ((2 * encodeRow rest + 0) % 2 = 1) = false
        simp
      · show decide ((2 * encodeRow rest + 1) % 2 = 1) = true
        simp
    | j + 1 =>
      rw [Nat.testBit_succ, half_cons, ih j]
      rfl

/-- Reading past the end of a list gives the default. `List.getD_eq_default`
does not exist in this toolchain, so this is the same fact assembled from the
two lemmas that do. -/
theorem getD_past_end (row : List Bool) (i : Nat) (h : row.length ≤ i) :
    row.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

/-- A row says nothing about bits at or above its length, so an encoded row's
high bits are zero. This replaces a numeric bound on `encodeRow`: the packing
argument needs only that the rotations have nothing to wrap in from above. -/
theorem testBit_encodeRow_high (row : List Bool) (i : Nat)
    (h : row.length ≤ i) : (encodeRow row).testBit i = false := by
  rw [testBit_encodeRow row i]
  exact getD_past_end row i h

/-! ## The rotations

Each is proved against a hypothesis that `R` has no bits at or above the row
width, which `testBit_encodeRow_high` supplies for any encoded row.

Two things learned from earlier rounds shape these proofs. `omega` treats
`ruleWidth` as an opaque atom because it is a definition, so every arithmetic
fact here is stated on the literal 256. And a `show` that guesses the goal
after a rewrite is a guess with no toolchain to check it, so the goals are
closed with `simp` and named hypotheses instead.
-/

/-- Every bit below the width is set in the mask. -/
theorem testBit_rowMask_lt (k : Nat) (hk : k < ruleWidth) :
    rowMask.testBit k = true := by
  rw [testBit_rowMask]
  simp [hk]

/-- Bit `i` of `rotL R` is bit `i - 1` of `R`, cyclically. -/
theorem testBit_rotL (R : Nat) (hR : ∀ j, ruleWidth ≤ j → R.testBit j = false)
    (i : Nat) (hi : i < ruleWidth) :
    (rotL R).testBit i = R.testBit ((i + ruleWidth - 1) % ruleWidth) := by
  have hw : ruleWidth = 256 := rfl
  rw [rotL, Nat.testBit_and, Nat.testBit_or, testBit_rowMask_lt i hi,
      Bool.and_true, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  cases i with
  | zero =>
    have hm : (0 + ruleWidth - 1) % ruleWidth = ruleWidth - 1 := by
      rw [hw]
    rw [hm]
    simp
  | succ k =>
    have hkw : k + 1 < 256 := by rw [hw] at hi; omega
    have hm : (k + 1 + ruleWidth - 1) % ruleWidth = k := by
      rw [hw]
      omega
    have hover : R.testBit (ruleWidth - 1 + (k + 1)) = false := by
      refine hR _ ?_
      rw [hw]
      omega
    rw [hm, hover]
    simp

/-- Bit `i` of `rotR R` is bit `i + 1` of `R`, cyclically. -/
theorem testBit_rotR (R : Nat) (hR : ∀ j, ruleWidth ≤ j → R.testBit j = false)
    (i : Nat) (hi : i < ruleWidth) :
    (rotR R).testBit i = R.testBit ((i + 1) % ruleWidth) := by
  have hw : ruleWidth = 256 := rfl
  rw [rotR, Nat.testBit_and, Nat.testBit_or, testBit_rowMask_lt i hi,
      Bool.and_true, Nat.testBit_shiftRight, Nat.testBit_shiftLeft,
      Nat.testBit_and]
  by_cases hlast : i = ruleWidth - 1
  · have hm : (i + 1) % ruleWidth = 0 := by
      rw [hw] at hlast ⊢
      omega
    have hover : R.testBit (1 + i) = false := by
      refine hR _ ?_
      rw [hw] at hlast ⊢
      omega
    rw [hm, hover, hlast]
    simp
  · have hlt : i < ruleWidth - 1 := by
      rw [hw] at hi hlast ⊢
      omega
    have hm : (i + 1) % ruleWidth = i + 1 := by
      rw [hw] at hi ⊢
      omega
    have hsh : (ruleWidth - 1 ≤ i) = False := by
      rw [hw] at hlt ⊢
      simp
      omega
    rw [hm]
    simp [hsh, Nat.add_comm 1 i]

/-! ## The step, cell by cell -/

/-- The length of a stepped row is the length it started with. -/
theorem length_stepRow (row : List Bool) :
    (stepRow row).length = row.length := by
  simp [stepRow]

/-- Cell `i` of the stepped row, for `i` inside the row. -/
theorem getD_stepRow (row : List Bool) (i : Nat) (h : i < row.length) :
    (stepRow row).getD i false
      = rule110 (row.getD ((i + row.length - 1) % row.length) false)
                (row.getD i false)
                (row.getD ((i + 1) % row.length) false) := by
  simp [stepRow, List.getD_eq_getElem?_getD, h]



/-! ## The correspondence

One packed step is one list step. Everything above exists to make this one
theorem provable; everything below follows from it by induction.
-/

/-- The high bits of an encoded row of the fixed width are absent, in the form
the rotation lemmas ask for. -/
theorem encodeRow_high (row : List Bool) (hlen : row.length = ruleWidth) :
    ∀ j, ruleWidth ≤ j → (encodeRow row).testBit j = false := by
  intro j hj
  refine testBit_encodeRow_high row j ?_
  rw [hlen]
  exact hj

/-- A packed step and a list step are the same row seen two ways. -/
theorem pStep_encodeRow (row : List Bool) (hlen : row.length = ruleWidth) :
    pStep (encodeRow row) = encodeRow (stepRow row) := by
  have hhigh := encodeRow_high row hlen
  refine Nat.eq_of_testBit_eq ?_
  intro i
  rw [pStep, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor,
      Nat.testBit_and, Nat.testBit_and]
  by_cases hi : i < ruleWidth
  · rw [testBit_rowMask_lt i hi, testBit_rotL _ hhigh i hi,
        testBit_rotR _ hhigh i hi, testBit_encodeRow row i,
        testBit_encodeRow row _, testBit_encodeRow row _,
        testBit_encodeRow (stepRow row) i]
    rw [getD_stepRow row i (by rw [hlen]; exact hi), rule110_eq, hlen]
    cases row.getD ((i + ruleWidth - 1) % ruleWidth) false <;>
      cases row.getD i false <;>
      cases row.getD ((i + 1) % ruleWidth) false <;> rfl
  · have hge : ruleWidth ≤ i := by omega
    have hL : (rotL (encodeRow row)).testBit i = false := by
      rw [rotL, Nat.testBit_and, testBit_rowMask]
      simp [hi]
    have hR : (rotR (encodeRow row)).testBit i = false := by
      rw [rotR, Nat.testBit_and, testBit_rowMask]
      simp [hi]
    rw [testBit_rowMask, hL, hR, hhigh i hge,
        testBit_encodeRow_high (stepRow row) i
          (by rw [length_stepRow, hlen]; exact hge)]
    simp [hi]

/-- Iterating the packed step is iterating the list step. -/
theorem pIter_encodeRow (t : Nat) :
    ∀ row : List Bool, row.length = ruleWidth →
      pIter t (encodeRow row) = encodeRow (iterRow t row) := by
  induction t with
  | zero =>
    intro row _
    rfl
  | succ k ih =>
    intro row hlen
    show pIter k (pStep (encodeRow row)) = encodeRow (iterRow k (stepRow row))
    rw [pStep_encodeRow row hlen]
    refine ih (stepRow row) ?_
    rw [length_stepRow, hlen]

/-- The initial row has the fixed width, because it is a map over a range. -/
theorem length_initRowFor (seed : Nat) :
    (initRowFor seed).length = ruleWidth := by
  simp [initRowFor]

theorem impl_correct : ∀ n, impl n = caSpecN n := by
  intro n
  show pIter (caSteps n) (encodeRow (initRowFor (caSeed n)))
      = encodeRow (iterRow (caSteps n) (initRowFor (caSeed n)))
  exact pIter_encodeRow _ _ (length_initRowFor _)

end Submission
