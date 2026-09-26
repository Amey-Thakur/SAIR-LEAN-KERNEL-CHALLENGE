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
width, which `testBit_encodeRow_high` supplies for any encoded row. -/

/-- Bit `i` of `rotL R` is bit `i - 1` of `R`, cyclically. -/
theorem testBit_rotL (R : Nat) (hR : ∀ j, ruleWidth ≤ j → R.testBit j = false)
    (i : Nat) (hi : i < ruleWidth) :
    (rotL R).testBit i = R.testBit ((i + ruleWidth - 1) % ruleWidth) := by
  show (((R <<< 1) ||| (R >>> (ruleWidth - 1))) &&& rowMask).testBit i
      = R.testBit ((i + ruleWidth - 1) % ruleWidth)
  rw [Nat.testBit_and, Nat.testBit_or, testBit_rowMask,
      Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  simp only [hi, decide_true, Bool.and_true]
  match i with
  | 0 =>
    have hz : (0 + ruleWidth - 1) % ruleWidth = ruleWidth - 1 := by decide
    rw [hz]
    show (decide (1 ≤ 0) && R.testBit (0 - 1)) || R.testBit (ruleWidth - 1 + 0)
        = R.testBit (ruleWidth - 1)
    simp
  | k + 1 =>
    have hhigh : R.testBit (ruleWidth - 1 + (k + 1)) = false := by
      refine hR _ ?_
      omega
    have hmod : (k + 1 + ruleWidth - 1) % ruleWidth = k := by
      have : k < ruleWidth := by omega
      omega
    rw [hmod, hhigh]
    show (decide (1 ≤ k + 1) && R.testBit (k + 1 - 1)) || false = R.testBit k
    simp

/-- Bit `i` of `rotR R` is bit `i + 1` of `R`, cyclically. -/
theorem testBit_rotR (R : Nat) (hR : ∀ j, ruleWidth ≤ j → R.testBit j = false)
    (i : Nat) (hi : i < ruleWidth) :
    (rotR R).testBit i = R.testBit ((i + 1) % ruleWidth) := by
  show (((R >>> 1) ||| ((R &&& 1) <<< (ruleWidth - 1))) &&& rowMask).testBit i
      = R.testBit ((i + 1) % ruleWidth)
  rw [Nat.testBit_and, Nat.testBit_or, testBit_rowMask,
      Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.testBit_and]
  simp only [hi, decide_true, Bool.and_true]
  by_cases hlast : i = ruleWidth - 1
  · subst hlast
    have hover : R.testBit (1 + (ruleWidth - 1)) = false := by
      refine hR _ ?_
      omega
    have hmod : (ruleWidth - 1 + 1) % ruleWidth = 0 := by decide
    rw [hmod, hover]
    show false || (decide (ruleWidth - 1 ≤ ruleWidth - 1)
        && (R.testBit (ruleWidth - 1 - (ruleWidth - 1))
            && (1 : Nat).testBit (ruleWidth - 1 - (ruleWidth - 1))))
        = R.testBit 0
    simp
  · have hlt : i < ruleWidth - 1 := by omega
    have hmod : (i + 1) % ruleWidth = i + 1 := by
      refine Nat.mod_eq_of_lt ?_
      omega
    have hshift : (decide (ruleWidth - 1 ≤ i)) = false := by
      simp
      omega
    rw [hmod, hshift]
    show R.testBit (1 + i) || false = R.testBit (i + 1)
    rw [Nat.add_comm 1 i]
    simp

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

end Submission
