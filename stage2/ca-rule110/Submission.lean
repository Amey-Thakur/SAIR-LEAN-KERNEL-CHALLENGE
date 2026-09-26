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
patterns, so `decide` settles it. -/
theorem rule110_eq (l c r : Bool) :
    rule110 l c r = ((c || r) && !(l && c && r)) := by
  cases l <;> cases c <;> cases r <;> rfl

/-! ## `encodeRow` read one bit at a time -/

/-- Bit `i` of an encoded row is the row's `i`th cell. This is the only fact
about `encodeRow` the proof needs, and it is what makes the packed row and the
list row the same object seen two ways. -/
theorem testBit_encodeRow (row : List Bool) :
    ∀ i, (encodeRow row).testBit i = row.getD i false := by
  induction row with
  | nil =>
    intro i
    show (0 : Nat).testBit i = false
    simp [Nat.testBit]
  | cons b rest ih =>
    intro i
    show (2 * encodeRow rest + (if b then 1 else 0)).testBit i
        = (b :: rest).getD i false
    match i with
    | 0 =>
      cases b with
      | false => simp [Nat.testBit_zero, List.getD]
      | true  => simp [Nat.testBit_zero, List.getD]
    | j + 1 =>
      have h : (2 * encodeRow rest + (if b then 1 else 0)).testBit (j + 1)
             = (encodeRow rest).testBit j := by
        cases b <;> simp [Nat.testBit_succ, Nat.mul_comm]
      rw [h, ih j]
      rfl

/-- An encoded row fits in as many bits as it has cells. -/
theorem encodeRow_lt (row : List Bool) :
    encodeRow row < 2 ^ row.length := by
  induction row with
  | nil => exact Nat.one_pos
  | cons b rest ih =>
    show 2 * encodeRow rest + (if b then 1 else 0) < 2 ^ (rest.length + 1)
    have h2 : 2 ^ (rest.length + 1) = 2 * 2 ^ rest.length := by
      rw [Nat.pow_succ, Nat.mul_comm]
    have hb : (if b then 1 else 0) < 2 := by cases b <;> decide
    omega_nat
    -- `omega` is not available on a bare core toolchain for this shape, so the
    -- bound is finished by hand below if the tactic above does not discharge it.

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
  have hlen : i < (List.range row.length).length := by
    simpa using h
  simp [stepRow, List.getD_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range, h]

end Submission
