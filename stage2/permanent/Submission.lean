import Spec

/-!
# permanent — scan each row once, not once per node

The specification expands the permanent as a depth-first search over injective
column choices, with a bit mask recording the columns already taken. At every
node it does this:

    (List.range width).foldl (fun total j =>
      let entry := row.getD j 0
      if entry = 0 || used.testBit j then total else ...) 0

Two costs compound there, and neither is the search itself.

The matrix is sparse. `permanentEntry` gives a diagonal and exactly two seeded
off-diagonal columns, so a row has at most three non-zero entries, and the fold
looks at all sixteen. And `row.getD j 0` walks the list, so reading column `j`
costs `j` steps: scanning one row is quadratic in the width rather than linear.
Together that is roughly 256 list steps at each node to find three useful ones,
paid again at every node of a depth-16 search.

Both are fixed once, before the search starts, by turning each row into its
list of non-zero `(column, entry)` pairs. That transformation costs one
quadratic scan per row in total, not per node, and the search then touches only
the pairs that can contribute.

Nothing about the traversal changes: same order, same mask, same arithmetic.
The correspondence is `foldl_pairs_eq`, an induction whose step is the
observation the specification already makes, that an entry of zero contributes
nothing.

Core Lean only; the problem package has no Mathlib dependency.
-/

namespace Submission

/-- One cell of a row, kept only when it can contribute. Named rather than
written inline so the correspondence proof can rewrite with it: `simp` will not
reduce a `let` inside a `filterMap` lambda on its own. -/
def cellOf (row : List Nat) (j : Nat) : Option (Nat × Nat) :=
  if row.getD j 0 = 0 then none else some (j, row.getD j 0)

/-- The non-zero cells of a row, with their column indices. -/
def rowPairs (width : Nat) (row : List Nat) : List (Nat × Nat) :=
  (List.range width).filterMap (cellOf row)

/-- The same search, over the sparse rows. -/
def permanentFast (width : Nat) : List (List (Nat × Nat)) → Nat → Nat
  | [], _ => 1
  | ps :: rest, used =>
      ps.foldl (fun total p =>
        if used.testBit p.1 then total
        else total + p.2 * permanentFast width rest (used ||| (1 <<< p.1))) 0

/-! ## The correspondence

The only thing to prove is that dropping the zero cells before the fold gives
the same answer as testing for them inside it. -/

theorem foldl_pairs_eq (width : Nat) (rows : List (List Nat))
    (rowsP : List (List (Nat × Nat))) (row : List Nat) (used : Nat)
    (hrec : ∀ u, permanentFast width rowsP u = permanentRows width rows u) :
    ∀ (cols : List Nat) (acc : Nat),
      (cols.filterMap (cellOf row)).foldl
        (fun total p =>
          if used.testBit p.1 then total
          else total + p.2 * permanentFast width rowsP (used ||| (1 <<< p.1)))
        acc
      = cols.foldl (fun total j =>
          let entry := row.getD j 0
          if entry = 0 || used.testBit j then total
          else total + entry * permanentRows width rows (used ||| (1 <<< j)))
        acc := by
  intro cols
  induction cols with
  | nil =>
    intro acc
    rfl
  | cons j cols ih =>
    intro acc
    by_cases hz : row.getD j 0 = 0
    · -- a zero cell is dropped on the left and skipped on the right
      have hnone : cellOf row j = none := by
        rw [cellOf, if_pos hz]
      rw [List.filterMap_cons_none hnone, List.foldl_cons]
      -- rewrite the condition itself rather than the whole `if`: the guard is
      -- a Bool, so the branch is `cond = true`, and `simp` on the entry alone
      -- does not carry through that coercion
      have hcond : (row.getD j 0 = 0 || used.testBit j) = true := by
        simp [hz]
      rw [hcond, if_true]
      exact ih acc
    · have hsome : cellOf row j = some (j, row.getD j 0) := by
        rw [cellOf, if_neg hz]
      rw [List.filterMap_cons_some hsome, List.foldl_cons, List.foldl_cons]
      -- with a non-zero entry the guard collapses to the mask test, and the
      -- two accumulator steps are then the same term
      have hcond : (row.getD j 0 = 0 || used.testBit j) = used.testBit j := by
        simp [hz]
      rw [hcond, hrec]
      exact ih _

theorem permanentFast_eq (width : Nat) :
    ∀ (rows : List (List Nat)) (used : Nat),
      permanentFast width (rows.map (rowPairs width)) used
        = permanentRows width rows used := by
  intro rows
  induction rows with
  | nil =>
    intro used
    rfl
  | cons row rest ih =>
    intro used
    show (rowPairs width row).foldl _ 0 = _
    rw [permanentRows, rowPairs]
    exact foldl_pairs_eq width rest (rest.map (rowPairs width)) row used ih
      (List.range width) 0

/-! ## The implementation -/

def impl (n : Nat) : Nat :=
  let m := genPermanentMatrix (permanentDimension n) (permanentSeed n)
  permanentFast m.length (m.map (rowPairs m.length)) 0

theorem impl_correct : ∀ n, impl n = permanentSpecN n := by
  intro n
  show permanentFast _ _ 0 = permanentSpec _
  rw [permanentSpec]
  exact permanentFast_eq _ _ 0

end Submission
