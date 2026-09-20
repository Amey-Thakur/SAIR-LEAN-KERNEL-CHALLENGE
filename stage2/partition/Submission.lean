/-
Integer partitions, computed by evaluating the specification's own recurrence
once per cell instead of once per call.

The specification defines `partAux k n` by recursion on the largest allowed
part. Evaluating it directly re-derives the same `partAux k m` along every path
that reaches it: at `n = 36` that is about 128,000 calls for a table with only
1,369 distinct entries.

This submission keeps the recurrence exactly as written and changes only where
the values live. Row `k` is built once, as a list whose `m`-th entry is
`partAux k m`, and row `k+1` reads that row instead of recomputing it. Because
each cell is the specification's own sum with the recursive call replaced by a
lookup, correctness is a congruence: the two agree because the row already
agrees, pointwise, one row down.

Everything below is self-contained. The indexed read, the list builder and
every lemma are defined here rather than imported, so each proof is about the
exact function the kernel reduces.
-/
import Spec

namespace Submission

/-! ## Reading and building a row -/

/-- Indexed read, zero past the end. -/
def nth : List Nat → Nat → Nat
  | [],      _     => 0
  | x :: _,  0     => x
  | _ :: xs, m + 1 => nth xs m

/-- `build f len i = [f i, f (i+1), ..., f (i + len - 1)]`. -/
def build (f : Nat → Nat) : Nat → Nat → List Nat
  | 0,       _ => []
  | len + 1, i => f i :: build f len (i + 1)

theorem nth_build (f : Nat → Nat) (len : Nat) :
    ∀ i m, m < len → nth (build f len i) m = f (i + m) := by
  induction len with
  | zero => intro _ m h; exact absurd h (Nat.not_lt_zero m)
  | succ L ih =>
    intro i m h
    match m with
    | 0 => rfl
    | M + 1 =>
      have hM : M < L := Nat.lt_of_succ_lt_succ h
      have h2 : nth (build f L (i + 1)) M = f (i + 1 + M) := ih (i + 1) M hM
      have harith : i + 1 + M = i + (M + 1) := by omega
      show nth (build f L (i + 1)) M = f (i + (M + 1))
      rw [h2, harith]

/-! ## The sum the specification takes over multiplicities

`specSum g d m` is the body of `partAux (k+1) m` with the recursive call
abstracted out, so that `partAux (k+1) m` and `specSum (partAux k) (k+1) m` are
literally the same term. Keeping this shape is what makes the correctness proof
a congruence rather than a re-derivation of the recurrence. -/

/-- The specification's inner sum, with the recursive call abstracted. -/
def specSum (g : Nat → Nat) (d m : Nat) : Nat :=
  ((List.range (m / d + 1)).map (fun j => g (m - j * d))).foldl (· + ·) 0

/-- Two functions that agree everywhere the sum looks give the same sum. Every
index the sum reads is `m - j * d`, which never exceeds `m`. -/
theorem map_eq_of_agree (f1 f2 : Nat → Nat) (m d : Nat) (h : ∀ i, i ≤ m → f1 i = f2 i) :
    ∀ (l : List Nat), l.map (fun j => f1 (m - j * d)) = l.map (fun j => f2 (m - j * d)) := by
  intro l
  induction l with
  | nil => rfl
  | cons x xs ih =>
    show f1 (m - x * d) :: xs.map (fun j => f1 (m - j * d))
        = f2 (m - x * d) :: xs.map (fun j => f2 (m - j * d))
    rw [h (m - x * d) (Nat.sub_le m (x * d)), ih]

theorem specSum_congr (g1 g2 : Nat → Nat) (d m : Nat) (h : ∀ i, i ≤ m → g1 i = g2 i) :
    specSum g1 d m = specSum g2 d m := by
  show ((List.range (m / d + 1)).map (fun j => g1 (m - j * d))).foldl (· + ·) 0
      = ((List.range (m / d + 1)).map (fun j => g2 (m - j * d))).foldl (· + ·) 0
  rw [map_eq_of_agree g1 g2 m d h]

/-! ## The table -/

/-- Row `0`, held as data. `partAux 0` is already a constant-time match; it is
the rows above it that need to find their values already computed. -/
def baseRow (len : Nat) : List Nat := build (partAux 0) len 0

/-- Row `d`, each entry the specification's sum read off the row below. -/
def nextRow (d : Nat) (prev : List Nat) (len : Nat) : List Nat :=
  build (fun m => specSum (fun i => nth prev i) d m) len 0

/-- Rows `0` through `k`, each holding `len` entries. The row below is named
once, so it is built once. -/
def rows : Nat → Nat → List Nat
  | 0,     len => baseRow len
  | k + 1, len =>
    let prev := rows k len
    nextRow (k + 1) prev len

/-- The partition count. Only entry `n` of row `n` is asked for; the rest of the
table is what makes reaching it cheap. -/
def impl (n : Nat) : Nat := nth (rows n (n + 1)) n

/-! ## Correctness -/

/-- Every entry of every row holds the value the specification gives it. -/
theorem rows_correct (len : Nat) :
    ∀ k m, m < len → nth (rows k len) m = partAux k m := by
  intro k
  induction k with
  | zero =>
    intro m h
    show nth (build (partAux 0) len 0) m = partAux 0 m
    rw [nth_build (partAux 0) len 0 m h, Nat.zero_add]
  | succ K ih =>
    intro m h
    show nth (build (fun m => specSum (fun i => nth (rows K len) i) (K + 1) m) len 0) m
        = partAux (K + 1) m
    rw [nth_build _ len 0 m h, Nat.zero_add]
    show specSum (fun i => nth (rows K len) i) (K + 1) m = specSum (partAux K) (K + 1) m
    exact specSum_congr _ _ (K + 1) m (fun i hi => ih i (Nat.lt_of_le_of_lt hi h))

theorem impl_correct : ∀ n, impl n = partitionSpec n := by
  intro n
  show nth (rows n (n + 1)) n = partAux n n
  exact rows_correct (n + 1) n n (Nat.lt_succ_self n)

end Submission
