/-
Integer partitions, with a whole row of the table carried in one natural number.

The specification's recurrence sums the row below at a fixed stride:

    partAux d m = partAux (d-1) m + partAux (d-1) (m-d) + partAux (d-1) (m-2d) + ...

On a list each of those reads walks the list, so a row costs a traversal per
entry. On a number whose `m`-th field of `w` bits holds the entry for `m`, the
same row is

    R' = R + (R <<< d*w) + (R <<< 2*d*w) + ...

which the kernel performs with a few arithmetic operations on one large
integer, whatever the row's length. At `n = 36` that is 528 operations in place
of roughly 32,000 list steps.

Fields never carry into one another because `w` is wide enough to hold any
entry: `partAux k m` is a sum of at most `m+1` terms each at most `(m+1)^(k-1)`,
so `partAux k m ≤ (m+1)^k ≤ (n+1)^n < 2^w`. That bound is proved below, not
assumed; it is the only thing between this representation and a wrong answer.

Everything is self-contained, so each lemma is about the exact function the
kernel reduces.
-/
import Spec

namespace Submission

/-! ## Small arithmetic facts, proved here rather than named from the library -/

theorem two_pow_pos : ∀ e : Nat, 0 < 2 ^ e := by
  intro e
  induction e with
  | zero => decide
  | succ E ih => rw [Nat.pow_succ]; omega

theorem lt_of_div_eq_zero {m d : Nat} (hd : 0 < d) (h : m / d = 0) : m < d := by
  by_contra hc
  have hge : d ≤ m := Nat.le_of_not_lt hc
  have hstep : m / d = (m - d) / d + 1 := Nat.div_eq_sub_div hd hge
  omega

/-! ## A width wide enough to hold any entry -/

/-- Bit length, driven by fuel so the kernel reduces it structurally. -/
def bitsAux : Nat → Nat → Nat
  | 0,        _     => 0
  | _ + 1,    0     => 0
  | fuel + 1, v + 1 => bitsAux fuel ((v + 1) / 2) + 1

/-- A length with `v < 2 ^ bits v`. -/
def bits (v : Nat) : Nat := bitsAux v v

theorem lt_two_pow_bitsAux : ∀ fuel v, v ≤ fuel → v < 2 ^ bitsAux fuel v := by
  intro fuel
  induction fuel with
  | zero =>
    intro v hv
    have hz : v = 0 := Nat.le_zero.mp hv
    subst hz
    decide
  | succ F ih =>
    intro v hv
    match v with
    | 0 => decide
    | V + 1 =>
      have hhalf : (V + 1) / 2 ≤ F := by omega
      have hrec := ih ((V + 1) / 2) hhalf
      show V + 1 < 2 ^ (bitsAux F ((V + 1) / 2) + 1)
      rw [Nat.pow_succ]
      omega

theorem lt_two_pow_bits (v : Nat) : v < 2 ^ bits v :=
  lt_two_pow_bitsAux v v (Nat.le_refl v)

/-- The field width used for inputs of size `n`. -/
def width (n : Nat) : Nat := n * bits (n + 1) + 1

/-! ## What the specification's sum can reach -/

theorem foldl_add_start : ∀ (xs : List Nat) (a : Nat),
    xs.foldl (· + ·) a = a + xs.foldl (· + ·) 0 := by
  intro xs
  induction xs with
  | nil => intro a; simp
  | cons x xs ih =>
    intro a
    show xs.foldl (· + ·) (a + x) = a + xs.foldl (· + ·) (0 + x)
    rw [ih (a + x), ih (0 + x)]
    omega

theorem sum_map_le (f : Nat → Nat) (C : Nat) (h : ∀ j, f j ≤ C) :
    ∀ (xs : List Nat), (xs.map f).foldl (· + ·) 0 ≤ xs.length * C := by
  intro xs
  induction xs with
  | nil => simp
  | cons x xs ih =>
    show (f x :: xs.map f).foldl (· + ·) 0 ≤ (xs.length + 1) * C
    rw [List.foldl_cons, foldl_add_start, Nat.succ_mul]
    have hx := h x
    omega

theorem partAux_le : ∀ k m, partAux k m ≤ (m + 1) ^ k := by
  intro k
  induction k with
  | zero =>
    intro m
    match m with
    | 0 => exact Nat.le_refl 1
    | _ + 1 => exact Nat.zero_le 1
  | succ K ih =>
    intro m
    have hterm : ∀ j, partAux K (m - j * (K + 1)) ≤ (m + 1) ^ K := fun j =>
      Nat.le_trans (ih (m - j * (K + 1))) (Nat.pow_le_pow_left (by omega) K)
    have hsum := sum_map_le _ _ hterm (List.range (m / (K + 1) + 1))
    rw [List.length_range] at hsum
    have hcount : (m / (K + 1) + 1) * (m + 1) ^ K ≤ (m + 1) * (m + 1) ^ K :=
      Nat.mul_le_mul_right _ (by omega)
    show ((List.range (m / (K + 1) + 1)).map
      (fun j => partAux K (m - j * (K + 1)))).foldl (· + ·) 0 ≤ (m + 1) ^ (K + 1)
    rw [Nat.pow_succ, Nat.mul_comm ((m + 1) ^ K) (m + 1)]
    exact Nat.le_trans hsum hcount

/-- Every entry the table for `n` can hold fits in one field. -/
theorem entry_lt (n k m : Nat) (hk : k ≤ n) (hm : m ≤ n) :
    partAux k m < 2 ^ width n := by
  have hb : n + 1 < 2 ^ bits (n + 1) := lt_two_pow_bits (n + 1)
  have h1 : partAux k m ≤ (m + 1) ^ k := partAux_le k m
  have h2 : (m + 1) ^ k ≤ (n + 1) ^ n :=
    Nat.le_trans (Nat.pow_le_pow_left (by omega) k) (Nat.pow_le_pow_right (by omega) hk)
  have h3 : (n + 1) ^ n ≤ (2 ^ bits (n + 1)) ^ n := Nat.pow_le_pow_left (by omega) n
  have h4 : (2 ^ bits (n + 1)) ^ n = 2 ^ (n * bits (n + 1)) := by
    rw [← Nat.pow_mul, Nat.mul_comm]
  have h5 : 2 ^ width n = 2 ^ (n * bits (n + 1)) * 2 := by
    show 2 ^ (n * bits (n + 1) + 1) = 2 ^ (n * bits (n + 1)) * 2
    rw [Nat.pow_succ]
  have h6 : 0 < 2 ^ (n * bits (n + 1)) := two_pow_pos _
  omega

/-! ## Digits

`pack w f len` is the number whose field `m` holds `f m`, for `m < len`. It is a
weighted sum, so adding two packed rows adds their fields with no side
condition; a field only has to fit in `w` bits when one is read back out. -/

def pack (w : Nat) (f : Nat → Nat) : Nat → Nat
  | 0       => 0
  | len + 1 => f 0 + 2 ^ w * pack w (fun m => f (m + 1)) len

/-- A row function cut off past the last field the row holds. -/
def cut (L : Nat) (f : Nat → Nat) : Nat → Nat := fun m => if m < L then f m else 0

theorem pack_congr (w : Nat) : ∀ (len : Nat) (f g : Nat → Nat),
    (∀ m, m < len → f m = g m) → pack w f len = pack w g len := by
  intro len
  induction len with
  | zero => intro _ _ _; rfl
  | succ L ih =>
    intro f g h
    show f 0 + 2 ^ w * pack w (fun m => f (m + 1)) L
        = g 0 + 2 ^ w * pack w (fun m => g (m + 1)) L
    rw [h 0 (by omega), ih _ _ (fun m hm => h (m + 1) (by omega))]

theorem pack_zero (w : Nat) : ∀ (len : Nat) (f : Nat → Nat),
    (∀ m, m < len → f m = 0) → pack w f len = 0 := by
  intro len
  induction len with
  | zero => intro _ _; rfl
  | succ L ih =>
    intro f h
    show f 0 + 2 ^ w * pack w (fun m => f (m + 1)) L = 0
    rw [h 0 (by omega), ih _ (fun m hm => h (m + 1) (by omega))]

theorem pack_add (w : Nat) : ∀ (len : Nat) (f g : Nat → Nat),
    pack w f len + pack w g len = pack w (fun m => f m + g m) len := by
  intro len
  induction len with
  | zero => intro _ _; rfl
  | succ L ih =>
    intro f g
    show (f 0 + 2 ^ w * pack w (fun m => f (m + 1)) L)
        + (g 0 + 2 ^ w * pack w (fun m => g (m + 1)) L)
        = (f 0 + g 0) + 2 ^ w * pack w (fun m => f (m + 1) + g (m + 1)) L
    rw [← ih (fun m => f (m + 1)) (fun m => g (m + 1)), Nat.mul_add]
    omega

/-- Extending a row past its last non-zero field does not change the number. -/
theorem pack_extend (w : Nat) : ∀ (len extra : Nat) (f : Nat → Nat),
    (∀ m, len ≤ m → f m = 0) → pack w f (len + extra) = pack w f len := by
  intro len
  induction len with
  | zero =>
    intro extra f h
    exact pack_zero w extra f (fun m _ => h m (Nat.zero_le m))
  | succ L ih =>
    intro extra f h
    show f 0 + 2 ^ w * pack w (fun m => f (m + 1)) (L + extra)
        = f 0 + 2 ^ w * pack w (fun m => f (m + 1)) L
    rw [ih extra (fun m => f (m + 1)) (fun m hm => h (m + 1) (by omega))]

/-- Fields that fit in `w` bits are what make the row occupy `w * len` bits. -/
theorem pack_lt (w : Nat) : ∀ (len : Nat) (f : Nat → Nat),
    (∀ m, m < len → f m < 2 ^ w) → pack w f len < 2 ^ (w * len) := by
  intro len
  induction len with
  | zero => intro _ _; decide
  | succ L ih =>
    intro f h
    have hrest := ih (fun m => f (m + 1)) (fun m hm => h (m + 1) (by omega))
    have h0 := h 0 (by omega)
    have hpow : 2 ^ (w * (L + 1)) = 2 ^ w * 2 ^ (w * L) := by
      rw [Nat.mul_add, Nat.mul_one, Nat.pow_add]
    have hstep : 2 ^ w * (pack w (fun m => f (m + 1)) L + 1) ≤ 2 ^ w * 2 ^ (w * L) :=
      Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_add, Nat.mul_one] at hstep
    show f 0 + 2 ^ w * pack w (fun m => f (m + 1)) L < 2 ^ (w * (L + 1))
    rw [hpow]
    omega

/-- A row splits into its bottom `len` fields and everything above them. -/
theorem pack_split (w : Nat) : ∀ (len extra : Nat) (f : Nat → Nat),
    pack w f (len + extra)
      = pack w f len + 2 ^ (w * len) * pack w (fun m => f (m + len)) extra := by
  intro len
  induction len with
  | zero =>
    intro extra f
    show pack w f extra = 0 + 2 ^ (w * 0) * pack w (fun m => f (m + 0)) extra
    rw [Nat.mul_zero, Nat.pow_zero, Nat.one_mul, Nat.zero_add]
    exact pack_congr w extra f (fun m => f (m + 0)) (fun m _ => rfl)
  | succ L ih =>
    intro extra f
    have hpow : 2 ^ (w * (L + 1)) = 2 ^ w * 2 ^ (w * L) := by
      rw [Nat.mul_add, Nat.mul_one, Nat.pow_add]
    have hshift : ∀ m, f (m + (L + 1)) = (fun i => f (i + 1)) (m + L) := by
      intro m
      show f (m + (L + 1)) = f (m + L + 1)
      rw [Nat.add_assoc]
    show f 0 + 2 ^ w * pack w (fun m => f (m + 1)) (L + extra)
        = (f 0 + 2 ^ w * pack w (fun m => f (m + 1)) L)
          + 2 ^ (w * (L + 1)) * pack w (fun m => f (m + (L + 1))) extra
    rw [ih extra (fun m => f (m + 1)), hpow,
        pack_congr w extra (fun m => f (m + (L + 1))) (fun m => f (m + L + 1))
          (fun m _ => hshift m),
        Nat.mul_add, Nat.mul_assoc]

/-- Cutting a longer row down to its bottom `len` fields. -/
theorem pack_trunc (w len extra : Nat) (f : Nat → Nat)
    (hb : ∀ m, m < len → f m < 2 ^ w) :
    pack w f (len + extra) % 2 ^ (w * len) = pack w f len := by
  rw [pack_split w len extra f, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (pack_lt w len f hb)]

/-- Reading field `m` back out: shift it down and mask it off. -/
theorem pack_get (w len m : Nat) (f : Nat → Nat)
    (hb : ∀ i, i < len → f i < 2 ^ w) (hm : m < len) :
    pack w f len / 2 ^ (w * m) % 2 ^ w = f m := by
  have hlen : m + (len - m) = len := by omega
  have hsplit := pack_split w m (len - m) f
  rw [hlen] at hsplit
  have hlow : pack w f m < 2 ^ (w * m) := pack_lt w m f (fun i hi => hb i (by omega))
  have hpos : 0 < 2 ^ (w * m) := two_pow_pos _
  have hrest : len - m = (len - m - 1) + 1 := by omega
  rw [hsplit, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt hlow, Nat.zero_add, hrest]
  show (f (0 + m) + 2 ^ w * pack w (fun i => f (i + 1 + m)) (len - m - 1)) % 2 ^ w
      = f m
  rw [Nat.zero_add, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hb m hm)]

/-! ## A row step

`sweep s R J` is `R + (R <<< s) + ... + (R <<< J*s)`, one addition and one shift
per term. `sweepF` is the same thing on fields, and the two agree field by
field. -/

def sweep (s R : Nat) : Nat → Nat
  | 0     => R
  | J + 1 => R + (sweep s R J) <<< s

def sweepF (d : Nat) (f : Nat → Nat) : Nat → Nat → Nat
  | 0,     m => f m
  | J + 1, m => f m + (if m < d then 0 else sweepF d f J (m - d))

theorem sweepF_congr (d : Nat) (f g : Nat → Nat) :
    ∀ J m, (∀ i, i ≤ m → f i = g i) → sweepF d f J m = sweepF d g J m := by
  intro J
  induction J with
  | zero => intro m h; exact h m (Nat.le_refl m)
  | succ Jp ih =>
    intro m h
    show f m + (if m < d then 0 else sweepF d f Jp (m - d))
        = g m + (if m < d then 0 else sweepF d g Jp (m - d))
    rw [h m (Nat.le_refl m)]
    by_cases hlt : m < d
    · rw [if_pos hlt, if_pos hlt]
    · rw [if_neg hlt, if_neg hlt, ih (m - d) (fun i hi => h i (by omega))]

theorem sweepF_zero_above (d : Nat) (f : Nat → Nat) (L : Nat)
    (hz : ∀ m, L ≤ m → f m = 0) :
    ∀ J m, L + J * d ≤ m → sweepF d f J m = 0 := by
  intro J
  induction J with
  | zero => intro m hm; exact hz m (by omega)
  | succ Jp ih =>
    intro m hm
    have hexp : L + (Jp + 1) * d = L + Jp * d + d := by rw [Nat.succ_mul]; omega
    rw [hexp] at hm
    show f m + (if m < d then 0 else sweepF d f Jp (m - d)) = 0
    rw [hz m (by omega), if_neg (by omega), ih (m - d) (by omega)]

theorem sweep_pack (w d : Nat) :
    ∀ (J L : Nat) (f : Nat → Nat), (∀ m, L ≤ m → f m = 0) →
      sweep (w * d) (pack w f L) J = pack w (sweepF d f J) (L + J * d) := by
  intro J
  induction J with
  | zero =>
    intro L f _
    show pack w f L = pack w (sweepF d f 0) (L + 0 * d)
    rw [Nat.zero_mul, Nat.add_zero]
    exact pack_congr w L f (sweepF d f 0) (fun _ _ => rfl)
  | succ Jp ih =>
    intro L f hz
    have hprev := ih L f hz
    have hshift : ∀ (g : Nat → Nat) (len : Nat),
        pack w g len * 2 ^ (w * d)
          = pack w (fun m => if m < d then 0 else g (m - d)) (len + d) := by
      intro g len
      have hsplit := pack_split w d len (fun m => if m < d then 0 else g (m - d))
      have hlow : pack w (fun m => if m < d then 0 else g (m - d)) d = 0 :=
        pack_zero w d _ (fun m hm => if_pos hm)
      have hhigh : ∀ m, (if m + d < d then 0 else g (m + d - d)) = g m := by
        intro m
        rw [if_neg (by omega)]
        congr 1
        omega
      rw [Nat.add_comm len d, hsplit, hlow, Nat.zero_add,
          pack_congr w len (fun m => (if m + d < d then 0 else g (m + d - d))) g
            (fun m _ => hhigh m),
          Nat.mul_comm]
    have hzp : ∀ m, L + Jp * d ≤ m → sweepF d f Jp m = 0 :=
      sweepF_zero_above d f L hz Jp
    have hlen : L + Jp * d + d = L + (Jp + 1) * d := by rw [Nat.succ_mul]; omega
    have hext : pack w f L = pack w f (L + (Jp + 1) * d) :=
      (pack_extend w L ((Jp + 1) * d) f hz).symm
    show pack w f L + (sweep (w * d) (pack w f L) Jp) <<< (w * d)
        = pack w (sweepF d f (Jp + 1)) (L + (Jp + 1) * d)
    rw [hprev, Nat.shiftLeft_eq, hshift (sweepF d f Jp) (L + Jp * d), hlen, hext,
        pack_add]
    exact pack_congr w _ _ _ (fun _ _ => rfl)

/-! ## The specification's sum, reached by the sweep -/

def specSum (g : Nat → Nat) (d m : Nat) : Nat :=
  ((List.range (m / d + 1)).map (fun j => g (m - j * d))).foldl (· + ·) 0

theorem specSum_lt (g : Nat → Nat) (d m : Nat) (h : m < d) : specSum g d m = g m := by
  have hdiv : m / d = 0 := Nat.div_eq_of_lt h
  show ((List.range (m / d + 1)).map (fun j => g (m - j * d))).foldl (· + ·) 0 = g m
  rw [hdiv]
  simp

theorem specSum_ge (g : Nat → Nat) (d m : Nat) (hd : 0 < d) (h : d ≤ m) :
    specSum g d m = g m + specSum g d (m - d) := by
  have hdiv : m / d = (m - d) / d + 1 := Nat.div_eq_sub_div hd h
  have hmap : ∀ (l : List Nat),
      l.map (fun j => g (m - Nat.succ j * d)) = l.map (fun j => g (m - d - j * d)) := by
    intro l
    induction l with
    | nil => rfl
    | cons x xs ihl =>
      have hx : m - Nat.succ x * d = m - d - x * d := by rw [Nat.succ_mul]; omega
      show g (m - Nat.succ x * d) :: xs.map (fun j => g (m - Nat.succ j * d))
          = g (m - d - x * d) :: xs.map (fun j => g (m - d - j * d))
      rw [hx, ihl]
  show ((List.range (m / d + 1)).map (fun j => g (m - j * d))).foldl (· + ·) 0
      = g m + ((List.range ((m - d) / d + 1)).map
          (fun j => g (m - d - j * d))).foldl (· + ·) 0
  rw [hdiv, List.range_succ_eq_map, List.map_cons, List.map_map]
  show (g (m - 0 * d) :: ((List.range ((m - d) / d + 1)).map
      (fun j => g (m - Nat.succ j * d)))).foldl (· + ·) 0
      = g m + ((List.range ((m - d) / d + 1)).map
          (fun j => g (m - d - j * d))).foldl (· + ·) 0
  rw [hmap, List.foldl_cons, foldl_add_start]
  simp

theorem sweepF_eq_specSum (d : Nat) (hd : 0 < d) (g : Nat → Nat) :
    ∀ J m, m / d ≤ J → sweepF d g J m = specSum g d m := by
  intro J
  induction J with
  | zero =>
    intro m hm
    have hlt : m < d := lt_of_div_eq_zero hd (Nat.le_zero.mp hm)
    show g m = specSum g d m
    rw [specSum_lt g d m hlt]
  | succ Jp ih =>
    intro m hm
    show g m + (if m < d then 0 else sweepF d g Jp (m - d)) = specSum g d m
    by_cases hlt : m < d
    · rw [if_pos hlt, specSum_lt g d m hlt]
    · have hge : d ≤ m := Nat.le_of_not_lt hlt
      have hstep : m / d = (m - d) / d + 1 := Nat.div_eq_sub_div hd hge
      rw [if_neg hlt, ih (m - d) (by omega), specSum_ge g d m hd hge]

/-! ## The table -/

/-- Rows `0` through `k`, each held as one number of `n+1` fields. -/
def rowsP (n : Nat) : Nat → Nat
  | 0     => 1
  | k + 1 =>
    let prev := rowsP n k
    sweep (width n * (k + 1)) prev (n / (k + 1)) % (1 <<< (width n * (n + 1)))

/-- The partition count: field `n` of row `n`. -/
def impl (n : Nat) : Nat :=
  rowsP n n / (1 <<< (width n * n)) % (1 <<< width n)

/-! ## Correctness -/

theorem rowsP_correct (n : Nat) : ∀ k, k ≤ n →
    rowsP n k = pack (width n) (cut (n + 1) (partAux k)) (n + 1) := by
  intro k
  induction k with
  | zero =>
    intro _
    have h0 : cut (n + 1) (partAux 0) 0 = 1 := by
      show (if 0 < n + 1 then partAux 0 0 else 0) = 1
      rw [if_pos (by omega)]
    have hrest : ∀ m, m < n → cut (n + 1) (partAux 0) (m + 1) = 0 := by
      intro m _
      show (if m + 1 < n + 1 then partAux 0 (m + 1) else 0) = 0
      by_cases hc : m + 1 < n + 1
      · rw [if_pos hc]
      · rw [if_neg hc]
    show (1 : Nat) = cut (n + 1) (partAux 0) 0
        + 2 ^ width n * pack (width n) (fun m => cut (n + 1) (partAux 0) (m + 1)) n
    rw [h0, pack_zero (width n) n _ hrest, Nat.mul_zero]
  | succ K ih =>
    intro hK
    have hKn : K ≤ n := by omega
    have hd : 0 < K + 1 := Nat.succ_pos K
    have hprev := ih hKn
    have hz : ∀ m, n + 1 ≤ m → cut (n + 1) (partAux K) m = 0 := by
      intro m hm
      show (if m < n + 1 then partAux K m else 0) = 0
      rw [if_neg (by omega)]
    have hcell : ∀ m, m < n + 1 →
        sweepF (K + 1) (cut (n + 1) (partAux K)) (n / (K + 1)) m = partAux (K + 1) m := by
      intro m hm
      have hagree : ∀ i, i ≤ m → cut (n + 1) (partAux K) i = partAux K i := by
        intro i hi
        show (if i < n + 1 then partAux K i else 0) = partAux K i
        rw [if_pos (by omega)]
      have hJm : m / (K + 1) ≤ n / (K + 1) := Nat.div_le_div_right (by omega)
      rw [sweepF_congr (K + 1) _ _ (n / (K + 1)) m hagree,
          sweepF_eq_specSum (K + 1) hd (partAux K) (n / (K + 1)) m hJm]
    have hbound : ∀ m, m < n + 1 →
        sweepF (K + 1) (cut (n + 1) (partAux K)) (n / (K + 1)) m < 2 ^ width n := by
      intro m hm
      rw [hcell m hm]
      exact entry_lt n (K + 1) m hK (by omega)
    have hmod : (1 : Nat) <<< (width n * (n + 1)) = 2 ^ (width n * (n + 1)) := by
      rw [Nat.shiftLeft_eq, Nat.one_mul]
    show sweep (width n * (K + 1)) (rowsP n K) (n / (K + 1))
          % (1 <<< (width n * (n + 1)))
        = pack (width n) (cut (n + 1) (partAux (K + 1))) (n + 1)
    rw [hprev, sweep_pack (width n) (K + 1) (n / (K + 1)) (n + 1) _ hz, hmod,
        pack_trunc (width n) (n + 1) (n / (K + 1) * (K + 1)) _ hbound]
    refine pack_congr (width n) (n + 1) _ _ (fun m hm => ?_)
    rw [hcell m hm]
    show partAux (K + 1) m = (if m < n + 1 then partAux (K + 1) m else 0)
    rw [if_pos hm]

theorem impl_correct : ∀ n, impl n = partitionSpec n := by
  intro n
  have hrow := rowsP_correct n n (Nat.le_refl n)
  have hb : ∀ m, m < n + 1 → cut (n + 1) (partAux n) m < 2 ^ width n := by
    intro m hm
    show (if m < n + 1 then partAux n m else 0) < 2 ^ width n
    rw [if_pos hm]
    exact entry_lt n n m (Nat.le_refl n) (by omega)
  have h1 : (1 : Nat) <<< (width n * n) = 2 ^ (width n * n) := by
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  have h2 : (1 : Nat) <<< width n = 2 ^ width n := by
    rw [Nat.shiftLeft_eq, Nat.one_mul]
  show rowsP n n / (1 <<< (width n * n)) % (1 <<< width n) = partAux n n
  rw [h1, h2, hrow, pack_get (width n) (n + 1) n _ hb (by omega)]
  show (if n < n + 1 then partAux n n else 0) = partAux n n
  rw [if_pos (by omega)]

end Submission
