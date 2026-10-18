import Spec

/-!
# The foundation for the lane-packed initial row

`lanes.py` settles the algorithm: give every cell a lane inside one `Nat`, run
the whole 32-bit mixing hash on all 256 cells at once, then gather one bit per
lane back down. What is left is the proof.

Lanes are assembled with `+`, not `|||`. The first version of this file used
`|||`, because `Nat.testBit_or` turns a bit of the whole into a disjunction of
bits of the parts with no carry reasoning at all, which made `testBit_pack`
short. It is the wrong choice all the same: the mixing hash multiplies, and
multiplication distributes over `+` and not over `|||`. Core Lean has no
`or_eq_add_of_and_eq_zero` to convert between them, so the sum is the
definition and the no-carry argument is paid once, here, where the lane bound
`f k < 2 ^ w` does the work.

This file is not the submission. It compiles on its own in CI so a wrong
lemma name or a broken induction is reported by itself, and so the live entry
is never at risk while this is being built.
-/

-- names this file is unsure of, reported by themselves
#check @Nat.testBit_mod_two_pow
#check @Nat.div_eq_of_lt
#check @Nat.pow_add
#check @Nat.succ_mul
#check @Nat.mul_le_mul_right
#check @Nat.add_mul_mod_self_right
#check @Nat.add_mul_div_right
#check @Nat.mod_eq_of_lt
#check @Nat.eq_of_testBit_eq
#check @Nat.div_add_mod
#check @Nat.div_lt_iff_lt_mul
#check @Nat.mod_lt
#check @Nat.mul_right_comm
#check @Nat.mul_left_comm
#check @List.range_succ
#check @List.map_append
#check @List.foldr_append
#check @List.length_map
#check @List.length_range
#check @Nat.testBit_zero
#check @Nat.testBit_succ
#check @Nat.pow_succ
#check @Nat.testBit_and
#check @Nat.testBit_xor
#check @Nat.testBit_two_pow_sub_one
#check @Nat.testBit_shiftRight
#check @Nat.xor_lt_two_pow
#check @Nat.and_lt_two_pow
#check @Nat.shiftRight_le
#check @Nat.mul_mod

namespace Lane

/-- `n` lanes of width `w`, lane `k` holding `f k`. -/
def pack (w : Nat) (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => pack w f k + f k * 2 ^ (w * k)

/-- A value below `2 ^ w` has no bits at or above `w`. The core lemma gives
this only at the index `w` itself. -/
theorem testBit_eq_false_of_lt_pow {x w i : Nat} (hx : x < 2 ^ w) (hi : w ≤ i) :
    x.testBit i = false := by
  have h2 : (2 : Nat) ^ w ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) hi
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx h2)

/-- `n` lanes of width `w` occupy `w * n` bits. This is what stops a lane
carrying into its neighbour. -/
theorem pack_lt (w : Nat) (f : Nat → Nat) (hf : ∀ k, f k < 2 ^ w) :
    ∀ n, pack w f n < 2 ^ (w * n) := by
  intro n
  induction n with
  | zero => simp [pack]
  | succ k ih =>
    have hstep : w * (k + 1) = w * k + w := Nat.mul_succ w k
    have hpow : (2 : Nat) ^ (w * k + w) = 2 ^ (w * k) * 2 ^ w := Nat.pow_add 2 _ _
    have hfk : f k + 1 ≤ 2 ^ w := hf k
    have hmul : (f k + 1) * 2 ^ (w * k) ≤ 2 ^ w * 2 ^ (w * k) :=
      Nat.mul_le_mul_right _ hfk
    have hexp : (f k + 1) * 2 ^ (w * k) = f k * 2 ^ (w * k) + 2 ^ (w * k) :=
      Nat.succ_mul (f k) (2 ^ (w * k))
    have hcomm : (2 : Nat) ^ w * 2 ^ (w * k) = 2 ^ (w * k) * 2 ^ w :=
      Nat.mul_comm _ _
    rw [pack, hstep, hpow]
    omega

/-- The lemma everything else rests on: a bit inside lane `i` of the packed
number is that bit of lane `i`'s value. -/
theorem testBit_pack (w : Nat) (f : Nat → Nat) (hf : ∀ k, f k < 2 ^ w) :
    ∀ n i b, b < w → i < n →
      (pack w f n).testBit (w * i + b) = (f i).testBit b := by
  intro n
  induction n with
  | zero => intro _ _ _ hin; omega
  | succ k ih =>
    intro i b hb hin
    rcases Nat.lt_or_ge i k with hlt | hge
    · -- the bit sits in an earlier lane, below everything the new term adds
      have hlow : w * i + b < w * k := by
        have h1 : w * (i + 1) ≤ w * k := Nat.mul_le_mul_left w hlt
        have h2 : w * (i + 1) = w * i + w := Nat.mul_succ w i
        omega
      -- `testBit_mod_two_pow` states the masked read, so the new lane is
      -- removed by taking the sum modulo the top of the earlier lanes
      have hmod : (pack w f k + f k * 2 ^ (w * k)) % 2 ^ (w * k) = pack w f k := by
        rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (pack_lt w f hf k)]
      have hbit := Nat.testBit_mod_two_pow
        (pack w f k + f k * 2 ^ (w * k)) (w * k) (w * i + b)
      have hdec : decide (w * i + b < w * k) = true := by simp [hlow]
      rw [hmod, hdec, Bool.true_and] at hbit
      rw [pack, ← hbit]
      exact ih i b hb hlt
    · -- the bit sits in the newest lane, and the earlier ones are all below it
      have hik : i = k := by omega
      subst hik
      have hdiv : (pack w f i + f i * 2 ^ (w * i)) / 2 ^ (w * i) = f i := by
        rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos (w * i)),
            Nat.div_eq_of_lt (pack_lt w f hf i), Nat.zero_add]
      have hshift := Nat.testBit_shiftRight (i := w * i) (j := b)
        (pack w f i + f i * 2 ^ (w * i))
      rw [Nat.shiftRight_eq_div_pow, hdiv] at hshift
      rw [pack]
      exact hshift.symm

/-! ## The lane algebra

Two shapes of lemma, and the split between them is the whole design.

`*` and `+` mix bits between positions, so they are handled at the level of
the packing itself, where distributivity does the work and no bound on the
lanes is needed. `^^^`, `&&&` and `>>>` do not mix bits, so they are handled
one bit at a time by the core `testBit` lemmas and need nothing new here.
`testBit_pack` above is the hinge between the two views.
-/

/-- A scalar multiplies every lane, with no side condition whatever. The
lanes are a sum precisely so that this is true: `*` distributes over `+`,
and Core Lean has no lemma that would let it distribute over `|||`. -/
theorem pack_mul (w : Nat) (f : Nat → Nat) (c : Nat) :
    ∀ n, pack w f n * c = pack w (fun k => f k * c) n := by
  intro n
  induction n with
  | zero => simp [pack]
  | succ k ih =>
    show (pack w f k + f k * 2 ^ (w * k)) * c
        = pack w (fun j => f j * c) k + f k * c * 2 ^ (w * k)
    rw [Nat.add_mul, ih, Nat.mul_right_comm]

/-- Two packings add lane by lane, again with no side condition. The sum of
two lanes may well overflow `2 ^ w`; this says only that the arithmetic is
faithful, and a bound is reimposed where one is needed. -/
theorem pack_add (w : Nat) (f g : Nat → Nat) :
    ∀ n, pack w f n + pack w g n = pack w (fun k => f k + g k) n := by
  intro n
  induction n with
  | zero => simp [pack]
  | succ k ih =>
    show pack w f k + f k * 2 ^ (w * k) + (pack w g k + g k * 2 ^ (w * k))
        = pack w (fun j => f j + g j) k + (f k + g k) * 2 ^ (w * k)
    rw [← ih, Nat.add_mul]
    omega

/-- Extensionality in the lane view: two numbers that fit in `n` lanes are
equal as soon as their lanes agree. This is what turns a value built by
shifting and masking back into a packing, which is the only way `pack_mul`
can then be applied to it. -/
theorem eq_of_lanes {w n x y : Nat} (hw : 0 < w)
    (hx : x < 2 ^ (w * n)) (hy : y < 2 ^ (w * n))
    (h : ∀ i b, i < n → b < w →
      x.testBit (w * i + b) = y.testBit (w * i + b)) :
    x = y := by
  apply Nat.eq_of_testBit_eq
  intro j
  rcases Nat.lt_or_ge j (w * n) with hj | hj
  · -- inside the lanes: name the lane and the offset by division
    have hd : w * (j / w) + j % w = j := Nat.div_add_mod j w
    have hb : j % w < w := Nat.mod_lt _ hw
    have hi : j / w < n := by
      rw [Nat.div_lt_iff_lt_mul hw, Nat.mul_comm]
      exact hj
    rw [← hd]
    exact h _ _ hi hb
  · -- above the lanes: both sides are zero, by the bound each one carries
    rw [testBit_eq_false_of_lt_pow hx hj, testBit_eq_false_of_lt_pow hy hj]

/-! ## Masking, xor and shifting, one lane at a time

These three are the whole bit-level toolkit, and between them they cover
every operation `caMix32` performs and every operation the gather performs.
Each is proved the same way: `eq_of_lanes` reduces the claim to one bit of
one lane, `testBit_pack` turns each packing into its lane, and a core
`testBit` lemma finishes it.

The mask is itself a packing, of the constant `2 ^ m - 1`. That is the point:
a mask written as one `Nat` literal would not be lane-local, and `% 2 ^ m` on
the whole packed number would clear every lane but the lowest.
-/

/-- Masking to `m` bits keeps each lane modulo `2 ^ m`. -/
theorem pack_and_mask {w m n : Nat} (f : Nat → Nat) (hw : 0 < w) (hm : m ≤ w)
    (hf : ∀ k, f k < 2 ^ w) :
    pack w f n &&& pack w (fun _ => 2 ^ m - 1) n
      = pack w (fun k => f k % 2 ^ m) n := by
  have hle : (2 : Nat) ^ m ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) hm
  have hmask : ∀ _ : Nat, (2 : Nat) ^ m - 1 < 2 ^ w := by
    intro _
    have := Nat.two_pow_pos m
    omega
  have hres : ∀ k, f k % 2 ^ m < 2 ^ w := fun k =>
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos m)) hle
  refine eq_of_lanes hw
    (Nat.lt_of_le_of_lt (Nat.and_le_left) (pack_lt w f hf n))
    (pack_lt w _ hres n) ?_
  intro i b hin hbw
  rw [Nat.testBit_and,
      testBit_pack w f hf n i b hbw hin,
      testBit_pack w _ hmask n i b hbw hin,
      testBit_pack w _ hres n i b hbw hin,
      Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
  exact Bool.and_comm _ _

/-- Exclusive or acts lane by lane. -/
theorem pack_xor {w n : Nat} (f g : Nat → Nat) (hw : 0 < w)
    (hf : ∀ k, f k < 2 ^ w) (hg : ∀ k, g k < 2 ^ w) :
    pack w f n ^^^ pack w g n = pack w (fun k => f k ^^^ g k) n := by
  have hres : ∀ k, (f k ^^^ g k) < 2 ^ w := fun k =>
    Nat.xor_lt_two_pow (hf k) (hg k)
  refine eq_of_lanes hw
    (Nat.xor_lt_two_pow (pack_lt w f hf n) (pack_lt w g hg n))
    (pack_lt w _ hres n) ?_
  intro i b hin hbw
  rw [Nat.testBit_xor,
      testBit_pack w f hf n i b hbw hin,
      testBit_pack w g hg n i b hbw hin,
      testBit_pack w _ hres n i b hbw hin,
      Nat.testBit_xor]

/-- A right shift of the whole packing, masked back to `m` bits, is a right
shift inside every lane. The mask is what makes this true rather than nearly
true: shifting right by `s` drags the bottom `s` bits of lane `k + 1` into
the top of lane `k`, and `m + s ≤ w` is exactly the condition that the mask
discards them. -/
theorem pack_shiftRight_and_mask {w m s n : Nat} (f : Nat → Nat) (hw : 0 < w)
    (hms : m + s ≤ w) (hf : ∀ k, f k < 2 ^ w) :
    (pack w f n >>> s) &&& pack w (fun _ => 2 ^ m - 1) n
      = pack w (fun k => (f k >>> s) % 2 ^ m) n := by
  have hle : (2 : Nat) ^ m ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) (by omega)
  have hmask : ∀ _ : Nat, (2 : Nat) ^ m - 1 < 2 ^ w := by
    intro _
    have := Nat.two_pow_pos m
    omega
  have hres : ∀ k, (f k >>> s) % 2 ^ m < 2 ^ w := fun k =>
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos m)) hle
  refine eq_of_lanes hw
    (Nat.lt_of_le_of_lt (Nat.and_le_left)
      (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ s) (pack_lt w f hf n)))
    (pack_lt w _ hres n) ?_
  intro i b hin hbw
  rw [Nat.testBit_and,
      testBit_pack w _ hmask n i b hbw hin,
      testBit_pack w _ hres n i b hbw hin,
      Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow,
      Nat.testBit_shiftRight, Nat.testBit_shiftRight]
  by_cases hbm : b < m
  · -- inside the mask, so the shifted bit is a bit of this same lane
    have hidx : s + (w * i + b) = w * i + (b + s) := by omega
    have hlt : b + s < w := by omega
    rw [hidx, testBit_pack w f hf n i (b + s) hlt hin, Nat.add_comm s b]
    simp [hbm]
  · -- outside the mask, so both sides are false whatever the bit was
    simp [hbm]

/-! ## The mixer, one lane at a time

`caMix32` masks to 32 bits *after* each multiply. The packed computation
cannot: an unmasked lane is 41 bits wide, and 41 bits times a 31-bit constant
is 72 bits, which still fits a 128-bit lane, but the *shifted* copy carries
the neighbour lane's bits at the top of the lane and those would be dragged
across the boundary by the multiply. So the packed form masks *before* the
multiply as well, and the two agree only because
`(a % 2 ^ m * c) % 2 ^ m = (a * c) % 2 ^ m`.

That identity, and the fact that the extra mask after the shift is a no-op on
a lane narrow enough, are the entire distance between `caMix32` and what the
packed arithmetic computes. Both are proved here, scalar, before any packing
is involved.
-/

/-- Masking before a multiply and masking after it agree. -/
theorem mul_mod_pow (a c m : Nat) :
    (a % 2 ^ m * c) % 2 ^ m = (a * c) % 2 ^ m := by
  rw [Nat.mul_mod, Nat.mod_eq_of_lt (Nat.mod_lt a (Nat.two_pow_pos m)),
      ← Nat.mul_mod]

/-- Masking after a shift is a no-op when the lane was narrow enough, which
is the only reason the packed form may insert it. -/
theorem shiftRight_mod_eq {x s m : Nat} (hx : x < 2 ^ (m + s)) :
    (x >>> s) % 2 ^ m = x >>> s := by
  apply Nat.mod_eq_of_lt
  rw [Nat.shiftRight_eq_div_pow, Nat.div_lt_iff_lt_mul (Nat.two_pow_pos s),
      ← Nat.pow_add]
  exact hx

/-- The specification's mask, as a remainder. -/
theorem and_mask_eq_mod (x m : Nat) : x &&& (2 ^ m - 1) = x % 2 ^ m := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
  exact Bool.and_comm _ _

example : (0xffffffff : Nat) = 2 ^ 32 - 1 := by rfl

/-- One xor-shift-multiply stage with the mask moved in front of the
multiply, which is what the packed arithmetic can do. -/
def stage (s c x : Nat) : Nat :=
  ((x ^^^ ((x >>> s) % 2 ^ 32)) % 2 ^ 32 * c) % 2 ^ 32

/-- The same stage as the specification writes it. -/
def stageSpec (s c x : Nat) : Nat :=
  ((x ^^^ (x >>> s)) * c) % 2 ^ 32

theorem stage_lt (s c x : Nat) : stage s c x < 2 ^ 32 :=
  Nat.mod_lt _ (Nat.two_pow_pos 32)

theorem stage_eq {s c x : Nat} (hx : x < 2 ^ (32 + s)) :
    stage s c x = stageSpec s c x := by
  rw [stage, stageSpec, shiftRight_mod_eq hx, mul_mod_pow]

/-- `caMix32` written the way the packed arithmetic computes it. -/
def mixLane (x : Nat) : Nat :=
  let d := stage 15 0x846ca68b (stage 16 0x7feb352d x)
  (d ^^^ ((d >>> 16) % 2 ^ 32)) % 2 ^ 32

/-- The two agree on every lane the initial row can produce. The hypothesis
is generous: a lane holds `seed + (i + 1) * 0x9e3779b9` with `seed < 2 ^ 32`
and `i + 1 ≤ 256`, hence less than `2 ^ 41`. -/
theorem mixLane_eq {x : Nat} (hx : x < 2 ^ 48) : mixLane x = caMix32 x := by
  have hwiden : ∀ {a j : Nat}, a < 2 ^ 32 → 32 ≤ j → a < 2 ^ j := by
    intro a j ha hj
    exact Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) hj)
  have hb : stage 16 0x7feb352d x < 2 ^ 32 := stage_lt _ _ _
  have hd : stage 15 0x846ca68b (stage 16 0x7feb352d x) < 2 ^ 32 :=
    stage_lt _ _ _
  have hlit : (0xffffffff : Nat) = 2 ^ 32 - 1 := by rfl
  simp only [mixLane, caMix32]
  rw [shiftRight_mod_eq (hwiden hd (by omega)),
      stage_eq (hwiden hb (by omega)),
      stage_eq (show x < 2 ^ (32 + 16) from hx),
      stageSpec, stageSpec, hlit,
      and_mask_eq_mod, and_mask_eq_mod, and_mask_eq_mod]

/-! ## The ramp, and splitting a packing in two

The 256 lane inputs are `seed + (i + 1) * 0x9e3779b9`. Built lane by lane
that is 256 multiplications and 256 additions. Built as a packing it is two
multiplications and one addition, against two constants that do not depend on
the seed, because `pack_mul` and `pack_add` carry no side conditions.
-/

theorem pack_congr (w : Nat) {f g : Nat → Nat} :
    ∀ n, (∀ k, k < n → f k = g k) → pack w f n = pack w g n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    rw [pack, pack, ih (fun j hj => h j (by omega)), h k (by omega)]

/-- The whole seeded ramp, from two seed-independent constants. -/
theorem ramp_eq (w n seed c : Nat) :
    pack w (fun _ => 1) n * seed + pack w (fun i => i + 1) n * c
      = pack w (fun i => seed + (i + 1) * c) n := by
  rw [pack_mul, pack_mul, pack_add]
  exact pack_congr w n (fun k _ => by rw [Nat.one_mul])

/-- A packing splits at any point, the upper part shifted by what the lower
part occupies. The merge tree is this read backwards. -/
theorem pack_split (w : Nat) (g : Nat → Nat) (a : Nat) :
    ∀ b, pack w g (a + b)
      = pack w g a + pack w (fun t => g (a + t)) b * 2 ^ (w * a) := by
  intro b
  induction b with
  | zero => simp [pack]
  | succ q ih =>
    have he : (2 : Nat) ^ (w * (a + q)) = 2 ^ (w * q) * 2 ^ (w * a) := by
      rw [Nat.mul_add, Nat.add_comm (w * a) (w * q), Nat.pow_add]
    show pack w g (a + q) + g (a + q) * 2 ^ (w * (a + q))
        = pack w g a
          + (pack w (fun t => g (a + t)) q + g (a + q) * 2 ^ (w * q))
            * 2 ^ (w * a)
    rw [ih, Nat.add_mul, he, Nat.mul_assoc]
    omega

/-! ## One round of the gather

A round reads a packing of `2 * m` lanes of width `W`, each holding `h` bits,
and returns a packing of `m` lanes of width `2 * W`, each holding `2 * h`
bits: the even lane in the low half, the odd lane above it. Eight rounds take
256 lanes of one bit each down to a single lane holding all 256, and
`pack W p 1 = p 0`, so that last lane *is* the answer.

The even and the odd halves are each recovered by one mask, which is bit
work and needs `eq_of_lanes`. Everything after that is free: `pack_mul`
raises the odd half into place and `pack_add` joins the two, neither with a
side condition, so no carry argument appears anywhere in the tree.
-/

/-- The even lanes, read at double width. -/
theorem pack_even {W h m : Nat} (P : Nat → Nat) (hW : 0 < W) (hh : h ≤ W)
    (hP : ∀ k, P k < 2 ^ h) :
    pack W P (2 * m) &&& pack (2 * W) (fun _ => 2 ^ h - 1) m
      = pack (2 * W) (fun j => P (2 * j)) m := by
  have hhW : (2 : Nat) ^ h ≤ 2 ^ W := Nat.pow_le_pow_right (by omega) hh
  have hPW : ∀ k, P k < 2 ^ W := fun k => Nat.lt_of_lt_of_le (hP k) hhW
  have hP2 : ∀ k, P k < 2 ^ (2 * W) :=
    fun k => Nat.lt_of_lt_of_le (hPW k)
      (Nat.pow_le_pow_right (by omega) (by omega))
  have hmask : ∀ _ : Nat, (2 : Nat) ^ h - 1 < 2 ^ (2 * W) := by
    intro _
    have h1 := Nat.two_pow_pos h
    have h2 : (2 : Nat) ^ h ≤ 2 ^ (2 * W) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hwm : W * (2 * m) = 2 * W * m := by
    rw [Nat.mul_comm 2 m, ← Nat.mul_assoc, Nat.mul_right_comm,
        Nat.mul_comm W 2]
  refine eq_of_lanes (by omega)
    (Nat.lt_of_le_of_lt Nat.and_le_left
      (by rw [← hwm]; exact pack_lt W P hPW (2 * m)))
    (pack_lt (2 * W) _ (fun j => hP2 (2 * j)) m) ?_
  intro i b hin hbw
  rw [Nat.testBit_and,
      testBit_pack (2 * W) _ hmask m i b hbw hin,
      testBit_pack (2 * W) _ (fun j => hP2 (2 * j)) m i b hbw hin,
      Nat.testBit_two_pow_sub_one]
  by_cases hbh : b < h
  · have hidx : 2 * W * i + b = W * (2 * i) + b := by
      rw [Nat.mul_comm 2 W, Nat.mul_assoc]
    rw [hidx, testBit_pack W P hPW (2 * m) (2 * i) b (by omega) (by omega)]
    simp [hbh]
  · rw [testBit_eq_false_of_lt_pow (hP (2 * i)) (by omega)]
    simp [hbh]

/-- The odd lanes, brought down by one lane width and read at double width. -/
theorem pack_odd {W h m : Nat} (P : Nat → Nat) (hW : 0 < W) (hh : h ≤ W)
    (hP : ∀ k, P k < 2 ^ h) :
    (pack W P (2 * m) >>> W) &&& pack (2 * W) (fun _ => 2 ^ h - 1) m
      = pack (2 * W) (fun j => P (2 * j + 1)) m := by
  have hhW : (2 : Nat) ^ h ≤ 2 ^ W := Nat.pow_le_pow_right (by omega) hh
  have hPW : ∀ k, P k < 2 ^ W := fun k => Nat.lt_of_lt_of_le (hP k) hhW
  have hP2 : ∀ k, P k < 2 ^ (2 * W) :=
    fun k => Nat.lt_of_lt_of_le (hPW k)
      (Nat.pow_le_pow_right (by omega) (by omega))
  have hmask : ∀ _ : Nat, (2 : Nat) ^ h - 1 < 2 ^ (2 * W) := by
    intro _
    have h1 := Nat.two_pow_pos h
    have h2 : (2 : Nat) ^ h ≤ 2 ^ (2 * W) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hwm : W * (2 * m) = 2 * W * m := by
    rw [Nat.mul_comm 2 m, ← Nat.mul_assoc, Nat.mul_right_comm,
        Nat.mul_comm W 2]
  refine eq_of_lanes (by omega)
    (Nat.lt_of_le_of_lt Nat.and_le_left
      (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ W)
        (by rw [← hwm]; exact pack_lt W P hPW (2 * m))))
    (pack_lt (2 * W) _ (fun j => hP2 (2 * j + 1)) m) ?_
  intro i b hin hbw
  rw [Nat.testBit_and,
      testBit_pack (2 * W) _ hmask m i b hbw hin,
      testBit_pack (2 * W) _ (fun j => hP2 (2 * j + 1)) m i b hbw hin,
      Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight]
  by_cases hbh : b < h
  · have hidx : W + (2 * W * i + b) = W * (2 * i + 1) + b := by
      rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm 2 W, Nat.mul_assoc]
      omega
    rw [hidx,
        testBit_pack W P hPW (2 * m) (2 * i + 1) b (by omega) (by omega)]
    simp [hbh]
  · rw [testBit_eq_false_of_lt_pow (hP (2 * i + 1)) (by omega)]
    simp [hbh]

/-- One round of the gather. The two masks are the only bit work; the shift
into place and the join are `pack_mul` and `pack_add`, which is why no carry
argument is needed. -/
theorem merge_round {W h m : Nat} (P : Nat → Nat) (hW : 0 < W) (hh : h ≤ W)
    (hP : ∀ k, P k < 2 ^ h) :
    (pack W P (2 * m) &&& pack (2 * W) (fun _ => 2 ^ h - 1) m)
      + ((pack W P (2 * m) >>> W)
          &&& pack (2 * W) (fun _ => 2 ^ h - 1) m) * 2 ^ h
      = pack (2 * W) (fun j => P (2 * j) + P (2 * j + 1) * 2 ^ h) m := by
  rw [pack_even P hW hh hP, pack_odd P hW hh hP, pack_mul, pack_add]

/-! ## Can the kernel check a mask against its packing

The eight gather masks have to be literals in the submission, because
building each one from the recursive definition would cost operations at
reduction time and the gather is already the larger half of the work. That is
only viable if the kernel can verify a literal against its packed form once,
at compile time. Both sizes the design needs are checked here: the first round
packs 128 lanes, and the last is a single lane 16,384 bits wide. If either
`rfl` is slow or fails, the masks have to be built by doubling instead and the
operation count rises.
-/

set_option maxRecDepth 100000 in
example : pack 64 (fun _ => 1) 4 = 0x1000000000000000100000000000000010000000000000001 := by rfl

set_option maxRecDepth 100000 in
example : pack 128 (fun _ => 1) 128 = 0x100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001 := by rfl

set_option exponentiation.threshold 400 in
set_option maxRecDepth 100000 in
example : pack 16384 (fun _ => 2 ^ 128 - 1) 1 = 0xffffffffffffffffffffffffffffffff := by rfl

/-! ## `encodeRow` is a packing of width one

`encodeRow` folds the row least-significant-bit first, so the number it builds
is exactly a packing with `w = 1`. Saying so turns the specification's list
fold into the same object the gather produces, and the whole proof then closes
inside the lane algebra rather than by reasoning about lists.
-/

theorem encodeRow_cons (a : Bool) (as : List Bool) :
    encodeRow (a :: as) = 2 * encodeRow as + (if a then 1 else 0) := rfl

theorem encodeRow_foldr (c : Nat) :
    ∀ l : List Bool,
      l.foldr (fun b acc => 2 * acc + (if b then 1 else 0)) c
        = encodeRow l + 2 ^ l.length * c := by
  intro l
  induction l with
  | nil => simp [encodeRow]
  | cons a as ih =>
    have hp : (2 : Nat) ^ (as.length + 1) = 2 ^ as.length * 2 :=
      Nat.pow_succ 2 as.length
    have hm : 2 * (2 ^ as.length * c) = 2 ^ as.length * 2 * c := by
      rw [Nat.mul_left_comm, ← Nat.mul_assoc]
    show 2 * (as.foldr (fun b acc => 2 * acc + (if b then 1 else 0)) c)
          + (if a then 1 else 0)
        = encodeRow (a :: as) + 2 ^ (as.length + 1) * c
    rw [ih, encodeRow_cons, hp, Nat.mul_add, hm]
    omega

theorem encodeRow_append (l1 l2 : List Bool) :
    encodeRow (l1 ++ l2) = encodeRow l1 + 2 ^ l1.length * encodeRow l2 := by
  rw [encodeRow, List.foldr_append]
  exact encodeRow_foldr (encodeRow l2) l1

/-- The specification's encoding of a row built by `List.range` and `map` is
a width-one packing of the same function. -/
theorem encodeRow_map_range (g : Nat → Bool) :
    ∀ n, encodeRow ((List.range n).map g)
      = pack 1 (fun i => if g i then 1 else 0) n := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
    have hone : (1 : Nat) * k = k := Nat.one_mul k
    have hlast : encodeRow (List.map g [k]) = (if g k then 1 else 0) := by
      simp [encodeRow]
    rw [List.range_succ, List.map_append, encodeRow_append, ih,
        List.length_map, List.length_range, hlast]
    show pack 1 (fun i => if g i then 1 else 0) k
          + 2 ^ k * (if g k then 1 else 0)
        = pack 1 (fun i => if g i then 1 else 0) k
          + (if g k then 1 else 0) * 2 ^ (1 * k)
    rw [hone, Nat.mul_comm]

/-! ## Reading one bit out of every lane

The row wants bit 31 of each lane. That is `pack_shiftRight_and_mask` at
`m = 1` and `s = 31`, since `1 + 31 ≤ 64`, and the mask is the all-ones
packing. What comes back is each lane modulo two, which is the bit.
-/

theorem mod_two_eq (y : Nat) : y % 2 = if y.testBit 0 then 1 else 0 := by
  rw [Nat.testBit_zero]
  by_cases h : y % 2 = 1
  · rw [h]; simp
  · have h0 : y % 2 = 0 := by omega
    rw [h0]; simp

theorem shiftRight_mod_two (x s : Nat) :
    (x >>> s) % 2 = if x.testBit s then 1 else 0 := by
  rw [mod_two_eq, Nat.testBit_shiftRight, Nat.add_zero]

/-! ## The payload, and why the merge tree is an induction

Round `r` has gathered the cells in groups of `2 ^ r`, each group packed at
the bottom of its field. Writing that group as `pack 1 b (2 ^ r)` — a
width-one packing, the same object `encodeRow` turned out to be — is what
makes the tree an induction: `pack_split` says a width-one packing of
`2 ^ (r+1)` cells is its lower half plus its upper half shifted, which is
exactly what one round produces.
-/

/-- The cells gathered at round `r`, group `j`. -/
def payload (b : Nat → Nat) (r j : Nat) : Nat :=
  pack 1 (fun t => b (2 ^ r * j + t)) (2 ^ r)

theorem payload_lt {b : Nat → Nat} (hb : ∀ k, b k < 2) (r j : Nat) :
    payload b r j < 2 ^ 2 ^ r := by
  have h := pack_lt 1 (fun t => b (2 ^ r * j + t)) (fun t => hb _) (2 ^ r)
  rw [Nat.one_mul] at h
  exact h

theorem payload_zero (b : Nat → Nat) (j : Nat) : payload b 0 j = b j := by
  show 0 + b (1 * j + 0) * 2 ^ (1 * 0) = b j
  rw [Nat.one_mul, Nat.add_zero, Nat.mul_zero, Nat.pow_zero, Nat.mul_one,
      Nat.zero_add]

theorem payload_succ (b : Nat → Nat) (r j : Nat) :
    payload b (r + 1) j
      = payload b r (2 * j) + payload b r (2 * j + 1) * 2 ^ 2 ^ r := by
  have hsplit : (2 : Nat) ^ (r + 1) = 2 ^ r + 2 ^ r := by
    rw [Nat.pow_succ]; omega
  have hlo : ∀ t, b (2 ^ (r + 1) * j + t) = b (2 ^ r * (2 * j) + t) := by
    intro t
    have he : (2 : Nat) ^ (r + 1) * j = 2 ^ r * (2 * j) := by
      rw [Nat.pow_succ, Nat.mul_assoc]
    rw [he]
  have hhi : ∀ t, b (2 ^ (r + 1) * j + (2 ^ r + t))
      = b (2 ^ r * (2 * j + 1) + t) := by
    intro t
    have he : (2 : Nat) ^ (r + 1) * j + 2 ^ r = 2 ^ r * (2 * j + 1) := by
      rw [Nat.mul_add, Nat.mul_one, Nat.pow_succ, Nat.mul_assoc]
    rw [← Nat.add_assoc, he]
  -- `hsplit` must not be rewritten in the goal: it would also fire inside the
  -- function body, turning `2 ^ (r+1) * j` into `(2 ^ r + 2 ^ r) * j` and
  -- leaving `pack_split` with nothing to match. So the split is established
  -- on its own, where rewriting both sides at once is harmless.
  have hs : pack 1 (fun t => b (2 ^ (r + 1) * j + t)) (2 ^ (r + 1))
      = pack 1 (fun t => b (2 ^ (r + 1) * j + t)) (2 ^ r)
        + pack 1 (fun t => b (2 ^ (r + 1) * j + (2 ^ r + t))) (2 ^ r)
          * 2 ^ (1 * 2 ^ r) := by
    rw [hsplit]
    exact pack_split 1 _ (2 ^ r) (2 ^ r)
  simp only [payload]
  rw [hs, Nat.one_mul,
      pack_congr 1 (2 ^ r) (fun t _ => hlo t),
      pack_congr 1 (2 ^ r) (fun t _ => hhi t)]

/-- A packing of one lane is that lane. This is what makes the eighth round
the answer rather than a step towards it. -/
theorem pack_one (w : Nat) (f : Nat → Nat) : pack w f 1 = f 0 := by
  show 0 + f 0 * 2 ^ (w * 0) = f 0
  rw [Nat.mul_zero, Nat.pow_zero, Nat.mul_one, Nat.zero_add]

/-- After eight rounds the single remaining group is the whole row. -/
theorem payload_eight (b : Nat → Nat) :
    payload b 8 0 = pack 1 b 256 := by
  show pack 1 (fun t => b (256 * 0 + t)) 256 = pack 1 b 256
  exact pack_congr 1 256 (fun t _ => by rw [Nat.mul_zero, Nat.zero_add])

/-! ## The gather, as one lemma used eight times

`merge_round` is about an arbitrary lane function; `payload_succ` says the
payload is exactly what one round produces. Putting the two together gives a
single lemma that advances the round counter, so the eight rounds in the
submission are eight instantiations of it rather than eight bit arguments.
-/

theorem gather_round (b : Nat → Nat) (hb : ∀ k, b k < 2) (r m W : Nat)
    (hW : 0 < W) (hh : 2 ^ r ≤ W) :
    (pack W (payload b r) (2 * m) &&& pack (2 * W) (fun _ => 2 ^ 2 ^ r - 1) m)
      + ((pack W (payload b r) (2 * m) >>> W)
          &&& pack (2 * W) (fun _ => 2 ^ 2 ^ r - 1) m) * 2 ^ 2 ^ r
      = pack (2 * W) (payload b (r + 1)) m := by
  rw [merge_round (payload b r) hW hh (payload_lt hb r)]
  exact pack_congr (2 * W) m (fun j _ => (payload_succ b r j).symm)

/-- The gather starts from the bits themselves. -/
theorem gather_start (b : Nat → Nat) (W n : Nat) :
    pack W (payload b 0) n = pack W b n :=
  pack_congr W n (fun j _ => payload_zero b j)

/-! ## The two fixed cells

The specification fixes cell 0 to true and cell 1 to false, excluding the two
spatially uniform rows. On the packed row that is one shift, one multiply and
one addition, because `pack_split` peels the bottom two lanes off a
width-one packing and the hash never has to be corrected.
-/

theorem fix_two {f g : Nat → Nat} (hf : ∀ k, f k < 2)
    (hfg : ∀ t, f (2 + t) = g (2 + t)) (hg0 : g 0 = 1) (hg1 : g 1 = 0) :
    (pack 1 f 256 >>> 2) * 4 + 1 = pack 1 g 256 := by
  have hpow : (2 : Nat) ^ (1 * 2) = 4 := by rfl
  have hlow : pack 1 f 2 < 4 := by
    have h := pack_lt 1 f hf 2
    rw [hpow] at h
    exact h
  have hsf : pack 1 f 256
      = pack 1 f 2 + pack 1 (fun t => f (2 + t)) 254 * 4 := by
    have h := pack_split 1 f 2 254
    rw [hpow] at h
    exact h
  have hsg : pack 1 g 256
      = pack 1 g 2 + pack 1 (fun t => g (2 + t)) 254 * 4 := by
    have h := pack_split 1 g 2 254
    rw [hpow] at h
    exact h
  have hg2 : pack 1 g 2 = 1 := by
    show 0 + g 0 * 2 ^ (1 * 0) + g 1 * 2 ^ (1 * 1) = 1
    rw [hg0, hg1]
    rfl
  have hup : pack 1 (fun t => f (2 + t)) 254
      = pack 1 (fun t => g (2 + t)) 254 :=
    pack_congr 1 254 (fun t _ => hfg t)
  -- the shift is exact, because the two lanes it drops are below 4
  have hdiv : pack 1 f 256 >>> 2 = pack 1 (fun t => f (2 + t)) 254 := by
    rw [Nat.shiftRight_eq_div_pow, hsf]
    show (pack 1 f 2 + pack 1 (fun t => f (2 + t)) 254 * 4) / 4 = _
    rw [Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hlow,
        Nat.zero_add]
  rw [hdiv, hsg, hg2, hup]

end Lane
