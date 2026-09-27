import Spec

namespace Submission

structure Window where
  x0 : Nat
  x1 : Nat
  x2 : Nat
  x3 : Nat
  x4 : Nat
  x5 : Nat
  x6 : Nat
  x7 : Nat
  x8 : Nat
  x9 : Nat
  x10 : Nat
  x11 : Nat
  x12 : Nat
  x13 : Nat
  x14 : Nat
  x15 : Nat

def Window.toList (w : Window) : List Nat :=
  [w.x0, w.x1, w.x2, w.x3, w.x4, w.x5, w.x6, w.x7,
   w.x8, w.x9, w.x10, w.x11, w.x12, w.x13, w.x14, w.x15]

def Window.nextWord (w : Window) : Nat :=
  add32 (add32 (smallSigma1 w.x14) w.x9)
    (add32 (smallSigma0 w.x1) w.x0)

def Window.push (w : Window) (x : Nat) : Window :=
  ⟨w.x1, w.x2, w.x3, w.x4, w.x5, w.x6, w.x7, w.x8,
   w.x9, w.x10, w.x11, w.x12, w.x13, w.x14, w.x15, x⟩

def generate : Nat → Window → List Nat
  | 0, _ => []
  | k + 1, w =>
      let x := w.nextWord
      x :: generate k (w.push x)

def initialWindow (d : Digest) : Window :=
  ⟨d.a, d.b, d.c, d.d, d.e, d.f, d.g, d.h,
   0x80000000, 0, 0, 0, 0, 0, 0, 256⟩

def fastSchedule (d : Digest) : List Nat :=
  let w := initialWindow d
  w.toList ++ generate 48 w

def fastStep (d : Digest) : Digest :=
  let f := rounds (K.zip (fastSchedule d)) iv
  ⟨add32 iv.a f.a, add32 iv.b f.b, add32 iv.c f.c, add32 iv.d f.d,
   add32 iv.e f.e, add32 iv.f f.f, add32 iv.g f.g, add32 iv.h f.h⟩

theorem drop_last16 (pre : List Nat) (w : Window) :
    (pre ++ w.toList).drop ((pre ++ w.toList).length - 16) = w.toList := by
  simp [Window.toList]

theorem nextWord_eq (w : Window) :
    add32 (add32 (smallSigma1 (w.toList.getD 14 0)) (w.toList.getD 9 0))
      (add32 (smallSigma0 (w.toList.getD 1 0)) (w.toList.getD 0 0)) =
      w.nextWord := by
  rfl

theorem append_push (pre : List Nat) (w : Window) :
    (pre ++ w.toList) ++ [w.nextWord] =
      (pre ++ [w.x0]) ++ (w.push w.nextWord).toList := by
  simp [Window.toList, Window.push]

theorem extend_eq : ∀ k pre w,
    extendW k (pre ++ w.toList) =
      pre ++ w.toList ++ generate k w
  | 0, pre, w => by
      simp [extendW, generate]
  | k + 1, pre, w => by
      rw [extendW, drop_last16, nextWord_eq, append_push]
      rw [extend_eq k (pre ++ [w.x0]) (w.push w.nextWord)]
      simp [generate, Window.toList, Window.push, List.append_assoc]

theorem schedule_correct (d : Digest) :
    fastSchedule d =
      extendW 48 [d.a, d.b, d.c, d.d, d.e, d.f, d.g, d.h,
        0x80000000, 0, 0, 0, 0, 0, 0, 256] := by
  simpa [fastSchedule, initialWindow, Window.toList] using
    (extend_eq 48 [] (initialWindow d)).symm

theorem fastStep_correct (d : Digest) : fastStep d = sha256step d := by
  unfold fastStep sha256step compress
  rw [schedule_correct]

theorem fastStep_fun : fastStep = sha256step :=
  funext fastStep_correct

/-! ## Fusing the schedule into the rounds

The starter already removed the specification's list-indexed `extendW` in
favour of a sixteen-field `Window`, which is the larger win and is kept. What
remains is that `fastStep` still materialises two lists per block: a 64-word
schedule, and then `K.zip` of it into 64 pairs. At 512 chain steps that is
about 65,000 cons cells allocated only to drive a loop whose trip count is
already known.

Neither list is needed. The window gives the current word as `w.x0` in one
projection, and sliding it by one produces the next, so the schedule can be
walked as the rounds consume it. `K` is walked head-first in lockstep, which is
O(1) per round and builds nothing.

`roundsW_eq` is the correspondence, proved by induction on the constant list.
The step is exactly the observation that pushing the window and dropping one
word from the schedule are the same move:

    [x1..x15] ++ (nextWord :: rest)  =  (w.push nextWord).toList ++ rest
-/

/-- The rounds, walking the schedule as it is generated. -/
def roundsW : List Nat → Window → Digest → Digest
  | [],      _, s => s
  | k :: ks, w, s => roundsW ks (w.push w.nextWord) (round s k w.x0)

theorem roundsW_eq :
    ∀ (ks : List Nat) (w : Window) (s : Digest) (m : Nat),
      ks.length ≤ 16 + m →
      roundsW ks w s = rounds (ks.zip (w.toList ++ generate m w)) s := by
  intro ks
  induction ks with
  | nil =>
    intro w s m _
    rfl
  | cons k ks ih =>
    intro w s m hm
    match m, hm with
    | (m + 1), hm =>
      rw [roundsW]
      show roundsW ks (w.push w.nextWord) (round s k w.x0)
          = rounds ((k :: ks).zip (w.toList ++ generate (m + 1) w)) s
      rw [ih (w.push w.nextWord) (round s k w.x0) m (by simp at hm ⊢; omega)]
      -- the head of the schedule is w.x0, and its tail is the pushed window's
      -- own schedule, which is the whole content of the step
      simp [Window.toList, Window.push, generate, rounds, List.zip]

/-- The constant list has exactly the 64 entries the schedule supplies. -/
theorem roundsW_K (d : Digest) :
    roundsW K (initialWindow d) iv = rounds (K.zip (fastSchedule d)) iv := by
  rw [fastSchedule]
  exact roundsW_eq K (initialWindow d) iv 48 (by decide)

/-- The same step, with no list built per block. -/
def fastStep2 (d : Digest) : Digest :=
  let f := roundsW K (initialWindow d) iv
  ⟨add32 iv.a f.a, add32 iv.b f.b, add32 iv.c f.c, add32 iv.d f.d,
   add32 iv.e f.e, add32 iv.f f.f, add32 iv.g f.g, add32 iv.h f.h⟩

theorem fastStep2_eq (d : Digest) : fastStep2 d = fastStep d := by
  rw [fastStep2, fastStep, roundsW_K]

theorem fastStep2_fun : fastStep2 = sha256step := by
  funext d
  rw [fastStep2_eq]
  exact fastStep_correct d

/-- TODO 1: Optimize this implementation. Keep it total and kernel-reducible. -/
def impl (n : Nat) : Nat :=
  encodeDigest
    (iterDigest fastStep2 (sha256Steps n) (seedDigest (sha256Seed n)))

/-- TODO 2: Prove that `impl n` equals `sha256Spec n` for every natural number n.
Keep the theorem statement unchanged. -/
theorem impl_correct : ∀ n, impl n = sha256Spec n := fun n =>
  congrArg
    (fun step => encodeDigest
      (iterDigest step (sha256Steps n) (seedDigest (sha256Seed n))))
    fastStep2_fun

end Submission
