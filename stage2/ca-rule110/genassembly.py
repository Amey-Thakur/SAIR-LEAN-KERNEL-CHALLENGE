#!/usr/bin/env python3
# ==============================================================================
# File: genassembly.py
# Description: Emits the assembly block that turns the verified lane algebra
#   into the packed initial row, with the wide constants as literals.
#
#   It is appended to LaneProbe.lean first, which CI compiles on its own, so
#   the assembly is checked without the live entry ever being at risk. Once it
#   compiles, build_submission.py moves the same text into Submission.lean.
#
#   Two file-level options rather than one per declaration. Relating a literal
#   to its packed form unfolds `pack` once per lane, up to 256 times, which is
#   past the elaborator's default recursion limit, and the last gather mask
#   holds 128 bits, whose exponent is past its exponentiation threshold. Both
#   are limits on *checking* a constant, not on the kernel reducing it. They
#   cannot be written as `set_option ... in` here, because a doc comment may
#   not sit between that and the declaration it belongs to.
#
#   Each stage of the mixer is a named definition. Nesting them as `let`s
#   instead would make the mixer's expanded term some 2,500 characters wide
#   and leave nothing for a rewrite to match against; named, the three stages
#   compose and the proof is three rewrites.
#
# Usage: py stage2/ca-rule110/genassembly.py --append
#        py stage2/ca-rule110/genassembly.py
# Author: Amey Thakur
# License: CC BY 4.0
# ==============================================================================

from __future__ import annotations

import argparse
import pathlib
import sys

sys.set_int_max_str_digits(200_000)

HERE = pathlib.Path(__file__).resolve().parent
CELLS = 256
LANE = 64
PHI = 0x9E3779B9
A1 = 0x7FEB352D
A2 = 0x846CA68B


def pack(width: int, values: list[int]) -> int:
    out = 0
    for k, v in enumerate(values):
        out |= v << (width * k)
    return out


ONES = pack(LANE, [1] * CELLS)
RAMP = pack(LANE, [i + 1 for i in range(CELLS)])
M32P = pack(LANE, [0xFFFFFFFF] * CELLS)

ROUNDS = []
for r in range(8):
    ROUNDS.append({
        "r": r,
        "W": LANE << r,
        "twoW": LANE << (r + 1),
        "mul": 1 << (1 << r),
        "lanes": CELLS >> (r + 1),
        "mask": pack(LANE << (r + 1),
                     [(1 << (1 << r)) - 1] * (CELLS >> (r + 1))),
    })


def block() -> str:
    L: list[str] = []
    a = L.append

    a("/-! ## Assembling the row")
    a("")
    a("The constants are literals, because building a mask from the recursive")
    a("definition would cost operations at reduction time and the gather is")
    a("already the larger half of the work. Each is related to its packed form")
    a("by rfl, which the kernel settles once, at compile time, and never again")
    a("while a judged case reduces.")
    a("-/")
    a("")
    a("namespace Row")
    a("")
    a("-- Checking a constant against its packing unfolds the packing once per")
    a("-- lane, and the last gather mask holds 128 bits. Both limits below are")
    a("-- on checking a constant, not on the kernel reducing it.")
    a("set_option maxRecDepth 1000000")
    a("set_option exponentiation.threshold 100000")
    a("")
    a(f"def onesP : Nat := {hex(ONES)}")
    a("")
    a(f"def rampP : Nat := {hex(RAMP)}")
    a("")
    a(f"def maskP : Nat := {hex(M32P)}")
    a("")
    for rd in ROUNDS:
        a(f"def gmask{rd['r']} : Nat := {hex(rd['mask'])}")
        a("")

    a("theorem onesP_eq : onesP = Lane.pack 64 (fun _ => 1) 256 := by rfl")
    a("")
    a("theorem onesP_eq' : onesP = Lane.pack 64 (fun _ => 2 ^ 1 - 1) 256 := by")
    a("  rfl")
    a("")
    a("theorem rampP_eq : rampP = Lane.pack 64 (fun i => i + 1) 256 := by rfl")
    a("")
    a("theorem maskP_eq :")
    a("    maskP = Lane.pack 64 (fun _ => 2 ^ 32 - 1) 256 := by rfl")
    a("")
    for rd in ROUNDS:
        a(f"theorem gmask{rd['r']}_eq : gmask{rd['r']}")
        a(f"    = Lane.pack {rd['twoW']} (fun _ => 2 ^ 2 ^ {rd['r']} - 1)"
          f" {rd['lanes']} := by rfl")
        a("")

    # ------------------------------------------------------------- the ramp --
    a("/-- The ramp lane, zero above the row. The packing reads only the first")
    a("256 lanes, so this agrees with seed + (i+1) * 0x9e3779b9 everywhere it")
    a("is read. Being bounded at *every* index is what matters: the lane")
    a("lemmas ask for a bound at every index, and the ramp itself has none. -/")
    a("def rampLane (seed i : Nat) : Nat :=")
    a(f"  if i < 256 then seed + (i + 1) * {PHI} else 0")
    a("")
    a("theorem rampLane_lt {seed : Nat} (hs : seed < 2 ^ 32) (i : Nat) :")
    a("    rampLane seed i < 2 ^ 41 := by")
    a("  have h41 : (2 : Nat) ^ 41 = 2199023255552 := by rfl")
    a("  have h32 : (2 : Nat) ^ 32 = 4294967296 := by rfl")
    a("  rw [rampLane]")
    a("  split")
    a("  · rename_i h")
    a(f"    have hb : (i + 1) * {PHI} <= 256 * {PHI} :=")
    a("      Nat.mul_le_mul_right _ (by omega)")
    a("    omega")
    a("  · omega")
    a("")
    a("theorem rampLane_lt64 {seed : Nat} (hs : seed < 2 ^ 32) :")
    a("    ∀ k, rampLane seed k < 2 ^ 64 := fun k =>")
    a("  Nat.lt_of_lt_of_le (rampLane_lt hs k)")
    a("    (Nat.pow_le_pow_right (by omega) (by omega))")
    a("")
    a("/-- The whole seeded ramp, from two seed-independent constants: two")
    a("multiplications and one addition in place of 256 of each. -/")
    a("theorem ramp_packed (seed : Nat) :")
    a(f"    onesP * seed + rampP * {PHI}")
    a("      = Lane.pack 64 (rampLane seed) 256 := by")
    a("  rw [onesP_eq, rampP_eq, Lane.ramp_eq]")
    a("  refine Lane.pack_congr 64 256 (fun k hk => ?_)")
    a("  rw [rampLane, if_pos hk]")
    a("")

    # ------------------------------------------------------------ the mixer --
    a("/-! ## The mixer")
    a("")
    a("One stage of the specification's hash, masked before the multiply")
    a("rather than after, and the final exclusive or, which has no multiply.")
    a("Naming them is what keeps the proof to three rewrites.")
    a("-/")
    a("")
    a("def stageP (s c x : Nat) : Nat :=")
    a("  (((x ^^^ ((x >>> s) &&& maskP)) &&& maskP) * c) &&& maskP")
    a("")
    a("def xorshiftP (s x : Nat) : Nat :=")
    a("  (x ^^^ ((x >>> s) &&& maskP)) &&& maskP")
    a("")
    a("theorem stageP_pack {s c : Nat} (f : Nat → Nat) (hs : 32 + s ≤ 64)")
    a("    (hc : c < 2 ^ 32) (hf : ∀ k, f k < 2 ^ 64) :")
    a("    stageP s c (Lane.pack 64 f 256)")
    a("      = Lane.pack 64 (fun k => Lane.stage s c (f k)) 256 := by")
    a("  rw [stageP, maskP_eq, Lane.pack_stage f hs hc hf]")
    a("")
    a("theorem xorshiftP_pack (f : Nat → Nat) (hf : ∀ k, f k < 2 ^ 64) :")
    a("    xorshiftP 16 (Lane.pack 64 f 256)")
    a("      = Lane.pack 64")
    a("          (fun k => (f k ^^^ ((f k >>> 16) % 2 ^ 32)) % 2 ^ 32)")
    a("          256 := by")
    a("  rw [xorshiftP, maskP_eq, Lane.pack_xorshift f (by omega) hf]")
    a("")
    a("/-- The whole hash, on all 256 cells at once. -/")
    a("theorem mix_packed {seed : Nat} (hs : seed < 2 ^ 32) :")
    a(f"    xorshiftP 16 (stageP 15 {A2} (stageP 16 {A1}")
    a("        (Lane.pack 64 (rampLane seed) 256)))")
    a("      = Lane.pack 64 (fun k => Lane.mixLane (rampLane seed k)) 256 := by")
    a("  have hwide : ∀ a : Nat, a < 2 ^ 32 → a < 2 ^ 64 := fun a ha =>")
    a("    Nat.lt_of_lt_of_le ha (Nat.pow_le_pow_right (by omega) (by omega))")
    a(f"  have hs1 : ∀ k, Lane.stage 16 {A1} (rampLane seed k) < 2 ^ 64 :=")
    a("    fun k => hwide _ (Lane.stage_lt _ _ _)")
    a(f"  have hs2 : ∀ k, Lane.stage 15 {A2}")
    a(f"      (Lane.stage 16 {A1} (rampLane seed k)) < 2 ^ 64 :=")
    a("    fun k => hwide _ (Lane.stage_lt _ _ _)")
    a("  rw [stageP_pack (rampLane seed) (by omega) (by decide)")
    a("        (rampLane_lt64 hs),")
    a("      stageP_pack _ (by omega) (by decide) hs1,")
    a("      xorshiftP_pack _ hs2]")
    a("  exact Lane.pack_congr 64 256 (fun k _ => rfl)")
    a("")

    # ---------------------------------------------------------- the gather --
    a("/-! ## The gather -/")
    a("")
    a("/-- Eight rounds, each one mask, one shift, one mask, one multiply and")
    a("one addition. -/")
    a("def gatherOf (b : Nat) : Nat :=")
    for rd in ROUNDS:
        a(f"  let b := (b &&& gmask{rd['r']})"
          f" + (((b >>> {rd['W']}) &&& gmask{rd['r']}) * {hex(rd['mul'])})")
    a("  b")
    a("")
    for rd in ROUNDS:
        r = rd["r"]
        a(f"theorem round{r} (b : Nat → Nat) (hb : ∀ k, b k < 2) (z : Nat)")
        a(f"    (hz : z = Lane.pack {rd['W']} (Lane.payload b {r})"
          f" {rd['lanes'] * 2}) :")
        a(f"    (z &&& gmask{r}) + (((z >>> {rd['W']}) &&& gmask{r})"
          f" * {hex(rd['mul'])})")
        a(f"      = Lane.pack {rd['twoW']} (Lane.payload b {r + 1})"
          f" {rd['lanes']} := by")
        a("  subst hz")
        a(f"  rw [gmask{r}_eq]")
        a(f"  exact Lane.gather_round b hb {r} {rd['lanes']} {rd['W']}")
        a("    (by omega) (by omega)")
        a("")

    a("/-- Eight rounds take 256 lanes of one bit each down to one lane holding")
    a("the whole row, and a packing of one lane is that lane.")
    a("")
    a("Each round after the first is instantiated at the previous round's")
    a("*result* and discharged by rfl, not at the previous round's expression.")
    a("Instantiating it at the expression would state the round in terms of a")
    a("term the preceding rewrite has already replaced, and the rewrite would")
    a("then find nothing to match. -/")
    a("theorem gatherOf_eq (b : Nat → Nat) (hb : ∀ k, b k < 2) :")
    a("    gatherOf (Lane.pack 64 b 256) = Lane.pack 1 b 256 := by")
    a("  have h0 := round0 b hb _ (Lane.gather_start b 64 256).symm")
    for rd in ROUNDS[1:]:
        a(f"  have h{rd['r']} := round{rd['r']} b hb _ rfl")
    a("  simp only [gatherOf]")
    a("  rw [h0, h1, h2, h3, h4, h5, h6, h7, Lane.pack_one]")
    a("  exact Lane.payload_eight b")
    a("")

    # ------------------------------------------------------------- the row --
    a("/-! ## The row -/")
    a("")
    a("/-- The initial row, all 256 cells at once. -/")
    a("def packedRow (seed : Nat) : Nat :=")
    a(f"  let x := onesP * seed + rampP * {PHI}")
    a(f"  let x := stageP 16 {A1} x")
    a(f"  let x := stageP 15 {A2} x")
    a("  let x := xorshiftP 16 x")
    a("  (gatherOf ((x >>> 31) &&& onesP) >>> 2) * 4 + 1")
    a("")
    a("/-- The bit the hash puts in cell i. -/")
    a("def bitOf (seed i : Nat) : Nat :=")
    a("  if (Lane.mixLane (rampLane seed i)).testBit 31 then 1 else 0")
    a("")
    a("theorem bitOf_def (seed k : Nat) :")
    a("    bitOf seed k")
    a("      = if (Lane.mixLane (rampLane seed k)).testBit 31 then 1 else 0 :=")
    a("  rfl")
    a("")
    a("theorem bitOf_lt (seed : Nat) : ∀ k, bitOf seed k < 2 := by")
    a("  intro k")
    a("  rw [bitOf]")
    a("  split <;> omega")
    a("")
    a("/-- The specification's own bit for cell i. -/")
    a("def specBit (seed i : Nat) : Nat :=")
    a("  if (if i = 0 then true else if i = 1 then false")
    a(f"      else (caMix32 (seed + (i + 1) * {PHI})).testBit 31)")
    a("    then 1 else 0")
    a("")
    a("theorem specBit_zero (seed : Nat) : specBit seed 0 = 1 := by rfl")
    a("")
    a("theorem specBit_one (seed : Nat) : specBit seed 1 = 0 := by rfl")
    a("")
    a("/-- Below the row the two agree, which is all the fix-up reads. It is")
    a("only below the row that they can: above it the ramp lane is zero and")
    a("the specification's hash is not. -/")
    a("theorem bitOf_eq_specBit {seed : Nat} (hs : seed < 2 ^ 32) :")
    a("    ∀ t, t < 254 → bitOf seed (2 + t) = specBit seed (2 + t) := by")
    a("  intro t ht")
    a("  have hlt : 2 + t < 256 := by omega")
    a("  have hne1 : ¬ (2 + t = 1) := by omega")
    a("  have h48 : rampLane seed (2 + t) < 2 ^ 48 :=")
    a("    Nat.lt_of_lt_of_le (rampLane_lt hs _)")
    a("      (Nat.pow_le_pow_right (by omega) (by omega))")
    a(f"  have hr : rampLane seed (2 + t) = seed + (2 + t + 1) * {PHI} := by")
    a("    rw [rampLane, if_pos hlt]")
    a("  rw [bitOf, specBit, Lane.mixLane_eq h48, hr]")
    a("  simp [hne1]")
    a("")
    a("/-- The row the packed arithmetic builds is the row the specification")
    a("encodes. -/")
    a("theorem packedRow_eq {seed : Nat} (hs : seed < 2 ^ 32) :")
    a("    packedRow seed = encodeRow (initRowFor seed) := by")
    a("  have hspec : encodeRow (initRowFor seed)")
    a("      = Lane.pack 1 (specBit seed) 256 := by")
    a("    rw [initRowFor, Lane.encodeRow_map_range]")
    a("    exact Lane.pack_congr 1 256 (fun i _ => rfl)")
    a("  have hmx : ∀ k, Lane.mixLane (rampLane seed k) < 2 ^ 64 := fun k =>")
    a("    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos 32))")
    a("      (Nat.pow_le_pow_right (by omega) (by omega))")
    a("  simp only [packedRow]")
    a("  rw [hspec, ramp_packed, mix_packed hs, onesP_eq',")
    a("      Lane.pack_shiftRight_and_mask _ (by omega) (by omega) hmx,")
    a("      Lane.pack_congr 64 256 (fun k _ =>")
    a("        (Lane.shiftRight_mod_two")
    a("            (Lane.mixLane (rampLane seed k)) 31).trans")
    a("          (bitOf_def seed k).symm),")
    a("      gatherOf_eq _ (bitOf_lt seed),")
    a("      Lane.fix_two (bitOf_lt seed) (bitOf_eq_specBit hs)")
    a("        (specBit_zero seed) (specBit_one seed)]")
    a("")
    a("end Row")
    return "\n".join(L)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--append", action="store_true")
    args = ap.parse_args()
    text = block()
    if args.append:
        p = HERE / "LaneProbe.lean"
        src = p.read_text(encoding="utf-8")
        marker = "/-! ## Assembling the row"
        if marker in src:
            src = src[:src.index(marker)].rstrip("\n") + "\n"
        p.write_text(src + "\n" + text + "\n", encoding="utf-8")
        print(f"appended {len(text.splitlines())} lines to LaneProbe.lean")
    else:
        print(text)


if __name__ == "__main__":
    main()
