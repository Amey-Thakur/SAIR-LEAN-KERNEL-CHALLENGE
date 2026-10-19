#!/usr/bin/env python3
# ==============================================================================
# File: instrument.py
# Description: Emits the Lean files that measure what the judge charges for,
#   and reports the instruction counts collected from them.
#
#   Why this exists. The rules say the metric is a hardware instruction count:
#   "In three separate processes, count only the target declaration's kernel
#   check, which reduces `impl n` and compares it with `v`", on a "Linux PMU
#   host". So the quantity to minimise is instructions retired by the KERNEL
#   while reducing `impl n`, and nothing else: not elaboration, not parsing the
#   expected literal, not the proof.
#
#   Two consequences, both of which have cost this repository rounds before.
#
#     * Wall clock is the wrong instrument. It includes 0.95 s of start-up and
#       the elaboration of a 24,000-digit literal, and it cannot resolve a
#       tenth of the work at the sizes that matter.
#     * A GitHub runner has no usable PMU, so `perf` cannot reproduce the
#       judge's counter. Callgrind can: it counts guest instructions exactly
#       and deterministically, which is the same quantity the PMU reports for
#       user-space work, and it has no run-to-run noise at all.
#
#   The kernel is then separated from the elaborator by differencing: the same
#   file is measured twice, once normally and once with
#   `debug.skipKernelTC`, which elaborates the declaration and does not hand
#   it to the kernel. The difference is the kernel check alone, which is what
#   the judge counts. The sum of those differences over the six judged sizes is
#   directly comparable with the number on the leaderboard, so the instrument
#   can be checked against a known figure rather than believed.
#
#   The micro-benchmarks answer the question the two cost models disagree
#   about. Each is a pair that differs by one operation, so the difference
#   divided by the iteration count is what that operation costs the kernel:
#   a `Nat` operation against an `Int` one, a narrow operand against a 3,484-bit
#   and an 80,000-bit one, and -- the pair that decides the whole strategy --
#   one pass of `lcG * c - lcR * d` over a 24-element list of wide integers
#   against the same arithmetic done once on a single packed integer.
#
# Usage: py stage2/polydisc/instrument.py --emit DIR
#        py stage2/polydisc/instrument.py --report DIR
# Author: Amey Thakur
# License: CC BY 4.0
# ==============================================================================

from __future__ import annotations

import argparse
import json
import pathlib
import re
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
sys.set_int_max_str_digits(2_000_000)

from model import JUDGED, disc_spec, kbits_of                      # noqa: E402

PREAMBLE = "import Submission\n"
OPTIONS = ("set_option maxRecDepth 8000000\n"
           "set_option maxHeartbeats 0\n")
SKIP = "set_option debug.skipKernelTC true\n"

# Operand widths that occur in the real computation: a coefficient at the
# hardest judged level, and an intermediate near the end of the subresultant
# loop, where the discriminant itself is about 80,000 bits.
W_COEFF = 3484
W_MID = 20000
W_BIG = 80000


def odd_hex(bits: int, salt: int = 1) -> int:
    """A deterministic odd integer of exactly `bits` bits."""
    value = (1 << (bits - 1)) | 1
    # fill the middle with a fixed pattern so the operand is not special
    pattern = 0xA5C3F17B9D2E6481
    shift = 1
    while shift + 64 < bits - 1:
        value |= (pattern + salt) % (1 << 64) << shift
        shift += 64
    return value | 1


def hx(value: int) -> str:
    """Hex, because a 24,000-digit decimal literal is parsed quadratically and
    that cost would sit in every measurement."""
    if value < 0:
        return f"(-0x{-value:x})"
    return f"0x{value:x}"


# --------------------------------------------------------------- benchmarks ---
def judged_cases() -> list[tuple[str, str, str]]:
    out = []
    for i, n in enumerate(JUDGED):
        value = disc_spec(n)
        body = (f"-- n = 2^{n.bit_length() - 1}, k = {kbits_of(n)} bits, "
                f"answer {value.bit_length()} bits\n"
                f"theorem judged : Submission.impl {n} = {hx(value)}"
                f" := by rfl\n")
        out.append((f"J{i}", body, f"judged n=2^{n.bit_length() - 1} "
                                   f"k={kbits_of(n)}"))
    return out


def breakdown() -> list[tuple[str, str, str]]:
    """Where the kernel's work actually sits inside one judged case.

    `costmodel.py` puts 55% of the operations in the coefficient setup and 95%
    of the bit-work in the subresultant loop, and the two halves imply opposite
    repairs. Operation count has now been measured to be the currency, but that
    does not settle it, because the setup's operations are `Nat` operations on
    narrow numbers and the loop's are `Int` operations, and those were measured
    to differ by 5.4x each. So the two parts are measured directly.

    Each file asserts a small residue, never the discriminant itself, so that
    the figure is the computation and not the comparison of a 24,000-figure
    literal.

      setup   the coefficient list, summed
      loop    the subresultant loop on a polynomial supplied as a literal,
              which performs no setup at all
      whole   the specification end to end
    """
    from model import (poly_of, deriv_hl, normal_resultant, disc_spec)

    out = []
    m = 1000003
    helper = ("def total : List Int -> Int\n"
              "  | [] => 0\n"
              "  | x :: xs => x + total xs\n")
    for tag, n in (("easy", 2 ** 18), ("mid", 2 ** 37), ("hard", 2 ** 57)):
        p = poly_of(n)
        k = kbits_of(n)

        out.append((f"B_setup_{tag}",
                    helper +
                    f"theorem b : total (polyOf {n}) % {m} = "
                    f"{sum(p) % m} := by rfl\n",
                    f"the coefficient setup alone, k={k}"))

        lit = ", ".join(hx(v) for v in p)
        value = normal_resultant(p, deriv_hl(p))
        out.append((f"B_loop_{tag}",
                    f"def PL : List Int := [{lit}]\n"
                    "def res : Int :=\n"
                    "  match normalResultant PL (derivHL PL) with\n"
                    "  | some r => r\n"
                    "  | none => 0\n"
                    f"theorem b : res % {m} = {value % m} := by rfl\n",
                    f"the subresultant loop alone, on a literal polynomial, "
                    f"k={k}"))

        out.append((f"B_whole_{tag}",
                    f"theorem b : discSpec {n} % {m} = "
                    f"{disc_spec(n) % m} := by rfl\n",
                    f"the specification end to end, k={k}"))
    return out


def loop(name: str, typ: str, step: str, reps: int, init: str,
         expect: str) -> str:
    """A fuel recursion carrying one accumulator, so two of these differ by
    exactly the operation in `step`."""
    return (f"def {name} : Nat -> {typ} -> {typ}\n"
            f"  | 0, acc => acc\n"
            f"  | k + 1, acc => {name} k ({step})\n"
            f"theorem t_{name} : {name} {reps} {init} = {expect} := by rfl\n")


def micro() -> list[tuple[str, str, str]]:
    out: list[tuple[str, str, str]] = []

    # ---- pure recursion, nothing else: the floor every loop below pays ----
    reps = 2000
    out.append(("R_nat", loop("rnat", "Nat", "acc", reps, "7", "7"),
                f"{reps} fuel steps, Nat accumulator, no operation"))

    # ---- one narrow operation per step, Nat against Int ----
    c64 = (1 << 63) | 0x9E3779B97F4A7C15
    m64 = (1 << 64) - 59
    acc = 7
    for _ in range(reps):
        acc = (acc + c64) % m64
    out.append(("A_nat",
                loop("anat", "Nat", f"(acc + {hx(c64)}) % {hx(m64)}",
                     reps, "7", hx(acc)),
                f"{reps} x (Nat add + Nat mod), 64-bit operands"))
    out.append(("A_int",
                loop("aint", "Int", f"(acc + {hx(c64)}) % {hx(m64)}",
                     reps, "7", hx(acc)),
                f"{reps} x (Int add + Int emod), 64-bit operands"))

    acc = 7
    for _ in range(reps):
        acc = (acc * c64) % m64
    out.append(("M_nat",
                loop("mnat", "Nat", f"(acc * {hx(c64)}) % {hx(m64)}",
                     reps, "7", hx(acc)),
                f"{reps} x (Nat mul + Nat mod), 64-bit operands"))
    out.append(("M_int",
                loop("mint", "Int", f"(acc * {hx(c64)}) % {hx(m64)}",
                     reps, "7", hx(acc)),
                f"{reps} x (Int mul + Int emod), 64-bit operands"))

    # ---- the same step at the widths the real computation uses ----
    for tag, bits, n in (("coeff", W_COEFF, 500),
                         ("mid", W_MID, 200),
                         ("big", W_BIG, 100)):
        cw = odd_hex(bits, 3)
        mw = odd_hex(bits, 7) | (1 << (bits - 1))
        acc = 7
        for _ in range(n):
            acc = (acc * cw) % mw
        out.append((f"M_int_{tag}",
                    loop(f"mi{tag}", "Int", f"(acc * {hx(cw)}) % {hx(mw)}",
                         n, "7", hx(acc)),
                    f"{n} x (Int mul + Int emod), {bits}-bit operands"))

    # ---- what the notation costs, as against the function it resolves to ----
    # `a * b` elaborates to `@HMul.hMul Int Int Int instHMul a b`, and before
    # the kernel reaches an accelerated operation it must unfold the `HMul.hMul`
    # projection, the `instHMul` definition, the `Mul.mul` projection and the
    # `Int.instMul` definition. The arguments differ every time, so no cache
    # can help. The `fib` entry on this challenge measured 2.22x from removing
    # exactly this. Each pair below performs identical arithmetic and differs
    # only in whether it is written with notation or with the function.
    reps = 2000
    c64 = (1 << 63) | 0x9E3779B97F4A7C15
    m64 = (1 << 64) - 59
    acc = 7
    for _ in range(reps):
        acc = (acc * c64) % m64
    out.append(("C_nat_notation",
                loop("cnatn", "Nat", f"(acc * {hx(c64)}) % {hx(m64)}",
                     reps, "7", hx(acc)),
                f"{reps} x Nat mul and mod written `a * b % m`"))
    out.append(("C_nat_direct",
                loop("cnatd", "Nat",
                     f"Nat.mod (Nat.mul acc {hx(c64)}) {hx(m64)}",
                     reps, "7", hx(acc)),
                f"{reps} x the same, written Nat.mod (Nat.mul ..)"))
    out.append(("C_int_notation",
                loop("cintn", "Int", f"(acc * {hx(c64)}) % {hx(m64)}",
                     reps, "7", hx(acc)),
                f"{reps} x Int mul and emod written `a * b % m`"))
    out.append(("C_int_direct",
                loop("cintd", "Int",
                     f"Int.emod (Int.mul acc {hx(c64)}) {hx(m64)}",
                     reps, "7", hx(acc)),
                f"{reps} x the same, written Int.emod (Int.mul ..)"))

    # and the subtraction, which is what the pseudo-remainder actually does:
    # `Int.sub` is itself defined as `m + (-n)`, so some of the chain is inside
    # core's own definition and cannot be avoided. This measures what is left.
    acc = 7
    for _ in range(reps):
        acc = (acc * c64 - c64) % m64
    out.append(("C_sub_notation",
                loop("csubn", "Int",
                     f"(acc * {hx(c64)} - {hx(c64)}) % {hx(m64)}",
                     reps, "7", hx(acc)),
                f"{reps} x Int mul, sub and emod, written with notation"))
    out.append(("C_sub_direct",
                loop("csubd", "Int",
                     f"Int.emod (Int.sub (Int.mul acc {hx(c64)}) "
                     f"{hx(c64)}) {hx(m64)}",
                     reps, "7", hx(acc)),
                f"{reps} x the same, written with Int.sub and Int.mul"))

    # ---- the equation compiler against an explicit recursor ----
    # A structurally recursive definition compiles to `brecOn`, which builds a
    # `below` structure the kernel then projects out of. An explicit `List.rec`
    # has none of that. Same arithmetic, same list.
    vals = [odd_hex(64, 400 + i) for i in range(24)]
    lit = ", ".join(hx(v) for v in vals)
    rounds = 200
    s = sum(vals) * rounds
    out.append(("C_eqn_compiler",
                f"def WS : List Int := [{lit}]\n"
                "def total : List Int -> Int\n"
                "  | [] => 0\n"
                "  | x :: xs => Int.add x (total xs)\n"
                "def reps : Nat -> Int\n"
                "  | 0 => 0\n"
                "  | k + 1 => Int.add (total WS) (reps k)\n"
                f"theorem t : reps {rounds} = {hx(s)} := by rfl\n",
                f"{rounds} x summing a 24-element list, equation compiler"))
    out.append(("C_recursor",
                f"def WS : List Int := [{lit}]\n"
                "def total (l : List Int) : Int :=\n"
                "  List.rec (motive := fun _ => Int) 0\n"
                "    (fun x _ ih => Int.add x ih) l\n"
                "def reps : Nat -> Int\n"
                "  | 0 => 0\n"
                "  | k + 1 => Int.add (total WS) (reps k)\n"
                f"theorem t : reps {rounds} = {hx(s)} := by rfl\n",
                f"{rounds} x the same, written as an explicit List.rec"))

    # ---- does a negative operand cost more than a positive one ----
    # `Int` is an inductive type with two constructors, so every operation is a
    # case analysis before it is arithmetic, and the `negSucc` side goes
    # through `negOfNat` and `subNatNat` where the `ofNat` side does not. Half
    # the coefficients in this problem are negative. Both loops below perform
    # one multiplication, one remainder and one addition per step at the same
    # width; only the sign of the accumulator differs.
    n = 500
    cw = odd_hex(W_COEFF, 3)
    mw = odd_hex(W_COEFF, 7) | (1 << (W_COEFF - 1))
    acc = 7
    for _ in range(n):
        acc = (acc * cw) % mw + mw
    out.append(("M_int_pos",
                loop("mipos", "Int",
                     f"(acc * {hx(cw)}) % {hx(mw)} + {hx(mw)}", n, "7",
                     hx(acc)),
                f"{n} x mul, emod, add with a POSITIVE accumulator, "
                f"{W_COEFF}-bit"))
    acc = 7
    for _ in range(n):
        acc = (acc * cw) % mw - mw
    out.append(("M_int_neg",
                loop("mineg", "Int",
                     f"(acc * {hx(cw)}) % {hx(mw)} - {hx(mw)}", n, "7",
                     hx(acc)),
                f"{n} x mul, emod, sub with a NEGATIVE accumulator, "
                f"{W_COEFF}-bit"))

    # ---- what does multiplying the widest intermediate by ONE cost ----
    # `pseudoRemainderGo` finishes with `scalePolynomial (lc ^ remaining)`, and
    # in the normal case `remaining` is zero, so the specification multiplies
    # every coefficient of the widest intermediate it ever holds by one: 276
    # times per judged case. Whether that is worth removing depends on whether
    # the kernel charges for a multiplication by one, which is this pair.
    n = 200
    big = odd_hex(W_BIG, 31)
    out.append(("M_one_big",
                loop("monebig", "Int", f"1 * (acc + 1)", n, hx(big),
                     hx(big + n)),
                f"{n} x (multiply by ONE, then add one), {W_BIG}-bit"))
    out.append(("M_one_ctl",
                loop("monectl", "Int", f"acc + 1", n, hx(big),
                     hx(big + n)),
                f"{n} x (add one), {W_BIG}-bit, the control for M_one_big"))

    # ---- division on its own, at the width the exact division runs at ----
    n = 100
    dv = odd_hex(W_BIG, 11)
    ds = odd_hex(W_BIG // 2, 13)
    acc = dv
    for _ in range(n):
        acc = (acc // ds) * ds + dv % ds       # keeps the width stationary
    out.append(("D_int_big",
                loop("dibig", "Int",
                     f"(acc / {hx(ds)}) * {hx(ds)} + {hx(dv % ds)}",
                     n, hx(dv), hx(acc)),
                f"{n} x (Int ediv + Int mul + Int add), "
                f"{W_BIG}-bit over {W_BIG // 2}-bit"))

    # ---- THE decisive pair: a pass over a list against one packed operation --
    # Both compute lcG * c - lcR * d on 24 coefficients of W_COEFF bits, the
    # work the pseudo-remainder does once per subresultant step. The list form
    # is the specification's; the packed form is the same arithmetic on one
    # integer, which is what a Kronecker-style representation would do.
    width = W_COEFF
    slots = 24
    lc_g = odd_hex(width, 17)
    lc_r = odd_hex(width, 19)
    xs = [odd_hex(width, 100 + i) for i in range(slots)]
    ys = [odd_hex(width, 200 + i) for i in range(slots)]
    passes = 100

    # the list version: build the list once, then run `passes` distinct passes
    # over it, summing every element so that nothing is left unforced and
    # nothing is answered from the kernel's cache.
    xs_lit = ", ".join(hx(v) for v in xs)
    ys_lit = ", ".join(hx(v) for v in ys)
    total = 0
    for j in range(passes):
        total += sum((lc_g + j) * c - lc_r * d for c, d in zip(xs, ys))
    list_src = (
        f"def XS : List Int := [{xs_lit}]\n"
        f"def YS : List Int := [{ys_lit}]\n"
        "def cancel (a b : Int) : List Int -> List Int -> List Int\n"
        "  | c :: cs, d :: ds => (a * c - b * d) :: cancel a b cs ds\n"
        "  | _, _ => []\n"
        "def total : List Int -> Int\n"
        "  | [] => 0\n"
        "  | x :: xs => x + total xs\n"
        "def reps : Nat -> Int\n"
        "  | 0 => 0\n"
        f"  | k + 1 => total (cancel ({hx(lc_g)} + Int.ofNat k) {hx(lc_r)} "
        "XS YS) + reps k\n"
        f"theorem t_list : reps {passes} = {hx(total)} := by rfl\n")
    out.append(("P_list", list_src,
                f"{passes} passes of lcG*c - lcR*d over a {slots}-element "
                f"list of {width}-bit Int, plus a sum of each result"))

    # the control for the same file: the summing pass alone, so the cancel
    # pass can be isolated from the forcing that makes it measurable.
    ctrl = sum(xs) * passes
    ctrl_src = (
        f"def XS : List Int := [{xs_lit}]\n"
        "def total : List Int -> Int\n"
        "  | [] => 0\n"
        "  | x :: xs => x + total xs\n"
        "def reps : Nat -> Int\n"
        "  | 0 => 0\n"
        "  | k + 1 => total XS + reps k\n"
        f"theorem t_ctrl : reps {passes} = {hx(ctrl)} := by rfl\n")
    out.append(("P_list_ctrl", ctrl_src,
                f"{passes} x summing the same {slots}-element list, the "
                f"control for P_list"))

    # the packed version: the identical arithmetic on one integer. The slot
    # width is 2*W + 2 so that no slot of the true product could overflow into
    # its neighbour; that is what a real packed design would have to reserve.
    slot = 2 * width + 2
    xp = sum(v << (slot * i) for i, v in enumerate(xs))
    yp = sum(v << (slot * i) for i, v in enumerate(ys))
    tot = 0
    for j in range(passes):
        tot += (lc_g + j) * xp - lc_r * yp
    packed_src = (
        f"def XP : Int := {hx(xp)}\n"
        f"def YP : Int := {hx(yp)}\n"
        "def reps : Nat -> Int\n"
        "  | 0 => 0\n"
        f"  | k + 1 => (({hx(lc_g)} + Int.ofNat k) * XP - {hx(lc_r)} * YP) "
        "+ reps k\n"
        f"theorem t_packed : reps {passes} = {hx(tot)} := by rfl\n")
    out.append(("P_packed", packed_src,
                f"{passes} x the same arithmetic on one packed integer of "
                f"{slots} slots of {slot} bits"))

    # ---- does a list recursion cost more per element when the list is long? --
    # Same number of elements processed, three list lengths. A rising total
    # means the kernel's structural recursion is not linear, which would make
    # the polynomial length itself a cost.
    for length, rounds in ((24, 96), (48, 48), (96, 24)):
        vals = [odd_hex(64, 300 + i) for i in range(length)]
        lit = ", ".join(hx(v) for v in vals)
        s = sum(vals) * rounds
        src = (f"def ZS : List Int := [{lit}]\n"
               "def total : List Int -> Int\n"
               "  | [] => 0\n"
               "  | x :: xs => x + total xs\n"
               "def reps : Nat -> Int\n"
               "  | 0 => 0\n"
               "  | k + 1 => total ZS + reps k\n"
               f"theorem t_len : reps {rounds} = {hx(s)} := by rfl\n")
        out.append((f"L_len{length}", src,
                    f"{rounds} x summing a {length}-element list "
                    f"({length * rounds} elements either way)"))

    return out


def probes() -> list[tuple[str, str, str]]:
    """Which primitives the kernel computes with GMP rather than by unfolding.

    A packed design needs `<<<`, `>>>` and `&&&` on numbers tens of thousands
    of bits wide. If any of those is reduced by recursion on the shift amount
    instead of by one library call, that route is closed before any proof is
    attempted. Each probe is one operation, so a cheap answer means accelerated
    and an expensive one means unfolded.
    """
    out = []
    m = 1000000007
    out.append(("Q_pow",
                f"theorem q : (2 ^ 3456 : Nat) % {m} = {pow(2, 3456) % m}"
                " := by rfl\n",
                "Nat.pow with a 3,456 exponent, as the setup does"))
    out.append(("Q_shiftl",
                f"theorem q : ((1 : Nat) <<< 83616) % {m} = "
                f"{(1 << 83616) % m} := by rfl\n",
                "Nat.shiftLeft by 83,616"))
    a = odd_hex(W_BIG, 23)
    out.append(("Q_shiftr",
                f"theorem q : (({hx(a)} : Nat) >>> 40000) % {m} = "
                f"{(a >> 40000) % m} := by rfl\n",
                "Nat.shiftRight of an 80,000-bit number"))
    mask = sum((1 << 64) - 1 << (192 * i) for i in range(400))
    out.append(("Q_land",
                f"theorem q : (({hx(a)} : Nat) &&& {hx(mask)}) % {m} = "
                f"{(a & mask) % m} := by rfl\n",
                "Nat.land of an 80,000-bit number with a lane mask"))
    out.append(("Q_lor",
                f"theorem q : (({hx(a)} : Nat) ||| {hx(mask)}) % {m} = "
                f"{(a | mask) % m} := by rfl\n",
                "Nat.lor of an 80,000-bit number with a lane mask"))
    b = odd_hex(W_BIG, 29)
    out.append(("Q_gcd",
                f"theorem q : (Nat.gcd {hx(a)} {hx(b)}) % {m} = "
                f"{__import__('math').gcd(a, b) % m} := by rfl\n",
                "Nat.gcd of two 80,000-bit numbers"))
    return out


# -------------------------------------------------------------------- emit ---
def emit(directory: pathlib.Path) -> int:
    directory.mkdir(parents=True, exist_ok=True)
    manifest = []

    (directory / "Base.lean").write_text(PREAMBLE + OPTIONS, encoding="utf-8")
    (directory / "Base_skip.lean").write_text(PREAMBLE + OPTIONS + SKIP,
                                              encoding="utf-8")
    manifest.append({"name": "Base", "note": "import and nothing else"})

    groups = [("judged", judged_cases()), ("breakdown", breakdown()),
              ("micro", micro()), ("probe", probes())]
    for group, items in groups:
        for name, body, note in items:
            if group == "micro":
                body = "namespace Bench\n" + body + "end Bench\n"
            (directory / f"{name}.lean").write_text(
                PREAMBLE + OPTIONS + body, encoding="utf-8")
            (directory / f"{name}_skip.lean").write_text(
                PREAMBLE + OPTIONS + SKIP + body, encoding="utf-8")
            manifest.append({"name": name, "group": group, "note": note})

    (directory / "manifest.json").write_text(
        json.dumps(manifest, indent=2), encoding="utf-8")
    print(f"  emitted {len(manifest)} benchmarks into {directory}")
    for item in manifest:
        print(f"      {item['name']:<14} {item.get('note', '')}")
    return 0


# ------------------------------------------------------------------ report ---
IREFS = re.compile(r"I\s+refs:\s+([\d,]+)")


def failed(path: pathlib.Path) -> bool:
    """A log carrying a Lean error is not a measurement of anything. A log that
    is not there at all was simply outside this run's scope, which is a
    different thing and must not be reported as a failure."""
    if not path.exists():
        return False
    text = path.read_text(errors="replace")
    return ("error:" in text) or ("MEASUREFAILED" in text)


def ireads(path: pathlib.Path) -> int | None:
    """The largest `I refs` in a callgrind log, which is the `lean` process:
    `lake` and the elan shim do nothing by comparison."""
    if not path.exists():
        return None
    best = None
    for match in IREFS.finditer(path.read_text(errors="replace")):
        value = int(match.group(1).replace(",", ""))
        best = value if best is None else max(best, value)
    return best


def report(directory: pathlib.Path) -> int:
    manifest = json.loads((directory / "manifest.json").read_text())
    base = ireads(directory / "Base.out")
    base_skip = ireads(directory / "Base_skip.out")
    if base is None:
        print("  no baseline measurement; nothing to report")
        return 1
    print(f"  baseline: import only, {base:>15,} instructions "
          f"(elaborator-only variant {base_skip if base_skip else 0:,})")
    print()
    print(f"  {'benchmark':<14} {'total':>15} {'elab only':>15} "
          f"{'KERNEL':>15}  note")
    rows = {}
    for item in manifest:
        name = item["name"]
        if name == "Base":
            continue
        full = ireads(directory / f"{name}.out")
        skip = ireads(directory / f"{name}_skip.out")
        bad = failed(directory / f"{name}.out")
        if bad:
            full = None
        kernel = None
        if full is not None and skip is not None:
            kernel = full - skip
        rows[name] = (full, skip, kernel)
        def f(x):
            return f"{x:,}" if x is not None else "--"
        mark = "  ERRORED  " if bad else "  "
        print(f"  {name:<14} {f(full):>15} {f(skip):>15} {f(kernel):>15}"
              f"{mark}{item.get('note', '')}")

    judged = [r for n, r in rows.items() if n.startswith("J")]
    have = [r[2] for r in judged if r[2] is not None]
    if have:
        print()
        print(f"  judged cases measured: {len(have)} of {len(judged)}")
        print(f"  SUM of kernel checks:  {sum(have):>15,}")
        print(f"  leaderboard, this file: {10_322_617_420:>14,}  "
              f"(submission 692, the specification)")
        if sum(have):
            print(f"  ratio instrument/board: "
                  f"{sum(have) / 10_322_617_420:.3f}")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--emit", type=pathlib.Path)
    ap.add_argument("--report", type=pathlib.Path)
    args = ap.parse_args()
    if args.emit:
        return emit(args.emit)
    if args.report:
        return report(args.report)
    ap.print_help()
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
