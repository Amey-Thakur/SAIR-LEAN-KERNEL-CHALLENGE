#!/usr/bin/env python3
"""Check every quantity the manuscript quotes against the data behind it.

Tables and figures are generated and cannot drift. The sentences around them are
written by hand, so a ratio that was right when it was typed and wrong after the
model was re-run would survive both the compiler and the figure check. This
script recomputes each quoted quantity from data/step_model.json and
data/wall_time.json and requires main.tex to contain it, formatted as the paper
formats numbers.

Usage: python tools/check_numbers.py
"""
from __future__ import annotations

import json
import math
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parents[1]
TEX = (ROOT / "main.tex").read_text(encoding="utf-8")
STEPS = json.loads((ROOT / "data" / "step_model.json").read_text(encoding="utf-8"))
WALL = json.loads((ROOT / "data" / "wall_time.json").read_text(encoding="utf-8"))

failures: list[str] = []
checked = 0


def grouped(n: int) -> str:
    """The paper writes a thousands separator as LaTeX, not as a comma."""
    return f"{n:,}".replace(",", "{,}")


def want(text: str, what: str) -> None:
    """main.tex must contain this string somewhere."""
    global checked
    checked += 1
    if text not in TEX:
        failures.append(f"{what}: {text!r} does not appear in main.tex")


def want_number(value: int, what: str) -> None:
    """Same, for a bare integer inside display maths, where the surrounding
    spacing macros vary and matching the literal string would be brittle."""
    global checked
    checked += 1
    if not re.search(r"(?<![0-9.,{])" + str(value) + r"(?![0-9.,}])", TEX):
        failures.append(f"{what}: {value} does not appear in main.tex")


def main() -> int:
    rows = {r["n"]: r for r in STEPS["rows"]}
    totals = STEPS["totals"]
    lo, hi = min(rows), max(rows)

    # ---- the answers, and the step counts, as the table prints them --------
    for n, r in rows.items():
        want(grouped(r["answer"]), f"partition count at n={n}")
        for key in ("spec", "list", "packed"):
            want(grouped(r[key]), f"{key} steps at n={n}")

    # ---- totals -----------------------------------------------------------
    for key in ("spec", "list", "packed"):
        want(grouped(totals[key]), f"total {key} steps")

    # ---- every ratio the table's last two columns print --------------------
    for n, r in rows.items():
        for key in ("spec", "list"):
            ratio = round(r[key] / r["packed"])
            want(f"{ratio}$\\times$", f"{key}-over-packed ratio at n={n}")
    for key in ("spec", "list"):
        want(f"{round(totals[key] / totals['packed'])}$\\times$",
             f"total {key}-over-packed ratio")

    # ---- the power-law exponents quoted in Section 3.3 ---------------------
    span = math.log(hi / lo)
    for key, name in (("packed", "packed"), ("list", "lists"),
                      ("spec", "specification")):
        e = math.log(rows[hi][key] / rows[lo][key]) / span
        want(f"${e:.2f}$", f"fitted exponent for {name}")

    # ---- the table-growth and cost-growth factors in Section 6.2 ----------
    cells = (hi + 1) ** 2 / (lo + 1) ** 2
    want(f"${cells:.1f}$", "growth in table cells from n=14 to n=36")
    want(f"${rows[hi]['packed'] / rows[lo]['packed']:.1f}$",
         "growth in packed cost from n=14 to n=36")

    # ---- field widths and row widths --------------------------------------
    r = rows[hi]
    want(f"${r['field_bits']}$ bits", "field width at n=36")
    want(f"${r['wide_field_bits']}$-bit field", "the wider field width")
    want(grouped(r["row_bits"]), "packed row width in bits")
    want(grouped(r["wide_field_bits"] * (hi + 1)),
         "row width in bits under the wider field")

    # ---- the harmonic sum of equation (14) --------------------------------
    want_number(sum(hi // d for d in range(1, hi + 1)),
                "shift-and-add pairs at n=36")

    # ---- wall times, exactly as the table prints them ---------------------
    for design, series in WALL["designs"].items():
        for n, t in zip(WALL["endpoints"], series):
            want(f"{t:.2f}", f"{design} wall time at n={n}")
    for design, total in WALL["totals"].items():
        want(f"{total:.2f}", f"{design} wall-time total")

    # ---- the two wall-time ratios quoted in Section 6.3 -------------------
    packed_total = WALL["totals"]["packed"]
    for design, name in (("specification", "specification"), ("lists", "lists")):
        want(f"${round(WALL['totals'][design] / packed_total)}$",
             f"wall-time ratio, {name} over packed")

    # ---- the width study ---------------------------------------------------
    ws = WALL["width_study"]
    wide, tight = ws["width_n_bits_n1_plus_1"], ws["width_2n_plus_1"]
    for n, a, b in zip(ws["n"], wide, tight):
        want(f"{a:.2f}", f"wide-width wall time at n={n}")
        want(f"{b:.2f}", f"tight-width wall time at n={n}")
    want(f"${sum(wide) / sum(tight):.1f}$", "width-study ratio over all sizes")
    want(f"${wide[0] / tight[0]:.1f}$", "width ratio at the smallest size")
    want(f"${wide[-1] / tight[-1]:.1f}$", "width ratio at the largest size")

    # ---- the packed step count is identical at both widths ----------------
    if r["packed"] != r["packed_wide_width"]:
        failures.append("the step model does distinguish the two widths, so the "
                        "claim in Section 6.3 is wrong")
    else:
        want("$1.00$", "the step model's ratio between the two widths")

    # ---- the sentence that says the wider row is three times as wide ------
    factor = r["wide_field_bits"] / r["field_bits"]
    if not 2.5 <= factor < 3.5:
        failures.append(f"the wider field is {factor:.2f} times as wide, so "
                        f"'three times as many machine words' is wrong")

    # ---- the width-bound slack table --------------------------------------
    slack = json.loads(
        (ROOT / "data" / "bound_slack.json").read_text(encoding="utf-8"))
    for s in slack["rows"]:
        want(grouped(s["largest_cell"]), f"largest cell at n={s['n']}")
        want(str(s["bits_needed"]), f"bits needed at n={s['n']}")
        want(str(s["tighter_width"]), f"tighter width at n={s['n']}")
        want(f"{s['proved_over_needed']:.1f}$\\times$",
             f"waste ratio at n={s['n']}")
    lo = min(s["proved_over_needed"] for s in slack["rows"])
    hi = max(s["proved_over_needed"] for s in slack["rows"])
    want(f"${lo:.1f}$ and ${hi:.1f}$", "the range of the waste ratio")

    # the two factors the prose quotes about the tighter bound
    last = slack["rows"][-1]
    want(f"${last['proved_width'] / last['tighter_width']:.1f}$",
         "proved width over tighter width at n=36")
    want(f"${last['tighter_width'] / last['bits_needed']:.1f}$",
         "tighter width over bits needed at n=36")

    # ---- report -----------------------------------------------------------
    print(f"  checked {checked} quantities against the data")
    for f in failures:
        print(f"  FAIL  {f}")
    if not failures:
        print("  ok    every quoted number matches")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
