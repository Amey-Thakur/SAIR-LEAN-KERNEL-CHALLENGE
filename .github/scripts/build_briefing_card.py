#!/usr/bin/env python3
"""Build the animated card for the SAIR Lean Kernel Challenge repository.

Original artwork in the palette these repositories already use, so the animation
can live in the repository and be attached to a post without borrowing the
competition site's own canvas.

Every number on this card is real. The exit codes are the arena contract, the
declaration shown is a genuine constant from a Lean 4 export, and nothing here
claims a score the competition has not published.

    python .github/scripts/build_animation.py .github/assets

Pillow only.
"""
import sys
from pathlib import Path

from PIL import Image, ImageDraw, ImageFont

W, H = 1200, 630
BG = (0x34, 0x08, 0x25)
PANEL = (0x3E, 0x0E, 0x2C)
EDGE = (0x6B, 0x2F, 0x4F)
INK = (0xF5, 0xF5, 0xF5)
DIM = (0xA5, 0x9C, 0xA1)
ROSE = (0xC9, 0xA9, 0xB8)
PALE = (0xD8, 0xD2, 0xD6)
GREEN = (0x2E, 0xA0, 0x43)
FRAMES, MS = 30, 90
M = 56

MONO = "C:/Windows/Fonts/consola.ttf"
SEMI = "C:/Windows/Fonts/seguisb.ttf"
UI = "C:/Windows/Fonts/segoeui.ttf"
MARK = Path(__file__).resolve().parent.parent / "assets" / "sair-mark.png"

_fc = {}


def f(path, size):
    if (path, size) not in _fc:
        _fc[(path, size)] = ImageFont.truetype(path, size)
    return _fc[(path, size)]


# A declaration in the shape the export format carries it: a name, a type and
# a value, each an index into the term table the checker has to rebuild.
# Consolas has no glyph for the universal quantifier, so the type is written
# in the arrow form Lean also accepts, and check_glyphs keeps it that way.
DECL = [
    "#DEF 412 Nat.add_comm",
    "  type  (n m : Nat) \u2192 n + m = m + n",
    "  value fun n m => Nat.rec \u2026",
]

# The arena contract, verbatim.
CODES = [("0", "accepted"), ("1", "rejected"), ("2", "declined")]


def panel(d, box, active=False):
    d.rounded_rectangle(box, radius=12, fill=PANEL,
                        outline=ROSE if active else EDGE, width=2 if active else 1)


def head(im, d, title, sub):
    mark = Image.open(MARK).convert("RGBA").resize((56, 56), Image.LANCZOS)
    im.paste(mark, (M, 26), mark)
    # wordmark and strapline together span the same 26..82 band as the mark
    d.text((M + 74, 22), "SAIR", font=f(SEMI, 30), fill=INK)
    d.text((M + 76, 60), "Foundation for Science and AI Research", font=f(UI, 16), fill=DIM)
    d.text((M, 100), title, font=f(SEMI, 46), fill=INK)
    d.text((M + 2, 158), sub, font=f(UI, 21), fill=ROSE)
    d.line([M, 196, W - M, 196], fill=EDGE)


def stats(d, y, cells):
    """A rule, then figure-over-label blocks justified with equal gaps between."""
    d.line([M, y, W - M, y], fill=EDGE)
    fb, fs = f(SEMI, 34), f(UI, 16)
    widths = [max(d.textlength(b, font=fb), d.textlength(s, font=fs)) for b, s in cells]
    gap = ((W - 2 * M) - sum(widths)) / (len(cells) - 1) if len(cells) > 1 else 0
    x = float(M)
    for (big, small), w in zip(cells, widths):
        d.text((x, y + 20), big, font=fb, fill=INK)
        d.text((x, y + 66), small, font=fs, fill=DIM)
        x += w + gap


def foot(d, competition):
    """One line, three zones: who made it, what it is, where to find more."""
    d.line([M, H - 62, W - M, H - 62], fill=EDGE)
    y = H - 42
    d.text((M, y), "Amey Thakur", font=f(SEMI, 22), fill=INK)
    cw = d.textlength(competition, font=f(UI, 19))
    d.text(((W - cw) / 2, y + 3), competition, font=f(UI, 19), fill=PALE)
    link = "github.com/Amey-Thakur"
    d.text((W - M - d.textlength(link, font=f(MONO, 17)), y + 4), link,
           font=f(MONO, 17), fill=ROSE)


def pipeline(d, t, boxes):
    x, wbox = M, (W - 2 * M - 2 * 52) // 3      # three boxes and two gaps, flush to both margins
    for k, (a, b) in enumerate(boxes):
        on = k <= (t * 3) % 3 < k + 1
        panel(d, [x, 214, x + wbox, 320], active=on)
        d.text((x + 20, 240), a, font=f(MONO, 20), fill=INK if on else PALE)
        d.text((x + 20, 274), b, font=f(UI, 15), fill=ROSE if on else DIM)
        if k < 2:
            x0, x1 = x + wbox + 6, x + wbox + 46
            d.line([x0, 267, x1, 267], fill=EDGE, width=2)
            travel = (t * 2 + k * 0.5) % 1.0
            dx = x0 + (x1 - x0) * travel
            d.ellipse([dx - 4, 263, dx + 4, 271], fill=ROSE)
        x += wbox + 52


def lean_kernel(i):
    t = i / FRAMES
    im = Image.new("RGB", (W, H), BG)
    d = ImageDraw.Draw(im)
    head(im, d, "Lean Kernel",
         "Can a proof checker run faster without being trusted less?")
    pipeline(d, t, [("export.ndjson", "lean4export, one line per item"),
                    ("kernel", "rebuild, infer, whnf, defeq"),
                    ("exit code", "0 accept, 1 reject, 2 decline")])

    # One panel across the full column, the way the sibling cards carry code.
    panel(d, [M, 346, W - M, 452])
    d.text((M + 20, 358), "a declaration the checker rebuilds from the export, then verifies",
           font=f(UI, 13), fill=DIM)
    for k, ln in enumerate(DECL[:2]):
        d.text((M + 20, 384 + k * 24), ln, font=f(MONO, 15), fill=ROSE if k == 0 else PALE)
    d.text((M + 20, 432), DECL[2] + " ·" * (int(t * 4) % 4), font=f(MONO, 15), fill=PALE)

    stats(d, 470, [("NDJSON", "the export it reads"), ("3.1.0", "export format version"),
                   ("0  1  2", "the only exit codes"),
                   ("Lean 4", "the kernel checked")])
    foot(d, "Lean Kernel Challenge")
    return im


def check_glyphs():
    """A missing glyph draws as a blank box, which is worse than a plainer
    notation, so every character the mono font is asked to draw is checked
    against it before any frame is rendered."""
    mono = f(MONO, 15)
    missing = set()
    for line in DECL + [c for pair in CODES for c in pair]:
        for ch in line:
            if ch != " " and mono.getmask(ch).getbbox() is None:
                missing.add(ch)
    if missing:
        raise SystemExit("mono font lacks glyphs: "
                         + " ".join(f"{c!r} ({hex(ord(c))})" for c in sorted(missing)))


BUILDS = {"lean-kernel.gif": lean_kernel}

if __name__ == "__main__":
    out = Path(sys.argv[1] if len(sys.argv) > 1 else ".")
    out.mkdir(parents=True, exist_ok=True)
    check_glyphs()
    for name, fn in BUILDS.items():
        frames = [fn(i).convert("P", palette=Image.ADAPTIVE, colors=64) for i in range(FRAMES)]
        p = out / name
        frames[0].save(p, save_all=True, append_images=frames[1:], duration=MS, loop=0,
                       optimize=False, disposal=2)
        print(f"  {name}: {p.stat().st_size // 1024} KB, {FRAMES} frames")
