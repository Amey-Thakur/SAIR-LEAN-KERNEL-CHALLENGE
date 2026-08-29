#!/usr/bin/env python3
"""Build the social preview card for the SAIR Lean Kernel Challenge repository.

This is a different drawing from the animation. The animation is a dense
briefing that rewards a reader who stops on it; the preview is the card GitHub,
X and LinkedIn scale down to a thumbnail, so it carries one title, one line of
explanation and nothing that would turn to mud at a quarter of the size.

The geometry matches the sibling repositories exactly, measured from their
cards rather than guessed: a 1280 by 640 canvas, the mark and wordmark centred
on a 232 pixel span, a rule 344 pixels wide, and the footer on the same
baseline. check_layout asserts the important ones before the file is written.

    python .github/scripts/build_social_preview.py .github/social-preview.png

Pillow only.
"""
import sys
from pathlib import Path

from PIL import Image, ImageDraw, ImageFont

W, H = 1280, 640
BG = (0x34, 0x08, 0x25)
EDGE = (0x6B, 0x2F, 0x4F)
WHITE = (0xFF, 0xFF, 0xFF)
INK = (0xF5, 0xF5, 0xF5)
PALE = (0xD8, 0xD2, 0xD6)
ROSE = (0xC9, 0xA9, 0xB8)
DIM = (0xA5, 0x9C, 0xA1)

BLACK_FACE = "C:/Windows/Fonts/seguibl.ttf"    # Segoe UI Black, the title
UI = "C:/Windows/Fonts/segoeui.ttf"            # Segoe UI, wordmark and strapline
MONO = "C:/Windows/Fonts/consola.ttf"
# The flat mark, already at the size the card uses. The round badge in
# sair-mark.png carries a disc that reads as a smudge behind the pyramid once
# the card is scaled to a thumbnail, which is why the sibling previews draw
# the mark flat instead.
MARK = Path(__file__).resolve().parent.parent / "assets" / "sair-mark-flat.png"

TITLE = "Lean Kernel"
SUBTITLE = "An independent proof checker for Lean 4"
KEYWORDS = "export . typecheck . accept or reject"
FOOTER = "SAIR Challenge . CC BY 4.0 . github.com/Amey-Thakur"

# Anchors measured from the sibling cards.
MARK_W, MARK_H = 74, 64          # the triangle, ink 524..597 by 75..138
MARK_GAP = 13                    # to the left edge of the wordmark
LOGO_TOP = 75
TITLE_BASE = 300                 # every sibling title has its ink bottom here
SUB_TOP = 339
RULE_Y, RULE_W = 396, 344
KEY_TOP = 433
FOOT_TOP = 575

_fc = {}


def f(path, size):
    if (path, size) not in _fc:
        _fc[(path, size)] = ImageFont.truetype(path, size)
    return _fc[(path, size)]


_probe = ImageDraw.Draw(Image.new("RGB", (1, 1)))


def ink_box(text, font):
    """Ink extent in the same coordinates draw.text uses, so subtracting the
    box origin lands the ink exactly on an anchor. font.getmask reports
    against a different origin and placed every band about forty pixels low."""
    return _probe.textbbox((0, 0), text, font=font)


def draw_centred(d, text, font, fill, top):
    """Place text so its ink starts at `top` and is centred on the canvas.
    Both coordinates are rounded, because a fractional origin moves the ink a
    pixel off the anchor and the layout check is exact."""
    x0, y0, x1, y1 = ink_box(text, font)
    d.text((round((W - (x1 - x0)) / 2 - x0), round(top - y0)), text,
           font=font, fill=fill)
    return x1 - x0, y1 - y0


def fit_title(text, target_w, max_size=124):
    """Largest Segoe UI Black that keeps the title inside target_w."""
    size = max_size
    while size > 24:
        x0, _, x1, _ = ink_box(text, f(BLACK_FACE, size))
        if x1 - x0 <= target_w:
            return f(BLACK_FACE, size)
        size -= 1
    return f(BLACK_FACE, 24)


def build():
    im = Image.new("RGB", (W, H), BG)
    d = ImageDraw.Draw(im)

    # Mark and wordmark, together centred, on the sibling 232 pixel span.
    word = f(UI, 73)
    wx0, wy0, wx1, wy1 = ink_box("SAIR", word)
    ww = wx1 - wx0
    total = MARK_W + MARK_GAP + ww
    x = (W - total) / 2
    mark = Image.open(MARK).convert("RGBA")
    if mark.size != (MARK_W, MARK_H):
        mark = mark.resize((MARK_W, MARK_H), Image.LANCZOS)
    im.paste(mark, (int(round(x)), LOGO_TOP), mark)
    # On the sibling cards the wordmark is not centred against the mark, it
    # sits on the mark's own bottom edge, which is what stops the pair from
    # looking as though the letters are floating.
    d.text((round(x + MARK_W + MARK_GAP - wx0),
            round(LOGO_TOP + MARK_H - (wy1 - wy0) - wy0)),
           "SAIR", font=word, fill=WHITE)

    # The title is placed by its bottom edge, not its top, so that a taller or
    # shorter word still sits on the same line as the sibling cards.
    title = fit_title(TITLE, 700)
    _, ty0, _, ty1 = ink_box(TITLE, title)
    draw_centred(d, TITLE, title, INK, TITLE_BASE - (ty1 - ty0))

    draw_centred(d, SUBTITLE, f(UI, 29), PALE, SUB_TOP)

    d.line([(W - RULE_W) / 2, RULE_Y, (W + RULE_W) / 2, RULE_Y], fill=EDGE)

    draw_centred(d, KEYWORDS, f(MONO, 26), ROSE, KEY_TOP)
    draw_centred(d, FOOTER, f(MONO, 21), DIM, FOOT_TOP)
    return im


def check_layout(im):
    """The card is only a sibling if it lands on the sibling geometry."""
    import numpy as np
    a = np.asarray(im.convert("RGB")).astype(int)
    mask = (np.abs(a - a[5, 5]).sum(axis=2) > 18)
    rows = np.where(mask.any(axis=1))[0]
    bands, s, prev = [], rows[0], rows[0]
    for r in rows[1:]:
        if r - prev > 6:
            bands.append((s, prev))
            s = r
        prev = r
    bands.append((s, prev))
    problems = []
    if len(bands) != 6:
        problems.append(f"expected 6 bands, drew {len(bands)}")
    for y0, y1 in bands:
        cols = np.where(mask[y0:y1 + 1].any(axis=0))[0]
        centre = (cols[0] + cols[-1] + 1) / 2
        if abs(centre - W / 2) > 2.0:
            problems.append(f"band {y0}-{y1} centred on {centre:.1f}, not {W / 2}")
    # One pixel of slack: the faintest antialiased row of a glyph can fall
    # under the detector's threshold, which shifts a measured band by one
    # without the text having moved.
    if bands and abs(bands[0][0] - LOGO_TOP) > 1:
        problems.append(f"logo ink starts at {bands[0][0]}, not {LOGO_TOP}")
    if bands and abs(bands[-1][0] - FOOT_TOP) > 1:
        problems.append(f"footer ink starts at {bands[-1][0]}, not {FOOT_TOP}")
    if problems:
        raise SystemExit("layout drifted from the sibling cards:\n  "
                         + "\n  ".join(problems))
    return bands


if __name__ == "__main__":
    out = Path(sys.argv[1] if len(sys.argv) > 1 else "social-preview.png")
    card = build()
    for y0, y1 in check_layout(card):
        print(f"  band y={y0}-{y1}")
    out.parent.mkdir(parents=True, exist_ok=True)
    card.save(out)
    print(f"  {out}: {out.stat().st_size // 1024} KB, {card.size[0]}x{card.size[1]}")
