# ==============================================================================
# File: build_animation.py
# Description: Builds the repository card in the visual language of the SAIR
#   Foundation's own hero art for this competition: a vertical copper to
#   aubergine gradient, white line work, and the three stages of the contract
#   read left to right. A Lean submission goes in, the kernel decides, the
#   instruction count is measured. Every coordinate below is measured off
#   SAIR's 1920x1080 original and mapped through one scale, so the proportions
#   are theirs rather than a redrawing by eye. The pipeline is centred on the
#   card and the top and bottom margins are equal, which the original does not
#   need to do because it sits behind page copy.
# Usage: python .github/scripts/build_animation.py .github/assets
# Tech Stack: Python 3.10+, Pillow
# ==============================================================================

import math
import os
import sys

from PIL import Image, ImageDraw, ImageFont

W, H = 1200, 600
SS = 3                       # supersample: Pillow does not antialias strokes
FRAMES, DURATION = 30, 60

TOP = (0x8F, 0x57, 0x43)     # sampled from the top row of the SAIR hero
BOT = (0x34, 0x08, 0x25)     # and its bottom row, which is the SAIR card colour
INK = (255, 255, 255)
STROKE = 4

HERE = os.path.dirname(os.path.abspath(__file__))
ASSETS = os.path.join(HERE, "..", "assets")
UIB = "C:/Windows/Fonts/segoeuib.ttf"
UIL = "C:/Windows/Fonts/segoeuil.ttf"

# -- mapping from SAIR's frame to this card ---------------------------------
# The pipeline spans x 252 to 1712 in the original and is given a 72px margin
# each side here, which fixes the scale. The vertical mapping then places the
# logo top and the base line an equal distance from the card's edges.

S = 1056 / 1460.0
MARGIN = 72
TOP_REF, BOTTOM_REF = 87, 725   # wordmark top, and the chip's lowest pin
VPAD = (H - (BOTTOM_REF - TOP_REF) * S) / 2


def x(v):
    return (v - 252) * S + MARGIN


def y(v):
    return (v - TOP_REF) * S + VPAD


def lx(v):
    """The logo sits left of the pipeline in the original, so it keeps its own
    origin and is aligned to the same margin."""
    return (v - 72) * S + MARGIN


_scratch = ImageDraw.Draw(Image.new("RGB", (8, 8)))


def f(path, size):
    """Fonts are built in supersampled units so that a size given in card
    pixels comes out the size it says."""
    return ImageFont.truetype(path, max(1, int(round(size * SS))))


def fit(path, text, target):
    """The font size whose rendered width matches a width measured off the
    original, so the type scales with the art instead of being guessed."""
    lo, hi = 4.0, 200.0
    for _ in range(40):
        mid = (lo + hi) / 2
        w = _scratch.textlength(text, font=f(path, mid)) / SS
        if w < target:
            lo = mid
        else:
            hi = mid
    return (lo + hi) / 2


def bg_at(py):
    t = max(0.0, min(1.0, py / (H - 1.0)))
    return tuple(round(TOP[i] + (BOT[i] - TOP[i]) * t) for i in range(3))


def dim(py, amount):
    """White faded toward the background behind it, so a mark can recede
    without needing per-pixel alpha in a GIF."""
    b = bg_at(py)
    return tuple(round(b[i] + (INK[i] - b[i]) * amount) for i in range(3))


def ease(t):
    return t * t * (3 - 2 * t)


def span(t, a, b):
    if t <= a:
        return 0.0
    if t >= b:
        return 1.0
    return ease((t - a) / (b - a))


def along(points, progress):
    """The first `progress` of a polyline by arc length, so a stroke can be
    drawn on rather than appearing all at once."""
    if progress <= 0:
        return []
    if progress >= 1:
        return list(points)
    segs = [math.dist(points[i], points[i + 1]) for i in range(len(points) - 1)]
    want = sum(segs) * progress
    out = [points[0]]
    for i, d in enumerate(segs):
        if want <= d:
            u = want / d if d else 0
            out.append((points[i][0] + (points[i + 1][0] - points[i][0]) * u,
                        points[i][1] + (points[i + 1][1] - points[i][1]) * u))
            break
        out.append(points[i + 1])
        want -= d
    return out


def rounded_path(points, r):
    """A closed polygon with its corners replaced by arcs, which is how the
    document outline keeps rounded corners either side of its diagonal cut."""
    out = []
    n = len(points)
    for i in range(n):
        p0, p1, p2 = points[i - 1], points[i], points[(i + 1) % n]
        v1 = (p0[0] - p1[0], p0[1] - p1[1])
        v2 = (p2[0] - p1[0], p2[1] - p1[1])
        l1 = math.hypot(*v1) or 1.0
        l2 = math.hypot(*v2) or 1.0
        k = min(r, l1 / 2, l2 / 2)
        a = (p1[0] + v1[0] / l1 * k, p1[1] + v1[1] / l1 * k)
        b = (p1[0] + v2[0] / l2 * k, p1[1] + v2[1] / l2 * k)
        out.append(a)
        for j in range(1, 7):
            u = j / 7.0
            m1 = (a[0] + (p1[0] - a[0]) * u, a[1] + (p1[1] - a[1]) * u)
            m2 = (p1[0] + (b[0] - p1[0]) * u, p1[1] + (b[1] - p1[1]) * u)
            out.append((m1[0] + (m2[0] - m1[0]) * u, m1[1] + (m2[1] - m1[1]) * u))
        out.append(b)
    out.append(out[0])
    return out


class Pen:
    def __init__(self, draw):
        self.d = draw

    def line(self, pts, colour=INK, width=STROKE, joint="curve"):
        if len(pts) < 2:
            return
        self.d.line([(p[0] * SS, p[1] * SS) for p in pts], fill=colour,
                    width=int(round(width * SS)), joint=joint)

    def rrect(self, box, r, colour=INK, width=STROKE):
        self.d.rounded_rectangle([box[0] * SS, box[1] * SS,
                                  box[2] * SS, box[3] * SS],
                                 radius=r * SS, outline=colour,
                                 width=int(round(width * SS)))

    def circle(self, cx, cy, r, colour=INK, width=STROKE):
        self.d.ellipse([(cx - r) * SS, (cy - r) * SS,
                        (cx + r) * SS, (cy + r) * SS],
                       outline=colour, width=int(round(width * SS)))

    def dashes(self, px, y0, y1, dash, gap, phase, colour=INK, width=STROKE):
        period = dash + gap
        v = y0 - period + (phase % period)
        while v < y1:
            a, b = max(v, y0), min(v + dash, y1)
            if b > a:
                self.line([(px, a), (px, b)], colour, width, None)
            v += period

    def text(self, pos, s, font, colour=INK, anchor="la", tracking=0.0):
        if not tracking:
            self.d.text((pos[0] * SS, pos[1] * SS), s, font=font,
                        fill=colour, anchor=anchor)
            return
        widths = [self.d.textlength(c, font=font) for c in s]
        total = sum(widths) + tracking * SS * (len(s) - 1)
        px = pos[0] * SS
        if anchor[0] == "m":
            px -= total / 2
        elif anchor[0] == "r":
            px -= total
        for c, w in zip(s, widths):
            self.d.text((px, pos[1] * SS), c, font=font, fill=colour,
                        anchor="l" + anchor[1])
            px += w + tracking * SS


# -- type, sized from the widths measured on the original -------------------

FS_SUB = fit(UIB, "LEAN SUBMISSION", 181 * S)
FS_EQ = fit(UIB, "f x = y", 172 * S)
FS_KERNEL = fit(UIB, "KERNEL", 192 * S)
FS_COUNT = fit(UIB, "Instruction count", 280 * S)


# -- the three stages -------------------------------------------------------

def stage_document(pen, t):
    x0, y0, x1, y1 = x(252), y(337), x(537), y(712)
    fold = 67 * S
    pen.line(rounded_path([(x0, y0), (x1 - fold, y0), (x1, y0 + fold),
                           (x1, y1), (x0, y1)], 16 * S))
    pen.line([(x1 - fold, y0), (x1 - fold, y0 + fold), (x1, y0 + fold)])

    pen.text((x(277), y(369)), "LEAN SUBMISSION", f(UIB, FS_SUB), INK, "lt")
    pen.text((x(391), y(474)), "f x = y", f(UIB, FS_EQ), INK, "mm")
    pen.line([(x(300), y(541)), (x(489), y(541))])

    bx0, by0, bx1, by1 = x(298), y(594), x(363), y(659)
    pen.rrect((bx0, by0, bx1, by1), 7 * S)
    w = bx1 - bx0
    tick = [(bx0 + 0.20 * w, by0 + 0.50 * w), (bx0 + 0.42 * w, by0 + 0.72 * w),
            (bx0 + 0.82 * w, by0 + 0.24 * w)]
    p = span(t, 0.02, 0.18) - span(t, 0.88, 1.0)
    pen.line(along(tick, p))

    pen.line([(x(381), y(612)), (x(489), y(612))])
    pen.line([(x(381), y(650)), (x(452), y(650))])


def stage_chip(pen, t):
    bx0, by0, bx1, by1 = x(832), y(372), x(1142), y(684)
    pen.rrect((bx0, by0, bx1, by1), 68 * S)
    leg = 41 * S
    for i, v in enumerate((904, 966.5, 1028.5, 1091)):
        a = 0.55 + 0.45 * (0.5 + 0.5 * math.sin(2 * math.pi * (t - i * 0.07)))
        pen.line([(x(v), by0), (x(v), by0 - leg)], dim(by0, a))
        pen.line([(x(v), by1), (x(v), by1 + leg)], dim(by1, a))
    for i, v in enumerate((438, 500.5, 562.5, 625)):
        a = 0.55 + 0.45 * (0.5 + 0.5 * math.sin(2 * math.pi * (t - i * 0.07)))
        pen.line([(bx0, y(v)), (bx0 - leg, y(v))], dim(y(v), a))
        pen.line([(bx1, y(v)), (bx1 + leg, y(v))], dim(y(v), a))

    pen.text((x(988.5), y(444.5)), "KERNEL", f(UIB, FS_KERNEL), INK, "mm")

    cx, cy, r = x(987), y(562.5), 51.5 * S
    pen.circle(cx, cy, r)
    check = [(cx - 0.44 * r, cy + 0.02 * r), (cx - 0.12 * r, cy + 0.36 * r),
             (cx + 0.46 * r, cy - 0.36 * r)]
    pen.line(along(check, span(t, 0.36, 0.56) - span(t, 0.90, 1.0)))


def stage_gauge(pen, t):
    x0, y0, x1, y1 = x(1433), y(334), x(1653), y(611)
    pen.rrect((x0, y0, x1, y1), 30 * S)
    cx, half = x(1543), 65 * S
    for i, v in enumerate((379, 450.3, 521.7, 593)):
        ty = y(v)
        lit = (t * 4.0) % 4.0
        near = min(abs(lit - i), 4 - abs(lit - i))
        pen.line([(cx - half, ty), (cx + half, ty)],
                 dim(ty, 0.62 + 0.38 * max(0.0, 1.0 - near)))

    # the column carries on below as dashes marching down: the count coming in
    for px in (x0, x1):
        pen.dashes(px, y(619), y(690), 11 * S, 6 * S, t * 3 * 17 * S,
                   dim(y(655), 0.85))
    pen.line([(x(1420), y(700)), (x(1666), y(700))])

    ax = x(1690)
    bob = 3 * math.sin(2 * math.pi * t)
    ay0, ay1 = y(444) + bob, y(595) + bob
    head = 22 * S
    pen.line([(ax, ay0), (ax, ay1)])
    pen.line([(ax - head, ay1 - head), (ax, ay1), (ax + head, ay1 - head)])


def arrow(pen, t, a, b, delay):
    """The arrow as SAIR draws it, with a pulse running along the shaft. The
    shaft is very slightly held back from white so the pulse has something to
    be brighter than."""
    my = y(542)
    length, half = 28 * S, 30 * S
    pen.line([(a, my), (b, my)], dim(my, 0.78))
    pen.line([(b - length, my - half), (b, my), (b - length, my + half)])
    u = ((t - delay) % 1.0) / 0.32
    if u < 1.0:
        tip = a + (b - length - a) * ease(u)
        pen.line([(max(a, tip - 24 * S), my), (tip, my)], INK, STROKE + 1)


# -- the card ---------------------------------------------------------------

def background():
    im = Image.new("RGB", (1, H))
    px = im.load()
    for py in range(H):
        px[0, py] = bg_at(py)
    return im.resize((W * SS, H * SS), Image.BILINEAR)


BG = background()


def logo(im):
    """The real mark and wordmark, lifted from SAIR's own artwork.

    Setting the wordmark in a substitute face was never going to be right: it
    is a specific typeface, and an approximation of a logo reads as a mistake
    rather than as a homage. This is their image, keyed off the gradient it was
    drawn on and recomposited onto ours."""
    art = Image.open(os.path.join(ASSETS, "sair-logo.png")).convert("RGBA")
    w = 303 * S                                  # the width it has in the hero
    h = round(art.height * (w / art.width))
    art = art.resize((round(w * SS), h * SS), Image.LANCZOS)
    im.paste(art, (round(lx(72) * SS), round(y(87) * SS)), art)


def frame(i):
    t = i / FRAMES
    im = BG.copy()
    pen = Pen(ImageDraw.Draw(im))

    logo(im)
    pen.text((x(1404), y(248)), "Instruction count", f(UIB, FS_COUNT), INK, "lt")

    stage_document(pen, t)
    arrow(pen, t, x(631), x(724), 0.16)
    stage_chip(pen, t)
    arrow(pen, t, x(1278), x(1370), 0.58)
    stage_gauge(pen, t)

    return im.resize((W, H), Image.LANCZOS)


def check_glyphs():
    """A missing glyph is a hollow box, and a hollow box ships silently."""
    missing = set()
    for face in (UIB,):
        font = f(face, 24)
        for line in ("LEAN SUBMISSION", "f x = y", "KERNEL",
                     "Instruction count"):
            for ch in line:
                if ch != " " and font.getmask(ch).getbbox() is None:
                    missing.add((os.path.basename(face), ch))
    if missing:
        raise SystemExit("font is missing glyphs: " + repr(sorted(missing)))


def check_layout(im):
    """The pipeline is centred, the margins match, and nothing touches an edge."""
    import numpy as np
    a = np.asarray(im.convert("RGB")).astype(int)
    ink = (a.min(axis=2) > 170) & ((a.max(axis=2) - a.min(axis=2)) < 45)
    rows = np.where(ink.any(axis=1))[0]
    body = ink[int(y(300)):, :]
    bcols = np.where(body.any(axis=0))[0]
    left, right = int(bcols.min()), int(W - 1 - bcols.max())
    top, bottom = int(rows.min()), int(H - 1 - rows.max())
    print(f"  pipeline margins  left {left}  right {right}")
    print(f"  card margins      top {top}  bottom {bottom}")
    if abs(left - right) > 2:
        raise SystemExit(f"pipeline is not centred: {left} vs {right}")
    if abs(top - bottom) > 4:
        raise SystemExit(f"card is not balanced: {top} vs {bottom}")
    if top < 20 or left < 20:
        raise SystemExit("ink runs too close to an edge")


def quantise(frames):
    """Map the frames onto one shared palette, exactly.

    Two reasons this is done by hand. A shared palette makes consecutive frames
    differ only where something moved, which takes the file from about 1.2 MB
    to under 150 KB. And Pillow's own palette matching is approximate, which
    quietly coarsens a smooth gradient into visible bands; matching on the
    nearest colour keeps the ramp exactly as it was rendered."""
    import numpy as np

    col = np.asarray(frames[0].convert("RGB")).astype(int)[:, 20, :]
    entries, seen = [], set()
    for c in map(tuple, col):                       # the ramp, in order
        if c not in seen:
            seen.add(c)
            entries.append(c)
    for a in (0.5, 0.62, 0.7, 0.78, 0.85, 0.92):    # the dimmed strokes
        for py in (0, H * 0.35, H * 0.65, H - 1):
            c = dim(py, a)
            if c not in seen:
                seen.add(c)
                entries.append(c)
    if (255, 255, 255) not in seen:
        entries.append((255, 255, 255))
    entries = entries[:256]
    table = [v for c in entries for v in c] + [0, 0, 0] * (256 - len(entries))
    exact = {c: i for i, c in enumerate(entries)}
    arr = np.array(entries, dtype=np.int32)

    out, cache = [], {}
    for fr in frames:
        a = np.asarray(fr.convert("RGB"))
        flat = a.reshape(-1, 3).astype(np.int32)
        keys = (flat[:, 0] << 16) | (flat[:, 1] << 8) | flat[:, 2]
        uniq, inverse = np.unique(keys, return_inverse=True)
        lut = np.empty(len(uniq), dtype=np.uint8)
        for j, k in enumerate(uniq.tolist()):
            c = ((k >> 16) & 255, (k >> 8) & 255, k & 255)
            i = exact.get(c)
            if i is None:
                i = cache.get(c)
                if i is None:
                    i = int(((arr - np.array(c)) ** 2).sum(axis=1).argmin())
                    cache[c] = i
            lut[j] = i
        im = Image.fromarray(lut[inverse].reshape(a.shape[:2]), mode="P")
        im.putpalette(table)
        out.append(im)
    return out


if __name__ == "__main__":
    out = sys.argv[1] if len(sys.argv) > 1 else ASSETS
    os.makedirs(out, exist_ok=True)
    check_glyphs()

    frames = [frame(i) for i in range(FRAMES)]
    check_layout(frames[0])

    path = os.path.join(out, "lean-kernel-sair.gif")
    q = quantise(frames)
    q[0].save(path, save_all=True, append_images=q[1:],
              duration=DURATION, loop=0, optimize=True, disposal=1)
    print(f"  {os.path.basename(path)}: {os.path.getsize(path) // 1024} KB, "
          f"{len(frames)} frames, {W}x{H}")
