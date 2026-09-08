# ==============================================================================
# File: audit.py
# Description: Audit a Stage 1 submission before it is submitted. Two things
#   disqualify an artifact no matter how fast it is: an unproved goal, and a
#   goal discharged outside the kernel. The first is `sorry`. The second is
#   `native_decide`, which evaluates with the compiler and leaves
#   `Lean.ofReduceBool` in the axiom list, so a scoring rule based on the work
#   a kernel performs is not measuring the submission at all.
#
#   The source checks run anywhere. The axiom check needs Lean, so it reads the
#   output of `#print axioms` when a build has produced some.
# Usage: python tools/audit.py stage1
#        lake build 2>&1 | python tools/audit.py stage1 --axioms -
# Tech Stack: Python 3.10+, standard library only
# ==============================================================================

from __future__ import annotations

import argparse
import pathlib
import re
import sys

OK, FAILED = 0, 1

# Lean's own axioms. Anything else in a submission's axiom list is a claim the
# kernel did not check.
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

BANNED = {
    "sorry": "an unproved goal",
    "native_decide": "a goal discharged outside the kernel",
    "nativeDecide": "a goal discharged outside the kernel",
}

# `sorry` inside a comment or a string is not a proof, so those are stripped
# before looking. This is deliberately crude: it over-reports rather than
# under-reports, because a false alarm costs a minute and a miss costs the run.
BLOCK_COMMENT = re.compile(r"/-.*?-/", re.S)
LINE_COMMENT = re.compile(r"--[^\n]*")
STRING = re.compile(r'"(?:[^"\\]|\\.)*"')


def strip_noncode(text: str) -> str:
    text = BLOCK_COMMENT.sub(lambda m: "\n" * m.group(0).count("\n"), text)
    text = LINE_COMMENT.sub("", text)
    return STRING.sub('""', text)


def scan_sources(root: pathlib.Path):
    """Every banned token in the Lean sources, with the line it is on."""
    findings = []
    for path in sorted(root.rglob("*.lean")):
        if ".lake" in path.parts:
            continue
        code = strip_noncode(path.read_text(encoding="utf-8"))
        for lineno, line in enumerate(code.splitlines(), 1):
            for token, why in BANNED.items():
                if re.search(rf"\b{re.escape(token)}\b", line):
                    findings.append((path, lineno, token, why))
    return findings


def scan_axioms(text: str):
    """Axioms reported by `#print axioms`, and which of them are not allowed.

    Lean prints one line per query, in the form

        'Stage1.impl_eq_spec' depends on axioms: [propext, Quot.sound]
    """
    reported, offending = [], []
    for m in re.finditer(r"depends on axioms:\s*\[([^\]]*)\]", text):
        names = [n.strip() for n in m.group(1).split(",") if n.strip()]
        reported.append(names)
        offending += [n for n in names if n not in ALLOWED_AXIOMS]
    return reported, sorted(set(offending))


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("root", nargs="?", default="stage1",
                    help="the directory holding the Lean sources")
    ap.add_argument("--axioms", metavar="FILE",
                    help="build output to read `#print axioms` from, or - for stdin")
    args = ap.parse_args(argv)

    root = pathlib.Path(args.root)
    if not root.exists():
        print(f"audit: {root} does not exist", file=sys.stderr)
        return FAILED

    failed = False

    findings = scan_sources(root)
    if findings:
        failed = True
        for path, lineno, token, why in findings:
            print(f"  BAD  {path}:{lineno}: {token}, {why}")
    else:
        count = sum(1 for _ in root.rglob("*.lean"))
        print(f"  ok   no sorry and no native_decide in {count} Lean files")

    if args.axioms:
        text = (sys.stdin.read() if args.axioms == "-"
                else pathlib.Path(args.axioms).read_text(encoding="utf-8"))
        reported, offending = scan_axioms(text)
        if not reported:
            print("  BAD  no `#print axioms` output found, so nothing was audited")
            failed = True
        elif offending:
            print(f"  BAD  axioms outside Lean's own: {', '.join(offending)}")
            failed = True
        else:
            for names in reported:
                print(f"  ok   axioms: {', '.join(names) or 'none'}")

    print("audit failed" if failed else "audit passed", file=sys.stderr)
    return FAILED if failed else OK


if __name__ == "__main__":
    raise SystemExit(main())
