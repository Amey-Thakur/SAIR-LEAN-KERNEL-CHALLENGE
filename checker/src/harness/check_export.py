# ==============================================================================
# File: check_export.py
# Description: The arena contract. Read an export, check every declaration in
#   it, and leave with exactly one of three exit codes. The mapping is the
#   whole point of the file: 0 only when the environment actually type checked,
#   1 when something in it did not, and 2 when this checker met something it
#   does not implement. There is no path that reaches 0 by doing nothing.
# Usage: python -m src.harness.check_export [export.ndjson]
#        IN=export.ndjson python -m src.harness.check_export
# Tech Stack: Python 3.10+, standard library only
# ==============================================================================

from __future__ import annotations

import os
import sys
import time

from ..export_format.reader import (MalformedExport, UnsupportedExport,
                                    read_export)
from ..kernel.typechecker import Declined, Rejected, TypeChecker

ACCEPTED, REJECTED, DECLINED, ERROR = 0, 1, 2, 3


def check_stream(lines, fuel: int = 2_000_000, verbose: bool = False):
    """Return (exit_code, message). Never raises for an input problem."""
    try:
        env = read_export(lines)
    except UnsupportedExport as exc:
        return DECLINED, f"declined: {exc}"
    except MalformedExport as exc:
        return REJECTED, f"rejected: {exc}"

    checker = TypeChecker(env, fuel=fuel)
    checked = 0
    for decl in env:
        try:
            checker.check_declaration(decl)
            checked += 1
        except Rejected as exc:
            return REJECTED, f"rejected: {decl.name}: {exc}"
        except Declined as exc:
            return DECLINED, f"declined: {decl.name}: {exc}"
        except RecursionError:
            return DECLINED, f"declined: {decl.name}: recursion limit"
        if verbose and checked % 500 == 0:
            print(f"  {checked} declarations", file=sys.stderr, flush=True)
    return ACCEPTED, f"accepted: {checked} declarations"


def main(argv=None) -> int:
    argv = list(sys.argv[1:] if argv is None else argv)
    verbose = "-v" in argv
    argv = [a for a in argv if a != "-v"]
    path = argv[0] if argv else os.environ.get("IN")

    started = time.perf_counter()
    try:
        if path:
            with open(path, "r", encoding="utf-8") as fh:
                code, msg = check_stream(fh, verbose=verbose)
        else:
            code, msg = check_stream(sys.stdin, verbose=verbose)
    except OSError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return ERROR

    elapsed = time.perf_counter() - started
    print(f"{msg} in {elapsed:.3f}s", file=sys.stderr)
    return code


if __name__ == "__main__":
    sys.setrecursionlimit(100_000)
    raise SystemExit(main())
