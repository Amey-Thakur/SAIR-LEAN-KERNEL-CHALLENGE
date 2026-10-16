#!/usr/bin/env python3
# ==============================================================================
# File: whatsliv.py
# Description: For every problem, what the judge is currently ranking and
#   whether it is the file in this repository.
#
#   The latest entry per problem is the one evaluated, not the best, and a
#   resubmission of unchanged text returns the stored submission rather than
#   creating a new one. Both of those make "did my improvement actually go
#   in" a question the board cannot answer on its own: it prints a submission
#   id, not a digest. This compares the digest of each local Submission file
#   against the submission the API holds, so a local improvement that was
#   never sent shows up as a mismatch instead of being assumed live.
#
#   Sends nothing. The key is read from the environment and never printed.
#
# Usage: py stage2/whatsliv.py
# Author: Amey Thakur
# License: CC BY 4.0
# ==============================================================================

from __future__ import annotations

import hashlib
import json
import os
import pathlib
import sys
import urllib.error
import urllib.request

BASE = "https://api.sair.foundation/api/public/v1"
COMP = "lean-kernel-challenge"
UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/128.0 Safari/537.36")

HERE = pathlib.Path(__file__).resolve().parent
PROBLEMS = ["ca-rule110", "fib", "mertens", "partition",
            "permanent", "polydisc", "primecount", "sha256"]

sys.stdout.reconfigure(encoding="utf-8", errors="replace")


def call(method, path, body=None):
    key = os.environ.get("SAIR_API_KEY")
    if not key:
        raise SystemExit("SAIR_API_KEY is not set")
    data = None if body is None else json.dumps(body).encode("utf-8")
    req = urllib.request.Request(
        BASE + path, data=data, method=method,
        headers={"Authorization": f"Bearer {key}", "Accept": "application/json",
                 "Content-Type": "application/json", "User-Agent": UA})
    try:
        with urllib.request.urlopen(req, timeout=90) as r:
            return r.status, json.loads(r.read().decode("utf-8"))
    except urllib.error.HTTPError as e:
        raw = e.read().decode("utf-8", "replace")
        try:
            return e.code, json.loads(raw)
        except json.JSONDecodeError:
            return e.code, {"raw": raw[:300]}


def mine():
    """Every submission this entrant has made, newest first per problem."""
    out, cursor = [], None
    while True:
        q = f"/competitions/{COMP}/submissions?limit=100"
        if cursor:
            q += f"&cursor={cursor}"
        code, body = call("GET", q)
        if code != 200:
            print(f"  cannot list submissions [{code}]: "
                  f"{json.dumps(body)[:200]}")
            return out
        d = body["data"]
        out.extend(d.get("items", []))
        cursor = d.get("nextCursor")
        if not cursor:
            return out


def local_files(problem):
    """Every Submission*.lean in the problem directory, with its digest."""
    found = {}
    for p in sorted((HERE / problem).glob("Submission*.lean")):
        text = p.read_text(encoding="utf-8")
        found[p.name] = hashlib.sha256(text.encode("utf-8")).hexdigest()
    return found


def main():
    subs = mine()
    by_problem = {}
    for s in subs:
        pid = s.get("problem") or s.get("problemId")
        by_problem.setdefault(pid, []).append(s)
    print(f"  {len(subs)} submissions on this entrant\n")

    for problem in PROBLEMS:
        files = local_files(problem)
        hist = by_problem.get(problem, [])
        latest = hist[0] if hist else None
        print(f"  {problem}")
        if latest:
            keys = {k: latest[k] for k in
                    ("submissionId", "status", "createdAt", "idempotencyKey")
                    if k in latest}
            print(f"      latest: {keys}")
        else:
            print("      latest: none found in the listing")
        live_digest = None
        if latest and latest.get("idempotencyKey"):
            live_digest = latest["idempotencyKey"].rsplit("-", 1)[-1]
        for name, digest in files.items():
            mark = ""
            if live_digest:
                mark = ("  <= this is what the judge has"
                        if digest.startswith(live_digest) else "")
            print(f"      {name:28} {digest[:24]}{mark}")
        if live_digest and not any(
                d.startswith(live_digest) for d in files.values()):
            print(f"      live digest {live_digest} matches NO local file")
        print()
    return 0


if __name__ == "__main__":
    sys.exit(main())
