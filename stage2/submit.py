#!/usr/bin/env python3
# ==============================================================================
# File: submit.py
# Description: Sends one Submission.lean to the Lean Kernel Challenge as a
#   formal entry, in the published JSON contract. Dry run is the default.
#
#   Three things this guards against. The contract version is read immediately
#   before the POST and passed through unchanged, because a stale one is
#   rejected. The idempotency key is derived from the submission text itself, so
#   a retry after a lost response returns the stored submission instead of
#   creating a second one. And the local interface checks run first, because the
#   latest entry per problem is the one evaluated, not the best.
#
#   The key is read from SAIR_API_KEY and never printed.
#
# Usage: py stage2/submit.py --problem partition
#          --file stage2/partition/SubmissionPacked.lean
#          --note stage2/partition/submission-note.md [--live]
# Author: Amey Thakur
# License: CC BY 4.0
# ==============================================================================

from __future__ import annotations

import argparse
import hashlib
import json
import os
import pathlib
import sys
import urllib.error
import urllib.request

BASE = "https://api.sair.foundation/api/public/v1"
COMP = "lean-kernel-challenge"
# Cloudflare answers error 1010 to a request with no browser user agent, before
# the API sees it, which looks exactly like a revoked key.
UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/128.0 Safari/537.36")


def call(method, path, body=None):
    key = os.environ.get("SAIR_API_KEY")
    if not key:
        raise SystemExit("SAIR_API_KEY is not set")
    data = None if body is None else json.dumps(body).encode("utf-8")
    headers = {"Authorization": f"Bearer {key}", "Accept": "application/json",
               "Content-Type": "application/json", "User-Agent": UA}
    req = urllib.request.Request(BASE + path, data=data, method=method,
                                headers=headers)
    try:
        with urllib.request.urlopen(req, timeout=180) as r:
            raw = r.read()
            return r.status, (json.loads(raw) if raw else {})
    except urllib.error.HTTPError as e:
        raw = e.read().decode("utf-8", "replace")
        try:
            return e.code, json.loads(raw)
        except ValueError:
            return e.code, {"raw": raw[:500]}


def read_note(path: pathlib.Path) -> str:
    """The note is the first fenced block of the note document."""
    if not path or not path.exists():
        return ""
    parts = path.read_text(encoding="utf-8").split("```")
    return parts[1].strip() if len(parts) > 2 else ""


def local_checks(text: str, limits: dict, shape: dict) -> list[str]:
    """What the judge will check, checked here first."""
    bad = []
    size = len(text.encode("utf-8"))
    if size > limits.get("maxUploadBytes", 1 << 20):
        bad.append(f"{size} bytes exceeds the {limits['maxUploadBytes']} limit")
    if not text.strip():
        bad.append("the source is empty")
    if f"def {shape.get('functionName', 'impl')} " not in text:
        bad.append(f"no definition of {shape.get('functionName')}")
    if f"theorem {shape.get('proofName', 'impl_correct')} " not in text:
        bad.append(f"no theorem named {shape.get('proofName')}")
    if "namespace Submission" not in text:
        bad.append("declarations are not inside namespace Submission")
    for banned in ("sorry", "native_decide", "partial def", "unsafe "):
        if banned in text:
            bad.append(f"contains {banned!r}")
    return bad


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--problem", required=True)
    ap.add_argument("--file", required=True)
    ap.add_argument("--note", default=None)
    ap.add_argument("--live", action="store_true")
    args = ap.parse_args()

    text = pathlib.Path(args.file).read_text(encoding="utf-8")
    note = read_note(pathlib.Path(args.note)) if args.note else ""
    if len(note) > 5000:
        print(f"  note is {len(note)} code points, over the 5000 limit")
        return 1

    code, spec = call("GET", f"/competitions/{COMP}/submission-spec")
    if code != 200:
        print(f"  cannot read the submission spec [{code}]: {spec}")
        return 1
    spec = spec["data"]
    contract = spec["contractVersion"]

    code, part = call("GET", f"/competitions/{COMP}/me")
    if code != 200:
        print(f"  cannot read participation [{code}]: {part}")
        return 1
    part = part["data"]
    if not part.get("enrolled") or not part.get("canSubmit"):
        print(f"  cannot submit: enrolled={part.get('enrolled')} "
              f"reason={part.get('submitBlockedReason')}")
        return 1

    available = {p["problemId"] for p in
                 call("GET", f"/competitions/{COMP}/problems")[1]["data"]["items"]
                 if p.get("availability") == "available"}
    if args.problem not in available:
        print(f"  {args.problem} is not an available problem: {sorted(available)}")
        return 1

    bad = local_checks(text, spec["limits"], spec["requiredSubmissionShape"])
    if bad:
        print("  the source does not meet the required shape:")
        for b in bad:
            print(f"    {b}")
        return 1

    digest = hashlib.sha256(text.encode("utf-8")).hexdigest()
    # Derived from the content, so a retry after a lost response returns the
    # stored submission rather than creating a second one.
    idem = f"lkc-{args.problem}-{digest[:24]}"

    team = part.get("team") or {}
    print(f"  problem      {args.problem}")
    print(f"  entrant      {team.get('teamNumber') or part.get('entrant', {}).get('id')}")
    print(f"  source       {args.file}")
    print(f"  bytes        {len(text.encode('utf-8'))} of {spec['limits']['maxUploadBytes']}")
    print(f"  sha256       {digest}")
    print(f"  note         {len(note)} code points")
    print(f"  contract     {contract}")
    print(f"  idempotency  {idem}")

    if not args.live:
        print("\n  dry run: nothing was sent. Pass --live to submit.")
        return 0

    body = {"idempotencyKey": idem,
            "contractVersionAcknowledged": contract,
            "payload": {"problem": args.problem, "text": text}}
    # The published contract documents the note as `meta.description`, but the
    # deployed endpoint rejects any `meta` object with MALFORMED_BODY and takes
    # the note as a top-level field instead. Probed with a deliberately stale
    # contract version, so no candidate was created while establishing this.
    if note:
        body["note"] = note

    code, resp = call("POST", f"/competitions/{COMP}/submissions", body)
    print(f"\n  POST -> {code}")
    print("  " + json.dumps(resp, ensure_ascii=False)[:1200])
    if code in (200, 201):
        d = resp.get("data", {})
        print(f"\n  submissionId {d.get('submissionId')}  status {d.get('status')}")
        print("  201 is a new entry; 200 means this exact request was already stored.")
        return 0
    return 1


if __name__ == "__main__":
    sys.exit(main())
