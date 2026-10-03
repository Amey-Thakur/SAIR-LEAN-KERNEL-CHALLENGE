#!/usr/bin/env python3
# ==============================================================================
# File: board.py
# Description: Prints the current leaderboard standing for one problem and
#   exits. No waiting, no sleeping.
#
#   Why this exists separately from watch_score.py. That script's job is to wait
#   for the next daily publish, so it sleeps until 08:00 UTC before it polls, and
#   it does that even when asked for zero polls. Twice now it has been reached
#   for when the question was simply "where do we stand", and twice it has sat
#   there for hours answering nothing. The two jobs wanted two scripts.
#
#   The key is read from the environment and never printed.
#
# Usage: py stage2/board.py [--problem partition] [--team LKC01-T00040]
# Author: Amey Thakur
# License: CC BY 4.0
# ==============================================================================

from __future__ import annotations

import argparse
import json
import os
import sys
import urllib.request

BASE = "https://api.sair.foundation/api/public/v1"
COMP = "lean-kernel-challenge"
# Cloudflare answers error 1010 to a request with no browser user agent, before
# the API sees it, which looks exactly like a revoked key.
UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/128.0 Safari/537.36")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--problem", default="partition")
    ap.add_argument("--team", default="LKC01-T00040")
    ap.add_argument("--top", type=int, default=3)
    args = ap.parse_args()

    key = os.environ.get("SAIR_API_KEY")
    if not key:
        print("SAIR_API_KEY is not set")
        return 1

    req = urllib.request.Request(
        f"{BASE}/competitions/{COMP}/leaderboard?problem={args.problem}",
        method="GET",
        headers={"Authorization": f"Bearer {key}", "Accept": "application/json",
                 "User-Agent": UA})
    with urllib.request.urlopen(req, timeout=120) as r:
        data = json.loads(r.read() or b"{}")

    meta = data["data"].get("meta", {})
    rows = data["data"]["problems"][args.problem]["ranked"]
    print(f"  {args.problem}: published {meta.get('publishedAt')} "
          f"batch {meta.get('batchId')}")
    print(f"  publishes daily at {meta.get('configuredUpdateTimeUtc')} UTC, "
          f"cutoff {meta.get('dataCutoffAt')}")
    print()
    for r_ in rows[:args.top]:
        print(f"  rank {r_['rank']:>2}  {int(r_['computationTotal']):>15,}  "
              f"{str(r_.get('teamName'))[:24]}")
    if len(rows) > args.top:
        print("  ...")
    ours = [r_ for r_ in rows if r_.get("teamNumber") == args.team]
    if not ours:
        print(f"  no row for {args.team}")
        return 0
    o = ours[0]
    print(f"  rank {o['rank']:>2}/{len(rows)}  "
          f"{int(o['computationTotal']):>15,}  submission {o['submissionId']}"
          f"   <= ours")
    print()
    print(f"  correctnessWork {int(o['correctnessWork']):,} (not ranked)   "
          f"coverage {o['coverage']['completed']}/{o['coverage']['planned']}")
    lead = int(rows[0]["computationTotal"])
    print(f"  {int(o['computationTotal']) / lead:.1f}x the leader")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
