#!/usr/bin/env python3
# ==============================================================================
# File: watch_score.py
# Description: Waits for this team's ranked row on a problem to change, and
#   prints what changed. Exits as soon as it does, so it produces one
#   notification rather than a stream.
#
#   Why it exists. There is no per-submission read on this API: GET on
#   /competitions/<comp>/submissions answers 405 and /submissions/<id> answers
#   404, so a submission's score is observable only when it reaches the
#   leaderboard and replaces the team's ranked row. Polling that row is the only
#   way to find out what a submission scored.
#
#   What it is waiting for here. Submission 713 is the list design for
#   `partition`: every value a single partition count, no packing. The packed
#   entry on the board is at 132,036,341. Elapsed time says the list design is 52
#   times SLOWER (3.63 s against 0.07 s over the six judged sizes); a cost model
#   that charges by operand size says it should score BETTER, near 95,000,000,
#   because nothing in it is ever 43 machine words wide. Those two predictions
#   cannot both hold, and 713's figure decides between them. See
#   stage2/partition/MODELS.md for the models and the calibration.
#
#   Either answer is worth having. Near 95M confirms that the ranked metric
#   charges by operand size, and the next design has to make the numbers small.
#   Above 132M refutes that, leaves elapsed time as the better guide, and means
#   the 92x gap is somewhere neither instrument has looked yet.
#
#   The key is read from the environment and never printed.
#
# Usage: py stage2/watch_score.py --problem partition --team LKC01-T00040
#          [--known-submission 649] [--interval 300] [--max-polls 96]
# Author: Amey Thakur
# License: CC BY 4.0
# ==============================================================================

from __future__ import annotations

import argparse
import json
import os
import sys
import time
import urllib.error
import urllib.request

BASE = "https://api.sair.foundation/api/public/v1"
COMP = "lean-kernel-challenge"
# Cloudflare answers error 1010 to a request with no browser user agent, before
# the API sees it, which looks exactly like a revoked key.
UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/128.0 Safari/537.36")


def call(path: str, key: str):
    req = urllib.request.Request(BASE + path, method="GET", headers={
        "Authorization": f"Bearer {key}", "Accept": "application/json",
        "User-Agent": UA})
    with urllib.request.urlopen(req, timeout=120) as r:
        return json.loads(r.read() or b"{}")


def our_row(problem: str, team: str, key: str):
    d = call(f"/competitions/{COMP}/leaderboard?problem={problem}", key)
    ranked = d["data"]["problems"][problem]["ranked"]
    for r in ranked:
        if r.get("teamNumber") == team:
            return r, len(ranked)
    return None, len(ranked)


def describe(r: dict, total: int) -> str:
    return (f"rank {r['rank']}/{total}  submission {r['submissionId']}  "
            f"computationTotal {int(r['computationTotal']):,}  "
            f"correctnessWork {int(r['correctnessWork']):,}  "
            f"coverage {r['coverage']['completed']}/{r['coverage']['planned']}")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--problem", default="partition")
    ap.add_argument("--team", required=True)
    ap.add_argument("--known-submission", default=None,
                    help="the submission id currently on the board; the wait "
                         "ends when the row no longer shows it")
    ap.add_argument("--interval", type=float, default=300.0,
                    help="seconds between polls; this is a remote API, so it is "
                         "deliberately not tight")
    ap.add_argument("--max-polls", type=int, default=96)
    args = ap.parse_args()

    key = os.environ.get("SAIR_API_KEY")
    if not key:
        print("SAIR_API_KEY is not set")
        return 1

    baseline_row, total = our_row(args.problem, args.team, key)
    if baseline_row is None:
        print(f"no row for {args.team} on {args.problem} yet")
        baseline_id = args.known_submission
        baseline_total = None
    else:
        baseline_id = args.known_submission or str(baseline_row["submissionId"])
        baseline_total = int(baseline_row["computationTotal"])
        print(f"waiting: {describe(baseline_row, total)}")
    sys.stdout.flush()

    for poll in range(args.max_polls):
        time.sleep(args.interval)
        try:
            row, total = our_row(args.problem, args.team, key)
        except (urllib.error.HTTPError, urllib.error.URLError, KeyError,
                TimeoutError) as exc:
            # One failed request must not end the wait. Transient 5xx and
            # Cloudflare hiccups are expected over a multi-hour poll.
            print(f"poll {poll + 1}: transient {type(exc).__name__}, retrying")
            sys.stdout.flush()
            continue
        if row is None:
            continue
        changed = (str(row["submissionId"]) != str(baseline_id)
                   or (baseline_total is not None
                       and int(row["computationTotal"]) != baseline_total))
        if changed:
            print(f"SCORED: {describe(row, total)}")
            if baseline_total:
                new = int(row["computationTotal"])
                d = new / baseline_total
                print(f"  was {baseline_total:,}, now {new:,}  ({d:.2f}x)")
                # The two predictions this was waiting to decide between.
                print(f"  operand-size model predicted about 95,000,000")
                print(f"  elapsed time predicted worse than 132,036,341")
                if new < 120_000_000:
                    print("  -> operand size IS charged; make the numbers small")
                else:
                    print("  -> operand size is NOT the explanation; the gap is "
                          "elsewhere")
            sys.stdout.flush()
            return 0
    print(f"no change after {args.max_polls} polls "
          f"({args.max_polls * args.interval / 3600:.1f} h)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
