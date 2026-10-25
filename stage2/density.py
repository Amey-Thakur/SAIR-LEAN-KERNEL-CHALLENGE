#!/usr/bin/env python3
# ==============================================================================
# File: density.py
# Description: For every problem, how much improvement buys how many places.
#
#   Score and rank are not the same objective. On 19 October a 5.8% gain on
#   polydisc LOST two places, because the field grew and other teams moved; on
#   the same day a 65x gain on ca-rule110 bought three. What decides the trade
#   is the density of the field immediately above us, which the top-three view
#   cannot show. This prints the neighbours.
#
# Usage: py stage2/density.py [--problem p] [--window 10]
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
UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
      "(KHTML, like Gecko) Chrome/128.0 Safari/537.36")
US = "LKC01-T00040"

PROBLEMS = ["fib", "polydisc", "ca-rule110", "sha256", "partition",
            "primecount", "permanent", "mertens"]


def call(path: str):
    key = os.environ.get("SAIR_API_KEY")
    if not key:
        raise SystemExit("SAIR_API_KEY is not set")
    req = urllib.request.Request(
        f"{BASE}{path}",
        headers={"Authorization": f"Bearer {key}", "User-Agent": UA,
                 "Accept": "application/json"})
    with urllib.request.urlopen(req, timeout=120) as r:
        return json.loads(r.read().decode())


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--problem")
    ap.add_argument("--window", type=int, default=10)
    a = ap.parse_args()
    problems = [a.problem] if a.problem else PROBLEMS

    print(f"{'problem':<11} {'ours':>17} {'rank':>7} "
          f"{'x to +1':>8} {'x to +5':>8} {'x to r3':>8}  verdict")
    print("-" * 78)
    plan = []
    for p in problems:
        data = call(f"/competitions/{COMP}/leaderboard?problem={p}")
        rows = data["data"]["problems"][p]["ranked"]
        # teamNumber is a top-level field on the row, not nested under team
        mine = next((r for r in rows if r.get("teamNumber") == US), None)
        if mine is None:
            print(f"{p:<11} (not ranked)")
            continue
        ours = int(mine["computationTotal"])
        rank = mine["rank"]
        above = [int(r["computationTotal"]) for r in rows
                 if r["rank"] < rank]
        above.sort(reverse=True)          # closest competitor first
        r3 = int(next(r for r in rows if r["rank"] == 3)["computationTotal"])

        def need(places: int) -> float:
            if len(above) < places:
                return float("nan")
            return ours / above[places - 1]

        x1, x5, xr3 = need(1), need(5), ours / r3
        # a place is cheap when a small factor buys it
        if x1 <= 1.10:
            v = f"CHEAP: {100*(x1-1):.1f}% buys a place"
        elif x5 <= 2.0:
            v = f"dense: {x5:.2f}x buys five"
        else:
            v = "sparse"
        plan.append((p, x1, x5, xr3, v))
        print(f"{p:<11} {ours:>17,} {rank:>4}/{len(rows):<2} "
              f"{x1:>8.2f} {x5:>8.2f} {xr3:>8.1f}  {v}")

    print()
    print("  Cheapest places first, by the factor needed to gain five:")
    for p, x1, x5, xr3, v in sorted(plan, key=lambda t: (t[2], t[1])):
        print(f"    {p:<11} +1 at {x1:>6.2f}x   +5 at {x5:>6.2f}x   "
              f"rank 3 at {xr3:>7.1f}x")
    return 0


if __name__ == "__main__":
    sys.exit(main())
