#!/usr/bin/env bash
# ==============================================================================
# File: runbench.sh
# Description: Runs each emitted benchmark in its own process under callgrind
#   and leaves the log beside the source, for instrument.py to read.
#
#   One file per process is the judge's own boundary: it counts "only the
#   target declaration's kernel check" in "three separate processes". Each file
#   is measured twice, once as written and once with `debug.skipKernelTC`, and
#   the difference is the kernel check with elaboration and literal parsing
#   removed.
#
#   `--trace-children` is on because `lake env lean` reaches the real binary
#   through two execs; the reader takes the largest count in the log, which is
#   always the `lean` process, since neither `lake` nor the elan shim does any
#   work worth counting.
#
#   The deadline exists because a probe can be slow for the very reason it is
#   being asked about: if a primitive turns out to be unfolded rather than
#   computed by the bignum library, that one file could run for an hour and
#   take the whole table with it. Order is judged sizes first, then probes,
#   then micro-benchmarks, so the figures that matter most are the ones
#   already on disk when the deadline falls.
#
# Usage: bash runbench.sh <dir> <deadline-seconds> <all|judged>
# Author: Amey Thakur
# License: CC BY 4.0
# ==============================================================================

set -u

DIR="${1:-bench}"
DEADLINE="${2:-3300}"
SCOPE="${3:-all}"
START=$SECONDS

run_one() {
  local stem="$1"
  local src="$DIR/$stem.lean"
  local out="$DIR/$stem.out"
  [ -f "$src" ] || return 0
  if [ $((SECONDS - START)) -gt "$DEADLINE" ]; then
    echo "MEASUREFAILED deadline reached before $stem" > "$out"
    return 0
  fi
  local began=$SECONDS
  timeout 1200 valgrind --tool=callgrind --cache-sim=no --branch-sim=no \
      --trace-children=yes --callgrind-out-file=/dev/null \
      lake env lean "$src" > "$out" 2>&1
  local status=$?
  if [ $status -ne 0 ]; then
    echo "MEASUREFAILED exit $status" >> "$out"
  fi
  printf '  %-18s %4d s  %s\n' "$stem" "$((SECONDS - began))" \
    "$(grep -o 'I *refs: *[0-9,]*' "$out" | tail -1)"
}

both() {
  run_one "$1"
  run_one "$1_skip"
}

# The baseline first: every other figure is read against it.
both Base

for i in 0 1 2 3 4 5; do both "J$i"; done

if [ "$SCOPE" = "all" ]; then
  for q in Q_pow Q_shiftl Q_shiftr Q_land Q_lor Q_gcd; do both "$q"; done
  for m in P_list P_list_ctrl P_packed \
           R_nat A_nat A_int M_nat M_int \
           M_int_coeff M_int_mid M_int_big D_int_big \
           L_len24 L_len48 L_len96; do both "$m"; done
fi

echo "  total $((SECONDS - START)) s"
