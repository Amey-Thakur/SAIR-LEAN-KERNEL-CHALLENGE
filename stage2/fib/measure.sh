#!/usr/bin/env bash
# ==============================================================================
# File: measure.sh
# Description: Measures the `fib` designs in a way that can see the
#   computation, inside the real problem package, on one runner, in one job.
#
#   Two measurements, because the first one answers whether the second is
#   needed.
#
#   A. Decomposition. The existing harness times `impl n = <expected literal>`,
#      and at n = 150000 that literal is 31,348 decimal digits. Five files
#      separate what that figure is made of: the import alone, the literal
#      alone in decimal, the literal alone in hex, the computation against a
#      right-hand side that costs nothing to read, and the two together, which
#      is what the harness does. If the literal is most of it, every number
#      this repository has recorded for `fib` is a measurement of Lean's
#      parser.
#
#   B. Bulk. Sixteen distinct inputs per judged group in one process, with the
#      cheap right-hand side, for each design in turn. Start-up is paid once
#      instead of sixteen times, distinct inputs keep the kernel's cache out of
#      it, and the three groups separately give the slope in n rather than one
#      number.
#
#   Lean's own profiler runs over the hardest group as well, because it
#   separates elaboration from `type checking`, and type checking is the
#   kernel's `addDecl` -- the only thing the judge counts.
#
# Usage: bash stage2/fib/measure.sh <repo-root>   # cwd = upstream/problems/fib
# Author: Amey Thakur
# License: CC BY 4.0
# ==============================================================================

set -u

ROOT="$(cd "$1" && pwd)"
PY="${PY:-python}"
OUT="$ROOT/fib-measure.tsv"
LOGS="$ROOT/fib-logs"
mkdir -p "$LOGS"
printf 'design\tcase\trep\tseconds\trc\n' > "$OUT"

DESIGN="none"

emit() { "$PY" "$ROOT/stage2/fib/bulk.py" "$@"; }

# One timing. /usr/bin/time writes the elapsed seconds and nothing else, so a
# failure still reports how long it took to fail, and `rc` says it failed.
run() {   # run <case> <file> <reps>
  local case=$1 file=$2 reps=$3 i rc secs
  for i in $(seq 1 "$reps"); do
    /usr/bin/time -f "%e" -o "$LOGS/t" \
      lake env lean "$file" > "$LOGS/$DESIGN-$case-$i.log" 2>&1
    rc=$?
    secs="$(cat "$LOGS/t")"
    printf '%s\t%s\t%s\t%s\t%s\n' "$DESIGN" "$case" "$i" "$secs" "$rc" >> "$OUT"
    printf '  %-10s %-10s rep%s  %8ss  rc=%s\n' \
      "$DESIGN" "$case" "$i" "$secs" "$rc"
  done
}

# Put a design in the package and build it. The starter is restored from the
# upstream checkout so that it is the shipped file and not a copy of it.
place() {   # place <design>
  DESIGN="$1"
  echo "=== $DESIGN ==="
  if [ "$DESIGN" = "starter" ]; then
    git -C "$ROOT/upstream" checkout -- problems/fib/Submission.lean || return 1
  else
    cp "$ROOT/stage2/fib/$DESIGN.lean" Submission.lean || return 1
  fi
  if ! lake build > "$LOGS/build-$DESIGN.log" 2>&1; then
    echo "  BUILD FAILED; see build-$DESIGN.log"
    grep -E "error" "$LOGS/build-$DESIGN.log" | head -20
    return 1
  fi
  printf 'import Submission\n#print axioms Submission.impl_correct\n' \
    > Axioms.lean
  lake env lean Axioms.lean > "$LOGS/axioms-$DESIGN.log" 2>&1
  echo "  axioms: $(cat "$LOGS/axioms-$DESIGN.log")"
  if grep -qiE "sorryAx|native|unknown|error" "$LOGS/axioms-$DESIGN.log"; then
    echo "  FORBIDDEN OR MISSING AXIOM LINE"
    return 1
  fi
  return 0
}

# ------------------------------------------------------------------ the files
emit --emit bulk --count 16 --groups f1 > Bulkf1.lean
emit --emit bulk --count 16 --groups f2 > Bulkf2.lean
emit --emit bulk --count 16 --groups f3 > Bulkf3.lean
emit --emit prof --n 150000            > Prof.lean
emit --emit decomp --case T0 --n 150000 > T0.lean
emit --emit decomp --case T1 --n 150000 > T1.lean
emit --emit decomp --case T2 --n 150000 > T2.lean
emit --emit decomp --case T3 --n 150000 > T3.lean
emit --emit decomp --case T4 --n 150000 > T4.lean
emit --emit decomp --case T5 --n 150000 > T5.lean
wc -c Bulkf1.lean Bulkf2.lean Bulkf3.lean T1.lean T3.lean T4.lean

# --------------------------------------------------------------- the designs
# starter first, because it is the live entry and the number to beat.
for design in starter SubmissionFastDouble Candidate; do
  if [ "$design" != "starter" ] && [ ! -f "$ROOT/stage2/fib/$design.lean" ]; then
    echo "=== $design: no such file, skipped ==="
    continue
  fi
  if ! place "$design"; then
    echo "=== $design: not measured ==="
    continue
  fi
  run T0 T0.lean 2          # start-up, which every other figure contains
  run bulk-f1 Bulkf1.lean 2
  run bulk-f2 Bulkf2.lean 2
  run bulk-f3 Bulkf3.lean 2
  run prof Prof.lean 1
  echo "  --- profiler lines ---"
  grep -E "took" "$LOGS/$DESIGN-prof-1.log" | head -40 || true
  # The decomposition only has to be done for two designs to settle the
  # question it asks, and T4 is the expensive one.
  if [ "$design" != "SubmissionFastDouble" ]; then
    run T1 T1.lean 2
    run T2 T2.lean 2
    run T3 T3.lean 2
    run T4 T4.lean 2
    run T5 T5.lean 2
  fi
done

# The package is left holding the starter, so nothing a later step builds is
# a design this script happened to stop on.
git -C "$ROOT/upstream" checkout -- problems/fib/Submission.lean || true

echo "=== table ==="
cat "$OUT"

# The minimum of the repetitions is the right statistic for a timing: noise
# only ever adds. T0 is the start-up every other figure contains, so the last
# column is the work.
echo "=== minima, and the work with start-up removed ==="
awk -F'\t' '
NR > 1 && $5 == 0 {
  k = $1 SUBSEP $2
  if (!(k in m) || $4 + 0 < m[k]) m[k] = $4 + 0
}
END {
  for (k in m) {
    split(k, a, SUBSEP)
    base = ((a[1] SUBSEP "T0") in m) ? m[a[1] SUBSEP "T0"] : 0
    printf "%-22s %-10s %8.2f %8.2f\n", a[1], a[2], m[k], m[k] - base
  }
}' "$OUT" | sort
