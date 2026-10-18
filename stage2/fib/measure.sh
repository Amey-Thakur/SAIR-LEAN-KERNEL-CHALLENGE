#!/usr/bin/env bash
# ==============================================================================
# File: measure.sh
# Description: Measures the `fib` designs at the boundary the judge measures,
#   inside the real problem package, on one runner, in one job.
#
#   What the judge counts, from rules/evaluation.md: "In three separate
#   processes, count only the target declaration's kernel check, which reduces
#   `impl n` and compares it with `v`." Nothing else. Not parsing, not
#   elaboration, not the `rfl` tactic's own reduction.
#
#   So that is what this measures. Lean's own profiler reports a cumulative
#   `type checking` figure, and type checking is `addDecl`, which is the
#   kernel. Wall-clock for the whole process is recorded next to it as a
#   cross-check, but it is not the number: at n = 150000 the expected answer
#   is a 31,348-digit literal, and parsing that literal is 0.28 s while the
#   kernel's entire reduction is 0.003 s. Every figure this repository
#   recorded for `fib` before 18 October 2026 was a measurement of Lean's
#   parser.
#
#   Four things are measured.
#
#   A. Each design, under the profiler, on twelve distinct inputs in each of
#      the three judged groups. Distinct inputs keep the kernel's cache out of
#      it; the three groups separately give the scaling in n.
#   B. The arithmetic floor. `calib` performs exactly the products that the
#      specialised design performs, on literal operands, with no recursion and
#      no unfolding. Its kernel figure is the part of the cost that no
#      rewriting can remove, and the gap above it is the overhead.
#   C. The price of the structural fuel. `fibAux fuel n` needs `fuel` only as
#      large as the number of halvings. Timing `fibAux 24 n` against
#      `fibAux n n` says whether the kernel pays for the size of the fuel,
#      which is the same question as whether the recursion was compiled
#      structurally or to `WellFounded.fix`.
#   D. What Lean actually compiled, printed, because the answer to C is a fact
#      about the compiled definition and it can simply be read.
#
# Usage: bash stage2/fib/measure.sh <repo-root>   # cwd = upstream/problems/fib
# Author: Amey Thakur
# License: CC BY 4.0
# ==============================================================================

set -u

ROOT="$(cd "$1" && pwd)"
PY="${PY:-python}"
COUNT="${COUNT:-12}"
OUT="$ROOT/fib-measure.tsv"
KERN="$ROOT/fib-kernel.tsv"
LOGS="$ROOT/fib-logs"
mkdir -p "$LOGS"
printf 'design\tcase\trep\tseconds\trc\n' > "$OUT"
printf 'design\tcase\tcases\tkernel_ms\tper_case_ms\n' > "$KERN"

DESIGN="none"

emit() { "$PY" "$ROOT/stage2/fib/bulk.py" "$@"; }

# The cumulative `type checking` figure, in milliseconds. The profiler prints
# seconds once a phase passes a second, so both units are handled.
kernel_ms() {   # kernel_ms <logfile>
  grep -E '^[[:space:]]+type checking [0-9]' "$1" | tail -1 | awk '{
    v = $3
    if (v ~ /ms$/) { sub(/ms$/, "", v); printf "%.3f", v + 0 }
    else if (v ~ /s$/) { sub(/s$/, "", v); printf "%.3f", (v + 0) * 1000 }
    else { printf "NA" }
  }'
}

# One timing. /usr/bin/time reports the elapsed seconds and nothing else, so a
# failure still says how long it took to fail and `rc` says it failed.
run() {   # run <case> <file> <reps> <cases-in-file>
  local case=$1 file=$2 reps=$3 ncases=$4 i rc secs km per
  for i in $(seq 1 "$reps"); do
    /usr/bin/time -f "%e" -o "$LOGS/t" \
      lake env lean "$file" > "$LOGS/$DESIGN-$case-$i.log" 2>&1
    rc=$?
    secs="$(cat "$LOGS/t")"
    printf '%s\t%s\t%s\t%s\t%s\n' "$DESIGN" "$case" "$i" "$secs" "$rc" >> "$OUT"
    km="$(kernel_ms "$LOGS/$DESIGN-$case-$i.log")"
    if [ -n "$km" ] && [ "$km" != "NA" ] && [ "$ncases" -gt 0 ]; then
      per="$(awk -v k="$km" -v n="$ncases" 'BEGIN{printf "%.4f", k / n}')"
    else
      per="NA"
    fi
    printf '%s\t%s\t%s\t%s\t%s\n' \
      "$DESIGN" "$case" "$ncases" "$km" "$per" >> "$KERN"
    printf '  %-22s %-10s rep%s  wall=%ss  kernel=%sms  per case=%sms  rc=%s\n' \
      "$DESIGN" "$case" "$i" "$secs" "$km" "$per" "$rc"
  done
}

# Put a design in the package and build it. The starter is restored from the
# upstream checkout, so it is the shipped file and not a copy of it.
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
    grep -E "error" "$LOGS/build-$DESIGN.log" | head -30
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
emit --emit prof  --group f1 --count "$COUNT" > Proff1.lean
emit --emit prof  --group f2 --count "$COUNT" > Proff2.lean
emit --emit prof  --group f3 --count "$COUNT" > Proff3.lean
emit --emit calib --n 150000                  > Calib.lean
emit --emit calibsweep                        > Floor.lean
emit --emit calibsweepraw                     > Floorraw.lean
emit --emit floortiny                         > Floortiny.lean
emit --emit fuel  --fuelmode small --count 4  > Fuelsmall.lean
emit --emit fuel  --fuelmode big   --count 4  > Fuelbig.lean
# The old method, kept so that the two can be compared in one place.
emit --emit decomp --case T0 --n 150000 > T0.lean
emit --emit decomp --case T1 --n 150000 > T1.lean
emit --emit decomp --case T3 --n 150000 > T3.lean
emit --emit decomp --case T4 --n 150000 > T4.lean
wc -c Proff1.lean Proff2.lean Proff3.lean Calib.lean

printf 'import Submission\n#print Submission.impl\n#print Submission.fibAux\n' \
  > Shape.lean

# --------------------------------------------------------------- the designs
for design in starter CandidateRaw; do
  if [ "$design" != "starter" ] && [ ! -f "$ROOT/stage2/fib/$design.lean" ]; then
    echo "=== $design: no such file, skipped ==="
    continue
  fi
  if ! place "$design"; then
    echo "=== $design: not measured ==="
    continue
  fi
  run prof-f1 Proff1.lean 2 "$COUNT"
  run prof-f2 Proff2.lean 2 "$COUNT"
  run prof-f3 Proff3.lean 2 "$COUNT"
  if [ "$design" = "starter" ]; then
    # The floor does not depend on any candidate; one measurement of it is
    # enough, and the starter is the build that is certain to exist.
    run calib    Calib.lean    2 49
    run floor    Floor.lean    2 0
    run floorraw  Floorraw.lean  2 0
    run floortiny Floortiny.lean 2 0
    run T0 T0.lean 2 0
    run T1 T1.lean 2 0
    run T3 T3.lean 2 0
    run T4 T4.lean 2 0
    echo "  --- the floor, per declaration, notation then raw ---"
    grep -E "type checking took" "$LOGS/$DESIGN-floor-1.log" || true
    echo "  ---"
    grep -E "type checking took" "$LOGS/$DESIGN-floorraw-1.log" || true
    echo "  --- the floor with a small statement, per declaration ---"
    grep -E "type checking took" "$LOGS/$DESIGN-floortiny-1.log" || true
  else
    run fuel-small Fuelsmall.lean 2 4
    run fuel-big   Fuelbig.lean   2 4
    echo "  --- what Lean compiled ---"
    lake env lean Shape.lean > "$LOGS/shape-$DESIGN.log" 2>&1
    head -40 "$LOGS/shape-$DESIGN.log"
    # The cheap right-hand side forces the whole reduction but only checks the
    # answer modulo 2^64 - 59. Once per design, check the real literal at every
    # judged size and at the small values whose answers are known by hand. This
    # is the slow harness, and here that does not matter: the question is
    # whether every case reduces to exactly the right number, not what it costs.
    echo "  --- full-literal check, all 13 cases ---"
    "$PY" "$ROOT/stage2/timecases.py" \
      --cases "$ROOT/stage2/fib/cases.json" \
      --label "$DESIGN" --out "$ROOT/fib-cases-$DESIGN.json" --timeout 300
  fi
  echo "  --- per declaration at the hardest group ---"
  grep -E "type checking took" "$LOGS/$DESIGN-prof-f3-1.log" || true
done

# The package is left holding the starter, so nothing a later step builds is
# whichever design this script happened to stop on.
git -C "$ROOT/upstream" checkout -- problems/fib/Submission.lean || true

echo "=== kernel table (the judged boundary) ==="
cat "$KERN"
echo "=== wall-clock table ==="
cat "$OUT"

# The minimum of the repetitions is the right statistic for a timing: noise
# only ever adds.
echo "=== kernel minima, per case ==="
awk -F'\t' '
NR > 1 && $4 != "NA" {
  k = $1 SUBSEP $2
  if (!(k in m) || $5 + 0 < m[k]) { m[k] = $5 + 0; tot[k] = $4 + 0 }
}
END {
  for (k in m) {
    split(k, a, SUBSEP)
    printf "%-22s %-12s %9.4f ms per case  (%8.2f ms total)\n",
      a[1], a[2], m[k], tot[k]
  }
}' "$KERN" | sort
