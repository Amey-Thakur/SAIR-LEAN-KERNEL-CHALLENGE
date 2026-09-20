# Stage 2 — competition submissions

Work for the live [Lean Kernel Challenge](https://competition.sair.foundation/competitions/lean-kernel-challenge)
(Stage 1, deadline **20 November 2026, 23:59 AoE**). The `stage1/` folder at the
repository root is the rehearsal built before the problems were published; this
folder holds entries for the actual problems.

> [!IMPORTANT]
> **Submit [`partition/SubmissionPacked.lean`](partition/SubmissionPacked.lean)**
> for the `partition` problem, renamed to `Submission.lean`.
> The competition selects **the latest entry by submission time, not the best
> one**, so nothing slower should be uploaded after it.

## What is here

| File | What it is |
|---|---|
| `partition/SubmissionPacked.lean` | The entry. A whole row of the table in one `Nat`. |
| `partition/Submission.lean` | An earlier, slower entry kept as a fallback: the same recurrence on lists. |
| `bench.py` | Builds a candidate in the real problem package, checks its axioms, and times the kernel reducing `impl n`. |
| `compare.py` | Prints several runs side by side. |

## The problem

Given `n`, count the partitions of `n`. The locked specification defines

```text
partAux 0 0       = 1
partAux 0 (n + 1) = 0
partAux (k + 1) n = sum over j = 0..floor(n / (k+1)) of partAux k (n - j*(k+1))
partitionSpec n   = partAux n n
```

and an entry must supply `impl` together with a proof that `impl n =
partitionSpec n` **for every `n`**, resting only on `propext`, `Quot.sound` and
`Classical.choice`. Rank is the total hardware instruction count the kernel
spends reducing `impl n` over six hidden cases with `n` between 14 and 36.

Evaluating the specification directly re-derives the same `partAux k m` along
every path that reaches it: about 128,000 calls at `n = 36` for a table with
1,369 distinct entries.

## The two entries

**Lists (`Submission.lean`).** Build row `k` once, as a list whose `m`-th entry
is `partAux k m`, and let row `k+1` read it. Each cell is the specification's
own sum with the recursive call replaced by a lookup, so correctness is a
congruence rather than a re-derivation. Reading position `m` of a list costs
`m` steps, which is what this design pays and the next one avoids.

**One number (`SubmissionPacked.lean`).** Hold the whole row in a single natural
number, with the entry for `m` in the `m`-th field of `w` bits. The row step is
then the specification's sum lifted to that representation,

```text
R' = ( R + (R <<< d*w) + (R <<< 2*d*w) + ... )  mod  2^(w*(n+1))
```

because field `m` of that sum is the sum over `j` with `j*d ≤ m` of field
`m - j*d` of `R`. The kernel does each step as one arithmetic operation on one
large integer, whatever the row's length: 528 operations at `n = 36` against
roughly 32,000 list steps.

Fields never carry into one another because `w` is wide enough to hold any
entry. Peeling one term off the specification's sum gives `partAux (k+1) m =
partAux k m + partAux (k+1) (m-(k+1))`, and `partAux k m ≤ 2^(m+k)` follows by
induction, so `w = 2n+1` is enough. That bound is proved, not assumed; it is the
only thing between this representation and a wrong answer.

Both files are self-contained. The indexing, the packing and every lemma are
defined in the submission rather than imported, so each proof is about the exact
function the kernel reduces.

## Measured

`.github/workflows/stage2.yml` clones the challenge at a pinned commit, builds
each candidate inside the real problem package, checks that the proof closes and
that its axioms are permitted, and times the kernel reducing `impl n`. Every
variant runs in the same job on the same runner.

Totals over the six published group endpoints, in seconds of kernel wall time
with process startup subtracted:

| Entry | 14 | 18 | 22 | 26 | 32 | 36 | total |
|---|---:|---:|---:|---:|---:|---:|---:|
| specification as written | 0.16 | 0.47 | 1.37 | 3.50 | 12.92 | 29.96 | 48.40 |
| lists | 0.13 | 0.18 | 0.31 | 0.47 | 0.83 | 1.13 | 3.05 |
| one number | 0.01 | 0.01 | 0.01 | 0.01 | 0.02 | 0.01 | **0.07** |

At the judged sizes the packed row finishes inside the timer's resolution, so
it is measured again where the work is large enough to see. Those runs are what
the field width was tuned against:

| `n` | 100 | 150 | 200 | 300 |
|---|---:|---:|---:|---:|
| width `n·bits(n+1)+1` | 0.08 | 0.16 | 0.32 | 1.06 |
| width `2n+1` | 0.03 | 0.06 | 0.11 | 0.27 |

> [!WARNING]
> These are **wall times on a virtualised runner, not instruction counts**. The
> judge counts hardware instructions through `perf_event_open`, which a GitHub
> Actions runner does not expose, so only the ordering between designs carries
> over, not the numbers. The upstream local evaluator reports wall time for the
> same reason.

Answers are checked against the specification's recurrence recomputed in Python,
independently of the submission, so a wrong answer cannot be measured as a fast
one. The packed entry is also checked at every `n` from 0 to 13, where the
counts are known by hand.

## Still open

- The sum `R + (R <<< s) + (R <<< 2s) + ...` takes one term at a time. Squaring
  the stride instead would reach the same total in `log` steps rather than
  `n/d`, cutting roughly 2.6x off the operation count at `n = 36`.
- `partAux k m ≤ 2^(m+k)` is loose: at `n = 36` a field is 73 bits wide for
  values that never exceed 17,977. `partAux k m ≤ 2^m · (k+1)` is provable by
  the same induction and would narrow it by about 1.7x.
- The other seven problems have no entry yet.
