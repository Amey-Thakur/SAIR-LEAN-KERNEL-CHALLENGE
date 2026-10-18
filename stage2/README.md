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

## What is live, on all eight problems

Verified against the board published 17 October 2026. The `polydisc` row carries submission 1610, sent that day; its score publishes at the next 08:00 UTC run. Every problem carries
this repository's best entry; nothing prepared here is unsent.

| Problem | Live entry | Submission | Rank | Instructions | x to rank 3 |
|---|---|---:|---:|---:|---:|
| `polydisc` | `polydisc/Submission.lean` | **1610** | 33/33 | 10,321,620,511 | **9.2** |
| `fib` | starter, unmodified | 687 | 47/47 | 96,286,901 | **13.4** |
| `sha256` | `sha256/Submission.lean` | 700 | 30/35 | 151,049,224,266 | **15.0** |
| `partition` | `partition/SubmissionPacked.lean` | 1103 | 28/43 | 131,414,027 | 90.7 |
| `ca-rule110` | `ca-rule110/Submission.lean` | 694 | 34/39 | 2,155,396,166 | 652 |
<!-- resubmitted 17 Oct 2026 as 1613, lane-packed initial row; awaiting the 08:00 UTC publish -->
| `primecount` | `primecount/Submission.lean` | 697 | 34/34 | 6,614,390,870 | 4,498 |
| `permanent` | `permanent/Submission.lean` | 701 | 32/35 | 208,166,925,573 | 4,994 |
| `mertens` | `mertens/Submission.lean` | 699 | 32/32 | 8,450,194,815 | 5,321 |

All eight complete every judged case: coverage 6/6, and 15/15 on `permanent`.

**Read the last column, not the rank.** Distance to the leader and distance to
rank three are not proportional, and the rank alone is misleading: `polydisc`
is last of 33 and is the closest problem on the board to a podium, while
`ca-rule110` is 34th of 39 and is two orders of magnitude further away. The
three problems at the top of the table are the only ones where a podium is a
constant-factor argument rather than a new algorithm.

**How the live entry is identified.** The API will not read a submission back:
`GET /submissions` and `GET /submissions/{id}` both answer `405`, so the board
gives an id and nothing that maps it to a file. `submit.py` derives its
idempotency key from the submission text, so re-sending a file that is already
live is a read rather than a write: `200` returns the stored submission and
creates nothing, `409 IDEMPOTENCY_CONFLICT` means that text was already used
with a different note, and only `201` creates. `whatsliv.py` runs the check.

### What has been ruled out

| Problem | Hypothesis | Measured | Verdict |
|---|---|---|---|
| `ca-rule110` | the stepping dominates, so the initial row is not worth optimising | judged cases ask at most 13 steps: the row is 5,348 of 5,465 operations | **false**, and it was the whole of the gap. Shipped as submission 1613: all 24 judged cases reduce in **0.28 s** against the previous entry's **2.50 s** |
| `fib` | `p.2 ^ 2` goes through `Monoid.npow`, and `Nat.binaryRec` is costly | both designs reduce `n = 150000` in 0.34 s of work, within 2% | **false**; neither suspect is real |
| `polydisc` | the exactness test is a fifth of the bit-work, so removing it is worth a fifth | removing it measures **3%** at the hardest difficulty | the saving is real but small: a bit-length proxy overstates a division by a nearly equal divisor |
| `ca-rule110` | 5,348 narrow operations against 64 wide ones is a factor of 84 | the row alone measures **5.6x**, but all 24 judged cases measure **2.50 s to 0.28 s** | the row-only figure was FLOOR-LIMITED and misled me for a day; see below |

Negative results are kept rather than deleted. Each removes an explanation for
a gap, which is the only thing that makes the next attempt cheaper.

## What is here

| File | What it is |
|---|---|
| `<problem>/Submission.lean` | The entry for that problem, except `partition`. |
| `<problem>/submission-note.md` | The note pasted into the submission form, and the measurements taken before sending. |
| `partition/SubmissionPacked.lean` | The `partition` entry. A whole row of the table in one `Nat`. |
| `partition/Submission.lean` | An earlier, slower entry kept as a fallback: the same recurrence on lists. |
| `baseline-note.md` | The note used for the seven starters submitted before optimisation began. |
| `bench.py` | Builds a candidate in the real problem package, checks its axioms, and times the kernel reducing `impl n`. |
| `compare.py` | Prints several runs side by side. |
| `board.py` | Current standing on one problem, without waiting for the next publish. |
| `whatsliv.py` | Which file each problem's live entry is, by idempotency replay. |
| `submit.py` | Sends one entry. Dry run by default. |

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

## What the judge charges for, settled 18 October 2026

This repository has carried two cost models that call for opposite fixes, and
`polydisc.yml` still says in its header that "whichever the judge charges for
decides what is worth building, and only a measurement can say." The
`ca-rule110` resubmission is that measurement.

| | |
| :--- | ---: |
| operation count predicted | **30.2x** (5,465 operations to 181) |
| raw clock, start-up included | 8.9x (2.50 s to 0.28 s) |
| clock with the 0.24 s start-up subtracted | 56.5x (2.26 s to 0.04 s) |

The prediction sits inside the measurement's own range, so **operation count
predicted this correctly**, and the currency is the number of kernel
reduction steps rather than the width of the operands. `widthcost.py` said as
much from the other direction, measuring a flat per-step cost of about 60 us.

**The 5.6x that argued the opposite was a measurement artefact, and it is
worth knowing how.** It compared an 84x operation ratio for the initial ROW
against a timing whose packed side was within 0.04 s of bare Lean start-up:
the computation had already vanished into the floor, so the ratio measured the
floor and not the work. The lesson is not that the count lies but that **a
ratio is meaningless once either side reaches the measurement floor**, and the
fix is to compare at a scope where both sides still do visible work, which is
what timing all 24 judged cases in one process did.

Against this, the proxy that genuinely does mislead is **bit length**: on
`polydisc` it predicted a fifth and measured 3%, because it scores a division
at `a_bits + b_bits` and so overstates a division by a nearly equal divisor.

**So: count operations, not bits.** That is why the lane-packed row worked, and
it is the rule to apply to the remaining problems.
