# Paper data

The measurements behind every number quoted in the manuscript *A whole table row
in one natural number: kernel-checked dynamic programming with a proved width
bound*. They live here, in the public repository, so that a reader can check the
paper's figures without needing access to the manuscript's own repository.

| file | what it holds |
| --- | --- |
| `step_model.json` | operation counts for the three designs at the six judged sizes, under the model stated in the paper: one step per `Nat` primitive, per definition unfolding, and per list constructor match |
| `wall_time.json` | reduction wall time for the same three designs, measured in one continuous-integration job on one runner, plus the field-width study and the competition judge's own figures |
| `bound_slack.json` | how loose the proved field-width bound is against the widths actually needed |
| `all_problems.json` | what was done to each of the eight problems in the challenge, and what it measured |
| `check_numbers.py` | the guard: it reads the manuscript and fails if any quoted figure disagrees with these files |

## Two things in `wall_time.json` worth reading before using it

**The route matters more than the runner.** An obligation written `:= rfl` is
settled by the elaborator's own definitional-equality checker; written
`:= by rfl` it is routed so the kernel performs the reduction. The two differ by
a factor of 478 at n = 18 on the list design, and above that size the elaborator
route does not finish. The three-design table was re-measured through the kernel;
the field-width study was not, because the wide-width variant no longer exists as
a file. The two routes agree on the packed design, which totals 0.07 s either
way, which is why a comparison between two packed widths is still usable. The
superseded figures are recorded in the file rather than deleted.

**Wall time is not the competition's metric.** The judge counts hardware
instructions through `perf_event_open`, which a shared runner does not expose.
The `judged` block holds the two figures the judge has actually produced for
designs from this family: 131,460,833 for the packed row and 3,396,012,941 for a
narrow-operand alternative proved by the same argument. Those are the judge's
numbers. Everything else here is a substitute for them, and the same block
records how far each substitute was off: wall time low by 1.6x, the operation
count low by 3.9x.

## Reproducing the figures

The Lean entries, the benchmark harness and the workflow that produced the
timings are in `stage2/` of this repository. `check_numbers.py` needs the
manuscript to check it against and so is included for reference rather than to
be run here.
