# Submission note — `sha256`

```
Approach: fuse the message schedule into the rounds, so no list is built per block.

The shipped starter already carries the larger optimisation and it is kept: it replaced the specification's list-indexed extendW with a sixteen-field Window, so reading a schedule word no longer walks a list. What remained is that fastStep still materialises two lists for every block, a 64-word schedule and then K.zip of it into 64 pairs. Across 512 chain steps that is roughly 65,000 cons cells allocated only to drive a loop whose trip count is already fixed.

Neither list is needed. The window yields the current word as w.x0 in one projection and sliding it produces the next, so the schedule can be walked as the rounds consume it, with the round constants walked head-first in lockstep.

Correctness rests on two lemmas. roundsW_eq says the rounds walk exactly the schedule the window produces, for any constant list and any window, with no hypothesis at all; that generality comes from naming the walked schedule directly rather than as toList ++ generate, a phrasing which needs a side condition that fails when the constant list is short. sched_eq then says sixteen steps of that walk are the window itself and every step after is a generated word, which connects it back to the starter's own fastSchedule and so to its proof of the specification.

Measured honestly. Starter and candidate were timed in the same continuous-integration job on the same runner, because wall times on shared runners vary by about twenty per cent between runs and the effect here is smaller than that. At the judged group boundaries: 4 chain steps 0.57 s against 0.52 s, 32 steps 3.16 s against 2.82 s, and 512 steps 59.60 s against 53.34 s. That is about eleven per cent.

It is worth saying plainly that eleven per cent is much less than removing 65,000 allocations suggested, and the measurement is the correction: the cost of this problem is the round function itself, roughly half a million masked 32-bit operations across 512 blocks, not the plumbing around it. The remaining headroom is in the arithmetic, not in the lists.

impl_correct is proved for every n. #print axioms Submission.impl_correct reports propext and Quot.sound, two of the three permitted, without reaching for Classical.choice.

No precomputed answers, and the specification is unchanged: the same rounds in the same order on the same words. Expected values used to check the kernel came from Lean's own compiler through #eval, a different evaluator from the kernel being measured.

Acknowledgements and references. No Contributor Network item and no external source was used. The Window formulation of the message schedule is the starter's and is not claimed here; what this entry adds is the fusion of the schedule into the rounds and the two lemmas that license it.
```

## Measured before submitting

Run `36285438556`, challenge pinned at `940f0a2ead23ef70ab1387edabb347e629111edd`.
Build clean; `#print axioms Submission.impl_correct` reports
`[propext, Quot.sound]`.

| chain steps | starter | this entry |
| ---: | ---: | ---: |
| 4 | 0.57 s | 0.52 s |
| 32 | 3.16 s | 2.82 s |
| 512 | 59.60 s | **53.34 s** |
