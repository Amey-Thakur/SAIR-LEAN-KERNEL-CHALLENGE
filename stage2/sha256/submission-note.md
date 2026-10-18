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

---

## Where the arithmetic cost is, measured 18 October 2026

The note above drew the right conclusion from its own 11%: the cost of this
problem is the round function's masked 32-bit arithmetic, not the plumbing
around it. `model.py` now counts that arithmetic. It transcribes the
specification and a candidate, and checks both against the specification AND
against `hashlib`, which shares no code with either transcription: 7 seeds,
4 chained steps each, no mismatches.

Three changes were modelled. Only one of them is worth anything:

| change | operations per chained step | |
| :--- | ---: | ---: |
| the specification | 4,528 | 1.00x |
| defer the mask across a chain of additions | 4,336 | 1.04x |
| rotate with one multiplication | 3,056 | **1.48x** |
| fold the padding's zero words out of the schedule | 2,988 | 1.52x |

`add32` masks after every single addition, and a sum of five terms needs one
mask rather than five, so deferring looked promising. It is worth 1.04x,
because the masks are only four operations of the round's fifty-one. Folding
the padding is worth 1.5%: every chained step hashes 32 bytes, so the block's
words 8 to 15 are the constants `[0x80000000, 0, 0, 0, 0, 0, 0, 256]` on all
512 steps, but only a handful of early expansion steps gain a dropped term.

**The rotation carries essentially all of it.** The specification rotates with
two shifts, an or and a mask, so a sigma is three rotations and two exclusive
ors: fourteen operations. For `x < 2 ^ 32`, `x * 0x100000001` is `x` placed
twice side by side, so every rotation is a single shift of that doubled word,
and because masking distributes over exclusive or the three rotations share one
mask. Fourteen becomes seven.

### What is proved

`RotProbe.lean` compiles with zero errors in CI and contains the whole
mathematical core:

- `and_w32` - masking to 32 bits is reduction modulo `2 ^ 32`;
- `testBit_dbl` - every bit of the doubled word, which is the trick itself;
- `rotr32_eq` - a rotation is one shift of the doubled word and one mask;
- `xor_and_w32` - masking distributes over exclusive or;
- `bigSigma0_eq`, `bigSigma1_eq`, `smallSigma0_eq`, `smallSigma1_eq`.

Two syntax facts cost a CI round each and are worth recording: on `Nat`, `^^^`
is LEFT associative, so `a ^^^ b ^^^ c` is `(a ^^^ b) ^^^ c` and a two-term
lemma suffices; and on `Bool`, `^^` binds more loosely than `=`, so an identity
over `^^` must be parenthesised in full or it is read as a `decide` of an
equation.

### Why it was not integrated

Every one of those lemmas needs `x < 2 ^ 32`, and it genuinely needs it: the
specification's `rotr32` masks only at the end, so bits of `x` at or above 32
DO leak into the result, and `bigSigma0 x` is not `bigSigma0 (x &&& w32)`.

The live entry's correctness proof carries no bound on any word at all. It
works by structural correspondence, because it reorganised the plumbing and
kept the specification's arithmetic verbatim. Using these lemmas therefore
means threading a "every word is below `2 ^ 32`" invariant through four nested
inductions - the message schedule, the 64 rounds, the 512-step chain and the
seed - each of which would have to be restated with the hypothesis. The
invariant itself is trivial at every point, since every word is produced by
`add32` or is a padding constant; the cost is purely volume, of the order of
100 to 200 lines.

Against that, here is what the change buys:

| | score | distance to rank 3 |
| :--- | ---: | ---: |
| the live entry | 151,072,678,381 | 15.0x |
| rotation only, at the modelled 1.48x | 102,076,134,041 | 10.1x |
| all three changes, at 1.52x | 99,389,919,988 | 9.9x |
| a hypothetical perfect 2x | 75,536,339,190 | 7.5x |
| rank 3 | 10,062,530,150 | - |

**Even a perfect doubling leaves this problem 7.5x short of a podium.** The
rotation is real and the lemmas are proved and kept, but it buys about one rank
place for that volume of proof, and it does not change what this problem needs.
Reaching 10,062,530,150 means about 1.7 kernel steps per SHA-256 round, which
no arrangement of elementary operations on 32-bit words can reach; it needs a
representation that does several of the round's operations in one `Nat`
operation, and packing the eight working variables into lanes does not provide
it - the bitwise functions `ch` and `maj` cost MORE packed (10 operations
against 5) because their three operands sit at different lane offsets.

So this is recorded as a measured partial result rather than shipped. Nothing
was submitted and `Submission.lean` is untouched.
