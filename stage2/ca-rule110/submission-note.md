# Submission note — `ca-rule110`

Paste the block below into the **Submission note** field.

```
Approach: the whole row in one natural number.

The specification holds the row as a List Bool of length 256 and reads each neighbour with getD, which walks the list. Three reads per cell across 256 cells make one step quadratic, and the judge asks for up to eight steps: roughly 786,000 list traversal steps for a row that is 256 bits of information.

This submission keeps the specification's automaton exactly and changes only where the row lives. Cell i becomes bit i of a single Nat, and the entire row steps at once:

  new = (c ||| r) &&& ~~~(l &&& c &&& r)

where l is the row rotated one place up and r one place down, both cyclically inside a 256-bit mask. That expression is the specification's own three-case rule110 table; rule110_eq proves the two agree on all eight patterns rather than assuming it. Eight Nat operations per step, so 64 for the judged maximum, against roughly 786,000 list steps.

Correctness. The proof rests on one theorem, pStep_encodeRow: a packed step and a list step are the same row seen two ways. It is proved bit by bit through Nat.eq_of_testBit_eq, splitting at the row width. Below the width, testBit_rotL and testBit_rotR show that bit i of each rotation is the cyclic neighbour the specification reads, each proved against the hypothesis that the row has no bits at or above 256, which is what makes a rotation wrap rather than leak. At or above the width both sides are absent: the packed side because every rotation is masked, the list side because a row says nothing past its length. pIter_encodeRow then lifts this to any number of steps by induction, carrying the width invariant through length_stepRow.

Nothing else is optimised, deliberately. The initial row is still built by the specification's own initRowFor and encoded once by its own encodeRow. That costs a few hundred kernel steps against the hundreds of thousands the stepping costs, and it means this file needs no lemma about how the row is created. The remaining gain there is small and the proof obligation is not.

impl_correct is proved for every n, including step counts far outside the judged range and the zero-step case. The file is self-contained and uses core Lean only, with no Mathlib dependency, so every lemma is about the exact function the kernel reduces. #print axioms Submission.impl_correct reports propext, Classical.choice and Quot.sound, all permitted.

No precomputed answers. There is no lookup table, no hardcoded value and no input-dependent branch carrying an answer; every cell is computed from the specification's own rule at evaluation time. The design was checked against the specification in a separate reference implementation before any Lean was written, including both wrap-around edge cases and step counts beyond the judged maximum, and the kernel was then checked to reduce impl to the specification's own values on 24 cases.

Acknowledgements and references. No Contributor Network item and no external source was used. Carrying several cells in the bits of one word so that a neighbourhood becomes a shift and a mask is a known idiom in bit-parallel cellular automaton simulation and is not claimed as new; what is specific to this entry is the correspondence proof against this locked list-based specification, and the observation that arbitrary-precision Nat removes the usual word-size ceiling so the bound needed is on the row width rather than on the machine.
```

## The other fields

| Field | Value |
|---|---|
| Problem | **ca-rule110** |
| Submission source | **Upload Submission.lean** |
| File | `stage2/ca-rule110/Submission.lean` |
| Reference | leave empty; nothing from the Contributor Network was used |

## Verified before submitting

Run `36280925440` of `.github/workflows/ca.yml`, on the challenge pinned at
`940f0a2ead23ef70ab1387edabb347e629111edd`:

- `lake build` inside the real problem package: **0 errors**.
- `#print axioms Submission.impl_correct`:
  `[propext, Classical.choice, Quot.sound]`, all three permitted.
- The kernel reduces `impl n` to the specification's own value on **24 cases**,
  covering 0, 1, 2, 4, 8 and 13 steps across four seeds.
- `model.py` re-checks the design against the specification on every run, so a
  build cannot pass with an algorithm that has drifted from the spec.
