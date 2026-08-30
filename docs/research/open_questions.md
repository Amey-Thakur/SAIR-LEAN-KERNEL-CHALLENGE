<div align="center">

# Open questions

**What is unfinished, stated plainly, including the parts that would be easy to hide.**

[Documentation](../README.md) &nbsp;·&nbsp;
[Rationale](../design_rationale.md) &nbsp;·&nbsp;
[Prior work](../literature/review.md)

</div>

---

## What used to be here

This page previously opened with a warning: the checker read recursors and
constructor field counts straight out of the export and used them. That is the
behaviour the arena's `extra-rec` and `ctor-num-fields` tests are built to
catch, and both of those are proofs of `False`.

That gap is closed. Inductive blocks are now derived rather than believed, in
[inductive.py](../../src/kernel/inductive.py): the eliminator, its rules, the
field counts, the index counts and the `k` flag are all computed from the
inductive types alone, and the export is checked against what was derived.
Anything the block could not have produced is rejected.

Closing it turned up a second false acceptance that had nothing to do with
recursors. Because the whole export was read before any of it was checked, a
declaration could refer to itself, and `def loop : False := loop` type checked
against its own declared type. Declarations are now admitted in dependency
order, which is what Lean's kernel gets for free by adding one at a time.

## Known gaps

Each of these produces `Declined` rather than a guess.

| Gap | Status |
| :--- | :--- |
| Structure projections | `infer` declines on `proj`. Nothing that uses a structure field can be checked |
| Nested inductives | An occurrence under another type former, as in `node : List Tree → Tree`, is declined. It is not unsound, and rejecting it would call ordinary mathematics false |
| Quotient types | See below. This is the one that is not merely incomplete |
| Nat and String literal arithmetic | Literals are typed, but the kernel's fast arithmetic on them is not implemented |
| Unsafe declarations | Outside what a kernel is supposed to trust |

## The gap that is not merely incomplete

`Quot`, `Quot.mk`, `Quot.lift` and `Quot.ind` are read from the export and their
declared types are used as given. Lean's kernel does not do that: it checks the
four quotient constants against fixed expected types, because they are
primitives rather than definitions.

> [!WARNING]
> An export that declares `Quot` at a type of its own choosing is believed. This
> is the same class of mistake the recursor derivation just fixed, in the one
> corner where it has not been done yet, and it is the next thing to work on.

The fix is bounded: build the four expected types and compare. `Quot.lift`
mentions `Eq`, so it has to be built after the environment has one, which is the
only fiddly part.

## Where the conservatism costs completeness

These are places where the checker refuses something a more complete one would
accept. None of them is a soundness risk, and each is a deliberate choice of the
safe direction.

| Choice | What it costs |
| :--- | :--- |
| A mutual block that might be a Prop gets Prop elimination only | A mutual subsingleton in Prop would be refused a large eliminator. No such type is known in core |
| A universe that is a bare parameter is treated as possibly zero | Correct, and the whole point of the `large-elim-param` test, but it means `Sort u` inductives are held to the subsingleton rule |
| Reduction runs on a fuel budget | A long but terminating reduction can be declined rather than finished |

## Performance questions, none of them settled

| Question | Why it is not obvious |
| :--- | :--- |
| **What is a sound cache key for `is_def_eq`?** | A pair of terms is not enough on its own: the answer has to be stable under every context the pair can appear in. `nanobruijn` buckets its cache by binding depth for exactly this reason |
| **How much does structural sharing buy?** | Terms in an export are already shared by index. Keeping that sharing through reduction, so pointer equality settles comparisons early, is a representation change rather than an algorithm change |
| **When is skipping an unfold sound?** | Delta is the dominant cost, and most unfolds turn out to be unnecessary. Deciding which, before doing them, is where every real kernel spends its heuristics |
| **Is deriving every block too slow?** | Each inductive block now costs a derivation and a definitional equality check against the export. Correct, and unmeasured at the scale of Mathlib |
| **How far up the corpus ladder does this reach?** | `init-prelude`, `init`, `std`, `mathlib`, `cedar`, `cslib`. Only the small tests and two arena fixtures have been measured here |

## The question behind all of them

Every one of the performance questions above is the same question in a different
costume: what would have to be true for this shortcut to be sound, and what
breaks if it is not.

Nothing in the system answers that. The compiler does not, the tests only answer
it for the cases someone thought of, and the benchmark cannot tell a fast correct
checker from a fast wrong one. Which is why the honest order of work is to
finish the quotient primitives first, and to leave the caching until there is an
argument for it that does not reduce to "it got faster and nothing broke".

**[Back to the documentation](../README.md)** &nbsp;·&nbsp;
**[Back to the checker](../../src/README.md)**
