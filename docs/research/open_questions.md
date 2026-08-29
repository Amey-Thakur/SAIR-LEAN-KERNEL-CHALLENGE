<div align="center">

# Open questions

**What is unfinished, stated plainly, including the parts that would be easy to hide.**

[Documentation](../README.md) &nbsp;·&nbsp;
[Rationale](../design_rationale.md) &nbsp;·&nbsp;
[Prior work](../literature/review.md)

</div>

---

## Known gaps

These are gaps, not open research. Each one is a thing this checker does not do
yet, and each one currently produces `Declined` rather than a guess.

| Gap | Status |
| :--- | :--- |
| Structure projections | `infer` declines on `proj`. Nothing that uses a structure field can be checked |
| Unsafe declarations | Declined by `check_declaration` |
| Quotient primitives | Read and stored, but their computation rule is not implemented |
| Nat and String literal arithmetic | Literals are typed, but the kernel's fast arithmetic on them is not implemented |
| Recursor derivation | See below. This is the one that is not merely incomplete |

## The gap that is not merely incomplete

The arena's `extra-rec` and `ctor-num-fields` tests both prove `False` from an
export whose structural fields are false. The recursor in the first is fabricated
outright; the constructor in the second lies about how many fields it has.

This checker currently reads recursors and their `numFields` from the export and
uses them. That is exactly the behaviour those tests are built to catch.

> [!WARNING]
> A checker must derive which recursors an inductive declaration can produce, and
> reject any exported recursor that is not one of them. Until that is
> implemented, an acceptance here is conditional on the export being honest about
> its inductive block, which is not something a proof checker gets to assume.

The right fix is to synthesise the recursors and their rules from the inductive
types and constructors, and compare, rather than to add a special case for the
shape these two tests happen to take. Until it is done, this is the first thing
to know about this entry.

## Performance questions, none of them settled

| Question | Why it is not obvious |
| :--- | :--- |
| **What is a sound cache key for `is_def_eq`?** | A pair of terms is not enough on its own: the answer has to be stable under every context the pair can appear in. `nanobruijn` buckets its cache by binding depth for exactly this reason |
| **How much does structural sharing buy?** | Terms in an export are already shared by index. Keeping that sharing through reduction, so pointer equality settles comparisons early, is a representation change rather than an algorithm change |
| **When is skipping an unfold sound?** | Delta is the dominant cost, and most unfolds turn out to be unnecessary. Deciding which, before doing them, is where every real kernel spends its heuristics |
| **What does proof irrelevance actually cost?** | It requires inferring both types and checking they are propositions, which is the most expensive test in `is_def_eq`, and it is tried last for that reason. Whether a cheap pre-filter exists is untested |
| **How far up the corpus ladder does this reach?** | `init-prelude`, `init`, `std`, `mathlib`, `cedar`, `cslib`. Nothing above the small tests has been measured here |

## The question behind all of them

Every one of the performance questions above is the same question in a different
costume: what would have to be true for this shortcut to be sound, and what
breaks if it is not.

Nothing in the system answers that. The compiler does not, the tests only answer
it for the cases someone thought of, and the benchmark cannot tell a fast correct
checker from a fast wrong one. Which is why the honest order of work is to
implement the recursor derivation first, and to leave the caching until there is
an argument for it that does not reduce to "it got faster and nothing broke".

**[Back to the documentation](../README.md)** &nbsp;·&nbsp;
**[Back to the checker](../../src/README.md)**
