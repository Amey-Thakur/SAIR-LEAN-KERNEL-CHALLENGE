<div align="center">

# Prior work

**The checkers that already exist, and what each one demonstrated.**

[Documentation](../README.md) &nbsp;·&nbsp;
[Kernel](../research/kernel.md) &nbsp;·&nbsp;
[Arena](https://arena.lean-lang.org/)

</div>

---

Independent checkers are not a new idea, and the
[Lean Kernel Arena](https://github.com/leanprover/lean-kernel-arena) runs a
dozen of them against a shared suite. Reading what they chose is more useful
than starting from a blank file, because the interesting decisions are all
visible in what they refuse to do.

## The reference points

| Checker | Language | What it is for |
| :--- | :--- | :--- |
| [Lean's own kernel](https://github.com/leanprover/lean4) | C++ | The thing every other entry is measured against. The arena also runs it in `--parse-only` mode, which separates the cost of reading an export from the cost of checking it |
| [Lean4Lean](https://github.com/digama0/lean4lean) | Lean 4 | The kernel written in Lean itself, derived from the C++ implementation, and the home of the metatheory work. Its own manifest is candid that being derived from C++ makes it not really independent |
| [nanoda](https://github.com/ammkrn/nanoda_lib) | Rust | The long-standing independent implementation, and the ancestor most of the Rust and Zig entries are forked from |

## What the variants are exploring

| Checker | Language | The idea being tested |
| :--- | :--- | :--- |
| [nanobruijn](https://github.com/leanprover/lean-kernel-arena) | Rust | Pure de Bruijn indices instead of locally nameless, with shifting deferred into pointer-plus-offset pairs so that terms differing by a uniform shift share one node |
| [kiota](https://github.com/sankalpsthakur/kiota) | Rust | Re-deriving K-likeness and iota rather than trusting the export's own fields for them |
| [rpylean](https://github.com/Julian/rpylean) | RPython | Whether a Python checker can be translated into something fast enough to matter |
| [nyaya](https://github.com/kodyvajjha/nyaya) | OCaml | A functional implementation, currently declining everything past the smallest corpus |
| [zignodamus](https://github.com/intgrah/zignodamus) | Zig | A port of a nanoda descendant into a systems language with explicit allocation |
| [vow-lean-kernel](https://github.com/pmatos/vow-lean-kernel) | Vow | A young systems language, and an entry that states plainly that it declines what it does not cover rather than falsely rejecting it |
| [mini](https://github.com/nomeata/lean-mini-kernel) | Lean 4 | A deliberately naive and incomplete kernel, written to improve the arena's own test coverage |

Two patterns run through the list. The performance work is almost entirely about
representation, not algorithms: sharing, lazy shifting, caching keyed by binding
depth. And the honest entries publish what they decline, as a field in their
manifest, rather than quietly failing on it.

## The corpora

Entries are run against a ladder: `init-prelude`, `init`, `std`, `mathlib`,
`cedar`, `cslib`. Several entries decline the upper rungs outright, and the
arena treats that as a legitimate declared position rather than a failure.

## The tests that matter most

The arena does not only feed checkers real proofs. It feeds them exports that
lie, and those cases are the sharpest statement of what this problem actually is.

| Test | The lie | What it catches |
| :--- | :--- | :--- |
| `extra-rec` | An extra recursor named `rogue` is smuggled into `False`'s inductive group, with no motives, no minors and no rules, and its type is `False` itself | A checker that registers exported recursors as given, instead of deriving which recursors an inductive declaration can produce, ends up holding an inhabitant of the empty type |
| `ctor-num-fields` | A one-field structure declares `numFields` of `0`, making it look unit-like | Definitional eta then equates all of its inhabitants, and `S.mk false = S.mk true` follows |
| `bogus1` | An openly invalid proof | The floor: an entry that cannot reject this is not checking anything |

> [!IMPORTANT]
> Both of the first two are proofs of `False`, and neither is a bug in a
> checker's reduction or equality. They are what happens when a checker believes
> a field the export told it. That is the sense in which trusting the exporter
> means having checked nothing.

## What this repository takes from that

| Taken | From |
| :--- | :--- |
| Declining is a declared position, not a failure | `vow-lean-kernel`, `mini`, `nyaya`, and the arena's own `declines` field |
| The export's structural claims are the attack surface | `extra-rec` and `ctor-num-fields` |
| Representation is where the time goes | `nanobruijn`'s offsets and depth-stratified caches |
| A Python entry is not automatically pointless | `rpylean` |

**[Back to the documentation](../README.md)** &nbsp;·&nbsp;
**[On to the open questions](../research/open_questions.md)**
