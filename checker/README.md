<div align="center">

# The independent checker

**Not a Stage 1 entry. A different question, kept because it answers it.**

[Back to the repository](../README.md) &nbsp;·&nbsp;
[Stage 1](../stage1/README.md) &nbsp;·&nbsp;
[Arena](https://github.com/leanprover/lean-kernel-arena)

</div>

---

> [!IMPORTANT]
> This directory is **not** aimed at the SAIR Lean Kernel Challenge. It targets
> the [Lean Kernel Arena](https://github.com/leanprover/lean-kernel-arena), a
> separate benchmark run by the Lean developers, which measures independent
> proof checkers against a shared suite of exports.
>
> The two are easy to confuse and were confused here. The arena asks you to
> *be* the checker. Stage 1 asks you to hand Lean's own kernel an artifact it
> can check cheaply. Building one does not enter you in the other.

## What it is

A proof checker for Lean 4 in standard-library Python. It reads the NDJSON
export produced by [`lean4export`](https://github.com/leanprover/lean4export),
format version 3.1.0, rebuilds every declaration, and answers with the arena's
exit codes.

| Code | Meaning |
| :--- | :--- |
| `0` | The environment type checks |
| `1` | Something in it does not |
| `2` | The checker does not handle this input, and declines rather than guess |
| anything else | A fault in the checker itself |

## Why it is still here

Because it works, and because the thing it gets right is the thing this whole
subject turns on: it does not believe the file it is reading.

An inductive block arrives carrying its own recursors and a set of integers
describing them. None of that is used as given. The eliminators are derived
from the inductive types and the export is checked against the derivation, so
the two exports in the arena's suite that prove `False` by lying about their
own inductive block are rejected rather than accepted.

| What it refuses | Because |
| :--- | :--- |
| A recursor the inductive block could not have produced | `extra-rec` smuggles one into `False` and derives `False` from it |
| A constructor that misreports its field count | `ctor-num-fields` makes a one-field structure look unit-like so eta collapses it |
| A `Sort u` inductive given large elimination | At `u := 0` it is a `Prop`, and proof irrelevance then proves `False` |
| A declaration that refers to itself | Otherwise `def loop : False := loop` checks against its own declared type |

## Run it

```bash
cd checker
python -m pytest tests -q
python -m src.harness.check_export tests/fixtures/extra-rec.ndjson ; echo $?
```

The two fixtures under [tests/fixtures/](tests/fixtures/) are the arena's own
adversarial exports, kept verbatim. Both exit `1`. The genuine Lean-generated
prefix of the second still exits `0`, which is what makes the derivation
correct rather than merely strict.

## What is unfinished

Listed in [open questions](docs/research/open_questions.md). The quotient
primitives are still believed at their declared types, which is the same class
of mistake as the recursor gap in the one corner where it has not been closed.

**[Back to the repository](../README.md)** &nbsp;·&nbsp;
**[On to Stage 1](../stage1/README.md)**
