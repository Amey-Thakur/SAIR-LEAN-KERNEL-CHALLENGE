<div align="center">

# The competition

**What Stage 1 asks for, what it measures, and what it will not accept.**

[Documentation](../README.md) &nbsp;·&nbsp;
[Stage 1](../../stage1/README.md) &nbsp;·&nbsp;
[Competition](https://competition.sair.foundation/competitions/lean-kernel-challenge/overview)

</div>

---

## The task in one sentence

Given a trusted Lean specification, submit an implementation that Lean's kernel
can verify cheaply, together with a machine-checked proof that the two agree on
every input.

## What is submitted

A package of kind `lean-kernel-package`. Two parts, and the second is not
optional:

| Part | What it is |
| :--- | :--- |
| The implementation | Written to minimise the work the kernel does while reducing it |
| The agreement proof | A machine-checked proof that it matches the specification **on every input**, not on a sample |

## How it is scored

The judge checks the correctness proof first. Only then does it measure, and
what it measures is:

> the work performed by a **pinned Lean kernel** when replaying the complete
> verified correctness artifact and the generated checks for judge-selected
> inputs.

Three things follow from that sentence, and they are the whole strategy.

**The kernel is the machine, not the compiler.** Nothing the compiler does is
being timed. `#eval` uses the compiled code and is no evidence at all. The
number that matters is how many reduction steps the kernel takes.

**The proof term is part of the artifact.** The kernel type-checks it, so a
tactic that closes a goal by emitting a huge term has moved the cost rather
than removed it. A short proof of a slightly harder lemma can beat a long proof
of an easy one.

**The inputs are chosen by the judge.** Tuning the implementation for inputs
you picked is worth nothing. The implementation has to be uniformly cheap.

> [!IMPORTANT]
> Correctness is the entry fee. An artifact that does not prove agreement is
> not slow, it is absent. Every optimisation is only admissible if the proof
> still goes through, which is why the implementation and the proof have to be
> designed together rather than in sequence.

## What is not accepted

| Refused | Why |
| :--- | :--- |
| `sorry` | The goal is not proved, and the artifact is not an artifact |
| `native_decide` | It evaluates outside the kernel and adds `Lean.ofReduceBool` to the axiom list. A scoring rule about kernel work cannot be satisfied by not using the kernel |
| An implementation proved on sample inputs | The task says every input, and a proof by cases over a finite sample is not that |

The axiom list is where this is visible, which is why
[audit.py](../../tools/audit.py) reads it back out of the build rather than
trusting the sources to look clean.

## The shape of the problem set

Announced at launch: algebra, number theory, combinatorics, cryptography and
discrete mathematics. Stage 1 is described by the organisers as the first,
experimental stage, beginning with fundamental computational problems, with
later stages covering more.

That phrasing is worth taking at face value. The first problems are likely to
be ones where the naive specification is obviously right and obviously
expensive, which is exactly the gap the worked example in
[stage1/](../../stage1/README.md) demonstrates.

## Dates

| | |
| :--- | :--- |
| Registration and team formation open | 26 August 2026 |
| Official launch | 15 September 2026 |
| Submission deadline | 20 November 2026, 23:59 AoE (UTC−12) |
| Stage 2 begins | December 2026 |

Co-organised by the Lean FRO and the SAIR Foundation, with Joachim Breitner,
Leonardo de Moura, Kim Morrison and Terence Tao. Results and benchmark data are
released publicly under an open-source licence after evaluation.

## What this repository is not doing

| Not done | Why |
| :--- | :--- |
| Guessing the submission format | It arrives at launch, and a guess would only have to be undone |
| Solving a problem | There are no problems yet |
| Entering the Lean Kernel Arena | Different benchmark, different question. See [checker/](../../checker/README.md) |

**[Back to the documentation](../README.md)** &nbsp;·&nbsp;
**[On to what the kernel costs](../research/kernel.md)**
