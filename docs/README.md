<div align="center">

# Documentation

**The reasoning behind the checker, in the order it is worth reading.**

[Back to the repository](../README.md) &nbsp;·&nbsp;
[Checker](../src/README.md) &nbsp;·&nbsp;
[Competition](https://competition.sair.foundation/competitions/lean-kernel-challenge/overview)

</div>

---

Read these in order and the decisions in `src/` stop looking arbitrary. Each one
answers a question the next one depends on.

## 1. What the competition actually demands

| Document | Question it answers |
| :--- | :--- |
| [competition/analysis.md](competition/analysis.md) | What is submitted, how it is invoked, and what the three exit codes commit the submitter to |

## 2. What has to be read

| Document | Question it answers |
| :--- | :--- |
| [research/export_format.md](research/export_format.md) | The NDJSON export, item by item: the three tables, the declarations, and what a reader is not allowed to do with an item it does not know |

## 3. What has to be decided

| Document | Question it answers |
| :--- | :--- |
| [research/kernel.md](research/kernel.md) | Reduction, definitional equality, universes and recursors: the four things a kernel is, and where each one is expensive |
| [architecture.md](architecture.md) | What each directory is responsible for, and what it is deliberately not allowed to know |
| [design_rationale.md](design_rationale.md) | Why declining is a first-class outcome, why reduction runs on a budget, and why no optimisation ships without an argument for why it is sound |

## 4. What is already known

| Document | Question it answers |
| :--- | :--- |
| [literature/review.md](literature/review.md) | The independent checkers that already exist, what each one demonstrated, and what is left to try |
| [research/open_questions.md](research/open_questions.md) | What is unsettled here: caching keys, sharing, the cost of proof irrelevance, and how much of Mathlib this reaches |

## The one idea to take away

Every optimisation in a proof checker is a claim that two things are the same.

A cache claims a term checked once does not need checking again. Sharing claims
two pointers are one value. A fast path claims a cheap test implies an expensive
one. Each claim is a small theorem, and none of them is checked by anything.

That is why the interesting constraint here is not speed. It is that the cost of
being wrong is not a slow answer, it is a false one, and a false acceptance is
indistinguishable from a true one from the outside. So the honest structure is
one where the parts that can be wrong are small, the parts that are unimplemented
say so, and nothing gets faster without an argument for why it still holds.

**[Back to the repository](../README.md)** &nbsp;·&nbsp;
**[On to the checker](../src/README.md)**
