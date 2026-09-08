<div align="center">

# Documentation

**What Stage 1 asks, what the kernel costs, and where the other half of this repository fits.**

[Back to the repository](../README.md) &nbsp;·&nbsp;
[Stage 1](../stage1/README.md) &nbsp;·&nbsp;
[Competition](https://competition.sair.foundation/competitions/lean-kernel-challenge/overview)

</div>

---

## 1. The competition

| Document | Question it answers |
| :--- | :--- |
| [competition/analysis.md](competition/analysis.md) | What is submitted, what the judge measures, and what disqualifies an artifact |

## 2. The kernel

| Document | Question it answers |
| :--- | :--- |
| [research/kernel.md](research/kernel.md) | What the kernel does when it reduces, which is the thing being counted |
| [stage1/kernel-cost.md](stage1/kernel-cost.md) | Where the cost actually goes, and the techniques that move it |

## 3. The checker, which answers a different question

[`checker/`](../checker/README.md) is an independent proof checker for Lean 4,
aimed at the [Lean Kernel Arena](https://github.com/leanprover/lean-kernel-arena)
rather than at this competition. Its own documentation lives with it:

| Document | Question it answers |
| :--- | :--- |
| [checker/docs/architecture.md](../checker/docs/architecture.md) | What each layer is responsible for |
| [checker/docs/design_rationale.md](../checker/docs/design_rationale.md) | Why declining is a first-class outcome |
| [checker/docs/research/export_format.md](../checker/docs/research/export_format.md) | The NDJSON export, item by item |
| [checker/docs/research/open_questions.md](../checker/docs/research/open_questions.md) | What is unfinished there |
| [checker/docs/literature/review.md](../checker/docs/literature/review.md) | The other independent checkers |

## The one idea to take away

The two halves of this repository pull in opposite directions, and noticing
that is the fastest way to understand the competition.

The checker asks: *given an artifact, how do I verify it without trusting it?*
Stage 1 asks: *given a kernel I cannot change, how do I hand it an artifact
that is cheap to verify?* One is written from the side of the thing doing the
checking, the other from the side of the thing being checked.

What they share is the reason either is hard. The kernel's cost is
concentrated in reduction and definitional equality, so both questions come
down to the same one: which reductions actually have to happen, and which only
look as though they do.

**[Back to the repository](../README.md)** &nbsp;·&nbsp;
**[On to the competition](competition/analysis.md)**
