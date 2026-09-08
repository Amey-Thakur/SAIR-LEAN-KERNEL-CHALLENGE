<div align="center">

# Checker documentation

**The reasoning behind the independent checker, in the order it is worth reading.**

[The checker](../README.md) &nbsp;·&nbsp;
[Back to the repository](../../README.md) &nbsp;·&nbsp;
[Arena](https://github.com/leanprover/lean-kernel-arena)

</div>

---

> [!NOTE]
> This documents the checker in [checker/](../README.md), which targets the
> Lean Kernel Arena. For the SAIR competition itself, read
> [the Stage 1 documentation](../../docs/README.md) instead.

## 1. What has to be read

| Document | Question it answers |
| :--- | :--- |
| [research/export_format.md](research/export_format.md) | The NDJSON export, item by item, and what a reader may not do with an item it does not know |

## 2. What has to be decided

| Document | Question it answers |
| :--- | :--- |
| [architecture.md](architecture.md) | What each layer is responsible for, and what it is deliberately not allowed to know |
| [design_rationale.md](design_rationale.md) | Why declining is a first-class outcome, and why nothing gets faster without an argument |

## 3. What is already known, and what is left

| Document | Question it answers |
| :--- | :--- |
| [literature/review.md](literature/review.md) | The independent checkers that already exist, and what each demonstrated |
| [research/open_questions.md](research/open_questions.md) | What is unfinished here, including the quotient primitives |

## The one idea to take away

Every optimisation in a proof checker is a claim that two things are the same,
and nothing verifies the claim. A wrong one does not make the checker slow. It
makes it accept a false proof, which is the only failure that cannot be
observed from the outside.

**[Back to the checker](../README.md)** &nbsp;·&nbsp;
**[Back to the repository](../../README.md)**
