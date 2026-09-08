<div align="center">

# Where the cost goes

**The kernel is not the compiler, and almost every mistake here follows from forgetting that.**

[Documentation](../README.md) &nbsp;·&nbsp;
[Stage 1](../../stage1/README.md) &nbsp;·&nbsp;
[What the kernel does](../research/kernel.md)

</div>

---

## The one distinction that matters

Lean has two evaluators and they have nothing to do with each other.

| | Runs | Used by | Counted by the judge |
| :--- | :--- | :--- | :--- |
| The **compiler** | compiled code, with real machine arithmetic | `#eval`, `native_decide`, anything you run | **No** |
| The **kernel** | definitional unfolding of the term as written | checking a proof, `decide`, `rfl` | **Yes** |

> [!CAUTION]
> A definition that evaluates instantly under `#eval` can be ruinous for the
> kernel, and the reverse happens too. Timing `#eval` while optimising for the
> kernel measures the wrong machine, and it is the easiest way to spend a week
> going backwards.

The honest test is to make the fact a proof. If the kernel can close
`example : f 1000 = 2000 := by rfl` quickly, the kernel can reduce `f`
quickly. That is what [Cost.lean](../../stage1/Stage1/Cost.lean) does: every
claim in it is checked by the kernel when the package builds.

## What the kernel is cheap at

**`Nat` literals.** The kernel has GMP-backed arithmetic for `Nat`, so
addition, multiplication, division, remainder and the decidable comparisons on
literals cost about the same whatever the magnitude. A closed form that lands
on literal arithmetic is close to free.

**Reaching a normal form early.** Reduction stops as soon as the head is
determined, so a definition that commits quickly costs less than one that has
to be unfolded to the leaves before anything is decided.

## What the kernel is expensive at

| Pattern | Why it costs |
| :--- | :--- |
| **Recursion on the unary structure** | Unfolding once per unit means the cost tracks the *value*, not its size. Doubling by `n+1 ↦ double n + 2` is linear in `n`; `2 * n` is not |
| **Large proof terms** | The kernel type-checks the proof as well as the definitions, so a tactic that emits a huge term has relocated the cost, not removed it |
| **`decide` on a heavy decision procedure** | It forces the kernel to run the whole procedure. Cheap when the procedure is cheap, disastrous when it is not |
| **Well-founded recursion** | Definitions compiled through `WellFounded.fix` do not reduce in the kernel the way structural ones do, so what looks like a definition can turn out to be opaque |

## Things that do not help

Worth stating because they look like optimisations and are not.

| Non-optimisation | Why |
| :--- | :--- |
| `@[inline]`, `@[specialize]` | Compiler directives. The kernel does not read them |
| `@[reducible]`, `@[irreducible]` | Elaboration hints. The kernel unfolds what it needs regardless |
| `@[simp]` | Changes how tactics build the proof, not how the kernel checks it. It can still help indirectly by producing a smaller term |
| Faster `#eval` | Measures the compiler. See above |

## The shape of a good submission

Design the implementation and the proof together, not one after the other.

1. Find a form the kernel reduces cheaply, usually one that ends in literal arithmetic rather than in structural recursion.
2. Check that the agreement proof is still reachable. The cheapest implementations are frequently the hardest to relate back to the specification, and an unprovable implementation scores nothing.
3. Keep the proof term small. A short proof of a slightly stronger lemma often beats a long proof of the obvious one.
4. Audit before submitting. `sorry` and `native_decide` are the two ways to have nothing at all, and both are visible in the axiom list.

## What is not known yet

The problems. Everything above is about the machine rather than about any
particular problem, which is why it can be written now. Once the problem set
lands on **15 September 2026**, the open question becomes which of these levers
each problem actually rewards, and that is measurable rather than arguable.

**[Back to the documentation](../README.md)** &nbsp;·&nbsp;
**[On to Stage 1](../../stage1/README.md)**
