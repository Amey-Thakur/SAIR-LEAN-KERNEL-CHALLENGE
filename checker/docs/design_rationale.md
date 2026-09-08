<div align="center">

# Design rationale

**Three decisions, and the failure each one is there to prevent.**

[Documentation](README.md) &nbsp;·&nbsp;
[Architecture](architecture.md) &nbsp;·&nbsp;
[Checker](../src/README.md)

</div>

---

## 1. Declining is a first-class outcome

Most programs have two outcomes: it worked, or it did not. A proof checker has
three, and the third one is the one that keeps the other two honest.

| | If unimplemented cases exited `1` | If they exited `0` | Here |
| :--- | :--- | :--- | :--- |
| Cost | Correct proofs called false | False proofs called true | An entry that scores nothing on that input |
| Detectable | Yes, loudly | **No** | Yes, in the message |

The second column is the failure that has no symptom. A false acceptance and a
true one are the same exit code, so nothing downstream can tell them apart, and
the error surfaces only when someone eventually trusts the result.

So every unimplemented case in this repository raises `Declined`. Structure
projections, unsafe declarations, unknown export items, exhausted budgets. None
of them has a path to `0`, and none of them quietly becomes a rejection either,
because claiming a proof is false is also a claim.

## 2. Reduction runs on a budget

`whnf` has fuel. When it runs out it raises `Declined` rather than continuing.

A kernel meets terms whose reduction is long and terms whose reduction does not
terminate at all, and the two look identical from inside the loop. A checker that
runs until the benchmark kills it has produced no answer, and has also produced
no information about why.

Declining is worse than answering and better than hanging, and it is the only one
of the three that is honest about what happened.

## 3. Nothing gets faster without an argument

This is a performance competition, so the temptation is obvious: cache the
comparisons, share the terms, add the fast paths, measure the improvement.

Each of those is a claim.

| Optimisation | The claim underneath it |
| :--- | :--- |
| Caching a comparison | These two terms are still the same in every later context |
| Sharing subterms | Two pointers to one value cannot diverge |
| A cheap pre-test | This test failing implies the expensive one would have failed |
| Skipping an unfold | The answer cannot depend on what is inside |

Nothing verifies any of them. A wrong one does not slow the checker down or make
it crash; it makes it accept a term that does not type check, which is precisely
the outcome that cannot be observed.

The order of work therefore runs: correct first, declining honestly wherever it
is incomplete, and only then fast. Every speed change has to arrive with the
argument for why what it skips was redundant, and with a test that would fail if
the argument were wrong.

> [!IMPORTANT]
> The right question about an optimisation here is not "did it get faster". It
> is "what would have to be true for this to still be sound, and what breaks if
> it is not".

## What this costs

A Python checker on a fuel budget that declines projections is not going to win a
speed benchmark. That is understood. The point of this shape is that when it
does answer, the answer means something, and every place it does not answer says
so out loud.

An entry that is right on what it covers and honest about what it does not is a
better starting point than one that is fast and cannot tell you which of its
acceptances it actually earned.

**[Back to the documentation](README.md)** &nbsp;·&nbsp;
**[On to the open questions](research/open_questions.md)**
