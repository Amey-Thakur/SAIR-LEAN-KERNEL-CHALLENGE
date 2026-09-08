# Arena fixtures

These two files are copied verbatim from the
[Lean Kernel Arena](https://github.com/leanprover/lean-kernel-arena) test suite,
at `tests/` in that repository. They are kept here rather than reconstructed
because a reconstruction of an attack is not the attack.

| File | What it is | Arena outcome |
| :--- | :--- | :--- |
| `extra-rec.ndjson` | A recursor named `rogue` smuggled into the inductive block of `False`, with no motives, no minors and no rules, whose type is `False` itself. The theorem `inconsistent : False` is then just `rogue` | `reject` |
| `large-elim-param.ndjson` | `MyBool.{u} : Sort u` with two constructors, given a large-eliminating recursor. At `u := 0` it is a `Prop`, so proof irrelevance makes `tt` and `ff` equal and the eliminator proves `False`. Found by Anthony Wang using Aristotle | `reject` |

The second file is also the closest thing here to a positive test against real
Lean output: everything in it before `MyBool` is a genuine export of `False` and
`True`, recursors and reduction rules included, and this checker accepts that
part. A derivation that were merely strict rather than correct would reject it.

Both are licensed as part of the arena repository.
