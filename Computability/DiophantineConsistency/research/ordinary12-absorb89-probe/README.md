# Speculative first-root absorption

`Absorb89Graph.lean` defines a draft by absorbing the direct graph's `+s` into the witness r. Its checked commutative-ring lemmas compare all three residuals under the forward assignment `rPrime=r+s`. The external digest-pinned DAG check in `check-dag.py` finds 89 live operations: 50 multiplications, 22 additions and 17 subtractions. Its observation is in `observations/dag-attempt01/`. A later [existence-equivalence join](EQUIVALENCE.md) establishes both model-level directions at bounded ports, and a [fixed-port join](HALT.md) relates the 89 graph's positive, shifted and byte-port forms to the machine's internal halt predicate. The [iPRA endpoint](../ordinary12-absorb89-ipra-join/README.md) now has an independently audited author build with the stated provider limits. Formal PDF binding remains separate.

`Absorb89First.lean` proves an actual draft output zero implies its first residual zero and exact scaled first norm in every IΣ₁ model, for arbitrary natural ports and without positivity. `Absorb89FirstQuotient.lean` adds a positive first root and its Pell equation assuming `J*beta>0`. Both theorem statements include the exact expressions. These are graph-specific first-factor results, not the missing reverse transformation.

The [sign theorem](SIGNS.md) now binds the positive and negative root branches
to an actual graph zero and proves its transport term positive. The
[divisibility theorem](DIVISIBILITY.md) establishes `b ∣ Bt` in either branch.
The [reflection theorem](REFLECTION.md) constructs a negative-branch witness
above `s` satisfying the positive first-root equation. A separate
[model reflection](../../reviews/ordinary12-absorb89-reflection-independent/README.md)
proves that this negative-branch replacement preserves the entire graph zero.
A separate [growth lemma](GROWTH.md)
proves the positive-branch bound `3*s≤k` if a first-Pell coordinate has index
at least 3. A subsequent [six-stage index chain](INDEX_CHAIN.md) proves that
an actual graph zero has such an index, in fact at least 13, under the stated
fixed-port bounds. The [positive-branch theorem](POSITIVE_BRANCH.md) joins
these results and derives the required witness bound. The separate
[existence-equivalence join](EQUIVALENCE.md) combines both branches with the
forward and inverse witness maps. Subsequent fixed-port and adapter joins now
establish the iPRA endpoint subject to the recorded provider limits.

The guarded graph, first and quotient attempts all exited 0 without reported warnings. The first-norm source locally suppresses unused-variable and unused-simp-argument linters; those classes were not checked. Source/object SHA-256 pairs are:

* Graph: `c74d9a6798e29aa77e93cb075983b91f46cb08cd92de4022a0f7fab02d85f4e0` / `819843dbc8412f1b65691912b820d4816afa47bc6bd54b65c3ed7c3ad59a0692`.
* First norm: `58b0564191303e71923d33e625ec3de4dff9fa780ae794318ba940ccaacd65b4` / `dccd2052e7bae80d731d316da559c842dfc00b393682fa6476c7bdc84ea5b2a8`.
* First quotient: `e9149e3110a434c2f494ce896f00357ce527cf8b133255ce4796b96a3b7eb149` / `b722b9eb6881e6c278a78b432f7ee9b69de1218455d328b94e8af2c4e98c59e6`.

The runners pin direct producer objects and the selected 1,291-object union; exact pins, logs, and resource samples are retained in `observations/`. Package, dynamic, and source-to-object ancestry remain inherited rather than freshly rebuilt; temporary paths may disappear. The separate `../ordinary12-direct-main-probe/PLUSBRANCH.md` and `REFLECT.md` contain the generic conditional sign lemmas used by these graph-specific results.
