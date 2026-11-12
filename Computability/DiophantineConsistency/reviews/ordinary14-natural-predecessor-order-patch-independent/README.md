# Independent review: inert predecessor-order alternatives

The [patch packet](../../research/ordinary14-natural-predecessor-order-patch/README.md) records the identified successor-order issue accurately and provides appropriate source-only alternatives. The original and independent receipts reproduce. Neither packet resolves the actual Lean declaration, checks tactics or compiles the alternatives.

The inspected Mathlib `ExistsAddOfLE` declaration has the orientation `a<=b → ∃ c, b=a+c`; the sampled Foundation natural-model instance supplies that class. Thus, when the intended declaration is used with `a=1`, the obtained equation has form `v=1+c`. The source definitions of `Natural81JShift.Related` and `Natural82Model.HasThreePredecessors` instead require `v=c+1`. The original natural81 source uses `simpa [w]` at this conversion, so its success depends on elaborator/simplifier behavior. The original natural82 source passes the three obtained equalities directly to `exact` in the other orientation; this appears a generic-type mismatch under the inspected declaration, but no Lean failure has been observed.

The independent checker pins the originals, the two `.lean.src` alternatives, the Mathlib declaration, a Foundation instance source, a repository example using `add_comm`, and the natural81 lexical endpoint inventory. An independent line diff confirms exactly one explicit `add_comm` addition in the natural81 alternative, and three explicit `by simpa [add_comm]` conversions in the natural82 alternative, with all other bytes unchanged. The inventory still points to the original `.lean` sources, not these inert `.lean.src` alternatives. Commutativity is the mathematically appropriate conversion; the 101 finite natural controls in the receipt do not replace Lean checking.

Selecting either alternative for a future proof requires explicit materialization and corresponding updated dependency snapshots and provider checks. This review does not prove name resolution, tactic success, source compatibility, an axiom closure or an iPRA endpoint. The separately updated natural80 gamma-shift source is outside this patch and is not changed here.

Run from the repository root while the pinned Mathlib checkout and Foundation snapshot remain available:

```sh
python3 -I -S -B Computability/DiophantineConsistency/reviews/ordinary14-natural-predecessor-order-patch-independent/check.py | cmp - Computability/DiophantineConsistency/reviews/ordinary14-natural-predecessor-order-patch-independent/result.json
```
