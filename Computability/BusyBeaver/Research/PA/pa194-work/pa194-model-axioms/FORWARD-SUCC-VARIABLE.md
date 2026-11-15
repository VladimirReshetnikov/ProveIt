# Source normalization of the value of a successor variable

`PA194ForwardSuccVariable.lean` uses the actual typed PAeq forward translation `PA194ForwardTyped.value` on the term `succ (.bvar 0)` with the bound variable interpreted as source variable x and the result as source variable z. In the natural-deduction source calculus, under an explicit `FormulaEquality` context, it proves both directions between this translated value and `domain(x) ∧ domain(z) ∧ successor(x,z)`. The proof opens the translated existential witness, transports domain and successor along its equality with x, and constructs the reverse witness using reflexivity.

The theorem is for standard source variable indices and standard typed syntax. Equality assumptions are explicit and the result has not yet been closed as a source theorem or applied to arbitrary internal formula/proof codes. In particular it is a concrete term-value component of the successor-substitution bridge, not a proof of that bridge, translated PA induction, an iPRA theorem, or machine correctness.

Run `bash check-forward-succ-variable.sh REPO NEW_OUTPUT`. The new source is rebuilt into a fresh output against pinned prebuilt dependencies, including the unified typed forward translator and source formula congruence; the full transitive source closure is not rebuilt. A successful run reports four axiom audits without `sorryAx`.
