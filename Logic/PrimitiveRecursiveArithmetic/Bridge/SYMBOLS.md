# Foundation and ConciseIPRA arithmetic symbols

The [bridge](README.md) maps the existing Foundation construction codes to
ordinary ConciseIPRA. In the table, “object equality” refers to a derivation
in `Prf PRAAx Γ` at arbitrary terms in the common finite scope. “Syntax”
means the translated terms agree in Lean before deriving their reflexivity.
The [arithmetic comparisons](Lean/IPRABridge/ArithmeticSymbols.lean),
[order comparisons](Lean/IPRABridge/OrderSymbols.lean),
[comparison bits](Lean/IPRABridge/ComparisonBits.lean), and
[bounded search](Lean/IPRABridge/BoundedSearch.lean) are separately importable.

| Foundation name | Arity and argument convention | Concise counterpart | Checked relation |
| --- | --- | --- | --- |
| `Code.zero 0` | Nullary | `PTm.zero` | Syntax. The positive-arity zero codes translate as compositions with empty argument families. Their defining equations prove equality to the nullary zero. |
| `Code.succ` | Unary | `PTm.succ` | Syntax. |
| `PRALanguage.oneCode` | Nullary, successor applied to zero | `PTm.succ PTm.zero` | Object equality, `translated_oneCode`. |
| `PRALanguage.addCore` | Binary, recursion on the first argument | `LeanProofs.IPRA.Sym.add` | The function symbols agree by `toConcise_addCore`. |
| `PRALanguage.addCode` | Binary, feeds the second argument into the core's recursion slot | `a + b` | Object equality, `translated_addCode`, using commutativity. `translated_addCode_left_cancel` reuses the shared proof at this exact symbol. |
| `PRALanguage.mulCore` | Binary, recursion on the first argument | `a * b` | Object equality, `translated_mulCore`, using defining equations and open induction. |
| `PRALanguage.mulCode` | Binary, feeds the second argument into the core's recursion slot | `a * b` | Object equality, `translated_mulCode`, using commutativity. |
| `PRATheory.predCode` | Unary, predecessor with `pred 0 = 0` | `LeanProofs.IPRA.PTm.pred` | Object equality, `translated_predCode`. |
| `PRATheory.subCore` | Binary, recursion on the subtrahend first | `b ∸ a` | Object equality, `translated_subCore`. Keep the reversed argument order. |
| `PRATheory.subCode` | Binary, minuend first | `a ∸ b` | Object equality, `translated_subCode`. |
| `PRATheory.ltBitCode` | Binary, nonzero test of `b ∸ a` | `LeanProofs.IPRA.lt a b`, meaning `S a ∸ b = 0` | Provable biconditional for the comparison bit equal to `oneCode`, `translated_ltBitCode`. The module also checks strictness at zero and at equal arguments. |
| `PRAIsZero.isZeroCode` | Unary. Returns `oneCode` at zero and zero at successors. | `LeanProofs.IPRA.eqb a PTm.zero` | Object equality, `translated_isZeroCode`. `IPRANotBit.notBitConvention` uses it after composing the code with an arbitrary PR function. |
| `PRABoundedSearchCode.searchCode good` | Bound first, then any finite family of parameters. Recurses on the bound and returns the first zero of `good` strictly below it, or the bound when no such zero exists. | `Search.Finite.mu (translatedSearchBody good) N xs` | Object equality at arbitrary terms, `translatedSearch_eq`. `translatedSearch_found` supplies the original Foundation witness at `IPRABoundedSelector.selectorOpen`. |

The translated order comparison uses the exact code which erases the native
`<` relation. At a Foundation call site, compose it with the checked
order-erasure biconditional. Foundation codes retain their original names
in machine and equation statements. The shared proof can then be used at
the terms and hypotheses already present.

The zero-test comparison gives the original bit-complement theorem in the
extended native theory, for arbitrary Foundation term assignments. The
bounded-child proof uses it both for the free witness and for the selector's
assigned witness.

The bounded-search comparison covers `N = 0` and the failed-search result.
It follows the original Foundation recursion and the portable least-witness
invariant, including the case where a previous witness must be retained.

## Coding interfaces used by the current clients

| Client operation | Existing contract | Comparison status |
| --- | --- | --- |
| C222 and C254 tag and payload | A positive code has the form `raw + 1`, with tag `raw % 12` and payload `raw / 12`. Both represented graphs use Foundation's `remDef` and `divDef` at divisor `12` over the ambient model. Code zero yields invalid output zero. | [`Core.Division`](../Derivations/Lean/IPRADerivations/Core/Division.lean) proves quotient and remainder uniqueness at positive divisors. A common zero-divisor convention has yet to be checked across these interfaces. |
| C222 and C254 pairing | `ArithmeticCantor.cantor a b = triangle (a + b) + b`, with represented projections `firstDef` and `secondDef`. | The portable [`pairT`](../Derivations/Lean/IPRADerivations/Core/Pairing.lean) uses `(a + b)² + a`. The two codes give `1` and `2` at `(1, 0)`, respectively. A comparison would require a separate translation between encodings. |
| C222 and C254 histories | Sequence reads and appends use the same Foundation HFS code, with the representation evaluated at arbitrary model inputs. | The portable bounded search packs a finite family of Lean-scoped terms. A model-internal HFS sequence translation has its own encoding and theorem obligations. |
