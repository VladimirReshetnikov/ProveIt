# Foundation and ConciseIPRA arithmetic symbols

The [bridge](README.md) maps the existing Foundation construction codes to
ordinary ConciseIPRA. In the table, “object equality” refers to a derivation
in `Prf PRAAx Γ` at arbitrary terms in the common finite scope. “Syntax”
means the translated terms agree in Lean before deriving their reflexivity.
The [arithmetic comparisons](Lean/IPRABridge/ArithmeticSymbols.lean) and
[order comparisons](Lean/IPRABridge/OrderSymbols.lean) are separately
importable.

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

The translated order comparison uses the exact code which erases the native
`<` relation. At a Foundation call site, compose it with the checked
order-erasure biconditional. Foundation codes retain their original names
in machine and equation statements. The shared proof can then be used at
the terms and hypotheses already present.

Further code families to compare at their first migrated uses include
division and remainder, bounded search, pairing, sequence coding, and
finite sums/products. Record output conventions at zero and the empty or
failed-search case before using a comparison in a reduction.
