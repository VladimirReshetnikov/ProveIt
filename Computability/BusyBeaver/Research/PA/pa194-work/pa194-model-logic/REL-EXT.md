# PA194 relation extensionality translation

With a local `Language.Eq` instance selecting the source relation `.eq`,
`sourceRelExt` is Foundation's actual `Theory.Eq.relExt Relation.mem` formula.
For every natural initial label `lo`, `relExt_toNamed` proves its actual typed
`toNamed` translation equals the displayed four-universal NNF named formula;
`relExt_numeric_expanded` further proves that the existing PA194 `relationalCode`
of that translation equals the explicit numeric expression `expectedNumeric`.
These standard typed syntax identities use `propext` and do not use `sorryAx`.

Independently, in every candidate-PRA model with IΣ₁,
`neighborhoodBothCongruence_target` proves two-position membership substitution
from two neighborhood equalities; `sourceAtom_binaryRelationSubstitution` gives
the corresponding statement for actual equality/membership atom decoders.
`relExtNNFBody_target` and `relExtNNF_supplier` prove the same displayed NNF shape
and its four-universal closure in the target numerical calculus, for arbitrary
model-valued consecutive labels under the four explicit reserved-label
inequalities. The latter proofs are fixed-size target proof recipes, including
nonstandard labels.

The two sides have *not yet been identified inside arbitrary models*: no theorem
here says that the internal `formulaReference` or `fixedFormulaTranslation` applied
to the quoted Foundation axiom yields the target supplier expression. The code
identities concern standard typed source syntax only. This is not arbitrary
source-axiom compilation, PA proof transport, physical-machine simulation or either
consistency implication. The retained-overlay same-output source replay is not an
empty-overlay build. The checker audits all eight displayed theorem reports.

Run `bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-logic/check-rel-ext.sh --out DIR` with matching retained prerequisites.

`PA194ModelRelExtSource` defines `relExtRoot` by source-code constructors in an arbitrary model of candidate PRA and IΣ₁. `relExtRoot_quote` proves it is exactly the model-valued quote of Foundation's actual typed `Theory.Eq.relExt Relation.mem`, using the source language equality instance selected in `PA194RelExtTypedTranslation`. Its four universal binders contain negative equality atoms at de Bruijn pairs (0,2) and (1,3), a negative membership atom at (0,1), and a positive membership atom at (2,3), combined in the exact Foundation NNF shape. `relExtRoot_valid` proves the model-valued code satisfies `IsUFormula` for the source language; this includes nonstandard models, although the source axiom itself is a fixed standard formula.

`PA194ModelRelExtBudget` shows that a reserved label `z` at least four successors above `lo` is fresh for the four consecutive labels, and derives the closed target numerical-calculus supplier under that single hypothesis. This does not prove that `formulaReference` on the quoted source code gives the supplier's expression, that the source-proof compiler establishes the bound, or that any arbitrary source axiom or proof is translated. It does not establish either consistency implication. The checker is a retained-overlay same-output replay, not an empty-overlay build; it recompiles sources in this directory and audits five axiom reports.

Run `bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-logic/check-rel-ext-source.sh --out DIR` with matching retained prerequisites for the model-valued quote and budget audit.
