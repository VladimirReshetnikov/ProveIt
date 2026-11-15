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
