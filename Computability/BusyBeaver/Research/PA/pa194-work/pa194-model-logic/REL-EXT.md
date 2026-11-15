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

These initial identities concern standard typed source syntax. The later
model-valued reference result below connects the quoted axiom to the target
supplier. This does not establish arbitrary source-axiom compilation, PA proof
transport, physical-machine simulation or either consistency implication. The
retained-overlay source replay is not an empty-overlay build; this checker audits
eight theorem reports.

Run `bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-logic/check-rel-ext.sh --out DIR` with matching retained prerequisites.

`PA194ModelRelExtSource` defines `relExtRoot` by source-code constructors in an arbitrary model of candidate PRA and IΣ₁. `relExtRoot_quote` proves it is exactly the model-valued quote of Foundation's actual typed `Theory.Eq.relExt Relation.mem`, using the source language equality instance selected in `PA194RelExtTypedTranslation`. Its four universal binders contain negative equality atoms at de Bruijn pairs (0,2) and (1,3), a negative membership atom at (0,1), and a positive membership atom at (2,3), combined in the exact Foundation NNF shape. `relExtRoot_valid` proves the model-valued code satisfies `IsUFormula` for the source language; this includes nonstandard models, although the source axiom itself is a fixed standard formula.

`PA194ModelRelExtBudget` shows that a reserved label `z` at least four successors above `lo` is fresh for the four consecutive labels, and derives the closed target numerical-calculus supplier under that single hypothesis. The later reference result below proves the first of these connections. This budget lemma alone does not show that the source-proof compiler establishes the bound, or that any arbitrary source axiom or proof is translated. It does not establish either consistency implication. The checker is a retained-overlay same-output replay, not an empty-overlay build; it recompiles sources in this directory and audits five axiom reports.

Run `bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-logic/check-rel-ext-source.sh --out DIR` with matching retained prerequisites for the model-valued quote and budget audit.

`PA194ModelRelExtReference` proves `fixedFormulaTranslation_relExt_target`: in every candidate-PRA model satisfying IΣ₁, for arbitrary model-valued initial and free stacks, initial label `base`, and reserved label `reserve`, the actual numerical target calculus proves `fixedFormulaTranslation` applied to the model-valued quote of Foundation's typed `Theory.Eq.relExt Relation.mem`, provided `((((base+1)+1)+1)+1) ≤ reserve`.

The proof identifies the quoted fixed source axiom with a valid explicit internal source-code tree, evaluates the independent Σ₁ formula recursor at that tree in arbitrary models, computes the four bound-stack lookups and four label allocations, and matches the resulting NNF expression to the existing fixed-size target supplier. `relExtRoot_four_le` and `relExtRoot_budget_shape` prove that the root source-code budget admits the four binder steps in every such model. The translation equation itself assumes no freshness; the stated reserve inequality is needed for the target proof supplier. Neither this theorem nor the finite target proof is an internal arbitrary-source-proof compiler, a PA proof transport, a physical-machine simulation, or a consistency implication. The theorem applies to this particular standard source axiom quoted into each model; it does not cover arbitrary nonstandard axiom codes. The checker uses a retained overlay and recompiles all locally resolved modules, so it is not an empty-overlay build. It audits ten axiom reports.

Run `bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-logic/check-rel-ext-reference.sh --out DIR` with matching retained prerequisites.

`fixedFormulaTranslation_relExt_target_rootBound` applies the concrete Foundation membership `Eq.relExt` translation result under the stronger compiler-style assumption `base + quotedSourceCode ≤ reserve`; this implies the four-label freshness inequality because the root source code is at least four in every candidate PRA/IΣ₁ model. The conclusion and limitations are exactly those of `fixedFormulaTranslation_relExt_target`: this fixed source axiom has a target proof, with arbitrary initial and free stacks; no general compiler or consistency implication follows. This retained-overlay same-output replay recompiles local sources and audits three reports.

