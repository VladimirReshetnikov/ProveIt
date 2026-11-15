# Source axioms in the numerical calculus, at model level

The direction `¬Halt(M₁₉₄) → Con(PA)` compiles an internal derivation of a source theory into
the numerical calculus ([`pa194-model-sequent`](../pa194-model-sequent/README.md),
[`pa194-model-logic`](../pa194-model-logic/README.md)). Every axiom of the source theory then
needs a target proof of its translation, inside a candidate-PRA model `M` whose arithmetic
reduct satisfies `𝗜𝚺₁`, for labels that may be nonstandard. `pa194-model-logic` has these
proofs for the five equality axioms. This directory is for the other axioms of the
relational source theory; their standard-number versions are in
[`pa194-source-separation`](../pa194-source-separation/README.md).

**Status.** Weak adjunction is done: the fixed formula translation of the quoted sentence is
target-provable for arbitrary stacks and labels with the reserved label above the four binder
labels, and the corresponding axiom leaf of a simulation follows
(`simRuleWeakAdjunction`). `adjunctiveTheory`, the equality axioms together with weak
adjunction, has a `Δ₁` presentation, and the axiom field of a simulation is discharged for it
(`simRuleAdjunctiveAxiom`). The first two modules are about the calculus only. No simulation
is constructed, and nothing here yields a consistency implication.

## Modules

| Module | Content |
| --- | --- |
| `PA194ModelNeighborhoodWitness` | `primitiveToNeighborhood_target`: the primitive equality `eqValue a b` entails the observational equality `neighborhoodValue a b z` at every label `z ≠ a, b`. `pa194-model-logic` has this under the premise that the primitive equality is vacuous at `z` (`targetEq_to_neighborhood_of_vacuity`), which the calculus cannot supply in general. Here the premise is discharged at the code of the equality itself by the diagonal axiom, and the bound label is then moved to `z` (`transferBinder_target`). Consequences: `neighborhoodWitness_target` (`∃x x ≈ c`), `universalInstance_target` (`∀x P → r` from `x ≈ y → P → r` and vacuity of `r` at `x`), and the four existential introductions for observational equality of `pa194-model-logic` without their vacuity premise (`targetExistsNeighborhoodLeft`, `…Right`, and the two negated forms; the premise is replaced by `z ≠ c`). |
| `PA194ModelWeakAdjunction` | `weakAdjunctionAtName_target`: for pairwise distinct labels `a, b, c, m` and a reserved label `z ≠ b, c, m`, the calculus proves `∃c ((∀m (m ∈ a → m ∈ c)) ∧ b ∈ c)`. The gate is used at the code of the theorem `∀q ⊤`; the bound member label is renamed by reverse rewriting and the output label by instantiation along observational equality. `weakAdjunction_supplier` is the universally closed form with the labels `lo, …, lo+3` and the source encoding of the implication. |
| `PA194ModelWeakAdjunctionAxiom` | `sourceWeakAdjunction`, the sentence `∀a ∀b ∃c ((∀m (m ∈ a → m ∈ c)) ∧ b ∈ c)` of the relational source language, with the implication written as a disjunction. `weakAdjRoot_quote`: its model-valued quote is an explicit code. `fixedFormulaTranslation_weakAdjRoot`: the fixed formula translation of that code, for arbitrary bound and free stacks, is the code of `weakAdjunction_supplier` with the binder labels `base, …, base+3` (by the constructor equations of `pa194-model-logic` and `fixedTranslation_membershipBound`, a membership atom on two bound variables). `fixedFormulaTranslation_weakAdjunction_target`: the translation is target-provable when the reserved label differs from `base+1`, `base+2`, `base+3`. `simRuleWeakAdjunction`: `(¬ tr e ⌜σ⌝) → 1` under every environment `e` with `base+3 < reserve`. |
| `PA194ModelAdjunctiveTheory` | `adjunctiveTheory`: the five equality axioms of `Theory.eqAxiom` and `sourceWeakAdjunction` (`adjunctiveTheory_eq`), with the `Δ₁` presentation `adjunctiveTheoryDelta` (a disjunction of six equations). `adjunctiveTheory_class`: in a model, the internal axiom class is "one of the five quoted equality axioms or the quoted weak-adjunction sentence". `simRuleAdjunctiveAxiom`: the axiom field of a simulation for this theory, `Pr (tr e p → 1)` for every internal axiom `p`, under the reserve bound `base + p ≤ reserve` that `pa194-model-logic` uses for the equality axioms (`four_le_weakAdjRoot` shows that the bound covers the four binder labels of weak adjunction). |

The sentence has the shape of `M6.PA.RelationalSource.weakAdjunctionFormula`
(`pa194-source-separation`), which is a formula over the free-variable type `ℕ`; that the two
agree under the embedding of sentences is not proved here.

## What is open

- The separation scheme for an internal, possibly nonstandard formula. It is a scheme, so
  its axiom class is not a finite disjunction and its leaf has to be uniform in the formula.
- The remaining fixed axioms of the standard development (empty set, intersection,
  irreflexivity), by the recipe used here for weak adjunction.
- The other fields of a simulation for `adjunctiveTheory` are those of `pa194-model-logic`;
  the quantifier rules are not complete there.

## Checking

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check.sh
```

runs [`check_bridge.py`](../pa194-model-fairness/check_bridge.py) with each module as the top
module, passing its arguments on (for example `--out DIR` to reuse compiled objects). On
2026-11-14 the modules were compiled directly with `lean` against objects of the standalone
modules they import. The script itself has not been run.
