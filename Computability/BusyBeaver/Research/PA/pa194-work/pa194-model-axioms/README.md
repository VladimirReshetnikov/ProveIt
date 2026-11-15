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
(`simRuleWeakAdjunction`). The first two modules are about the calculus only. No simulation is
constructed, the source theory with this axiom is not defined as a `Theory`, and nothing here
yields a consistency implication.

## Modules

| Module | Content |
| --- | --- |
| `PA194ModelNeighborhoodWitness` | `primitiveToNeighborhood_target`: the primitive equality `eqValue a b` entails the observational equality `neighborhoodValue a b z` at every label `z ≠ a, b`. `pa194-model-logic` has this under the premise that the primitive equality is vacuous at `z` (`targetEq_to_neighborhood_of_vacuity`), which the calculus cannot supply in general. Here the premise is discharged at the code of the equality itself by the diagonal axiom, and the bound label is then moved to `z` (`transferBinder_target`). Consequences: `neighborhoodWitness_target` (`∃x x ≈ c`), `universalInstance_target` (`∀x P → r` from `x ≈ y → P → r` and vacuity of `r` at `x`), and the four existential introductions for observational equality of `pa194-model-logic` without their vacuity premise (`targetExistsNeighborhoodLeft`, `…Right`, and the two negated forms; the premise is replaced by `z ≠ c`). |
| `PA194ModelWeakAdjunction` | `weakAdjunctionAtName_target`: for pairwise distinct labels `a, b, c, m` and a reserved label `z ≠ b, c, m`, the calculus proves `∃c ((∀m (m ∈ a → m ∈ c)) ∧ b ∈ c)`. The gate is used at the code of the theorem `∀q ⊤`; the bound member label is renamed by reverse rewriting and the output label by instantiation along observational equality. `weakAdjunction_supplier` is the universally closed form with the labels `lo, …, lo+3` and the source encoding of the implication. |
| `PA194ModelWeakAdjunctionAxiom` | `sourceWeakAdjunction`, the sentence `∀a ∀b ∃c ((∀m (m ∈ a → m ∈ c)) ∧ b ∈ c)` of the relational source language, with the implication written as a disjunction. `weakAdjRoot_quote`: its model-valued quote is an explicit code. `fixedFormulaTranslation_weakAdjRoot`: the fixed formula translation of that code, for arbitrary bound and free stacks, is the code of `weakAdjunction_supplier` with the binder labels `base, …, base+3` (by the constructor equations of `pa194-model-logic` and `fixedTranslation_membershipBound`, a membership atom on two bound variables). `fixedFormulaTranslation_weakAdjunction_target`: the translation is target-provable when the reserved label differs from `base+1`, `base+2`, `base+3`. `simRuleWeakAdjunction`: `(¬ tr e ⌜σ⌝) → 1` under every environment `e` with `base+3 < reserve`. |

The sentence has the shape of `M6.PA.RelationalSource.weakAdjunctionFormula`
(`pa194-source-separation`), which is a formula over the free-variable type `ℕ`; that the two
agree under the embedding of sentences is not proved here.

## What is open

- A `Theory` of the relational source language that contains this sentence with a `Δ₁`
  presentation, and the classifier that reduces the axiom field of a simulation to one leaf
  per axiom (as `finiteEqTheory_class` does for the equality axioms).
- The separation scheme for an internal, possibly nonstandard formula, and the remaining
  fixed axioms.

## Checking

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check.sh
```

runs [`check_bridge.py`](../pa194-model-fairness/check_bridge.py) with each module as the top
module, passing its arguments on (for example `--out DIR` to reuse compiled objects). On
2026-11-14 the modules were compiled directly with `lean` against objects of the standalone
modules they import. The script itself has not been run.
