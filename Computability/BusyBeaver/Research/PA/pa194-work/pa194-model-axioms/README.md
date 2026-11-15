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
(`simRuleAdjunctiveAxiom`). The separation scheme is done instance by instance: for every
internal formula `φ` of arity one, possibly nonstandard and with free variables, the fixed
formula translation of the instance `sepRoot φ` is target-provable, and the axiom leaf
follows (`simRuleSeparation`). No theory containing the instances is defined yet. The empty
set and irreflexivity of membership are done as fixed sentences, and `fixedSetTheory` (the
equality axioms, weak adjunction, the empty set, irreflexivity) has a `Δ₁` presentation and
a discharged axiom field (`simRuleFixedSetAxiom`).
`PA194ModelNeighborhoodWitness`, `PA194ModelWeakAdjunction` and `PA194ModelSeparation` are
about the calculus only. No simulation is constructed, and nothing here yields a consistency
implication.

## Modules

| Module | Content |
| --- | --- |
| `PA194ModelNeighborhoodWitness` | `primitiveToNeighborhood_target`: the primitive equality `eqValue a b` entails the observational equality `neighborhoodValue a b z` at every label `z ≠ a, b`. `pa194-model-logic` has this under the premise that the primitive equality is vacuous at `z` (`targetEq_to_neighborhood_of_vacuity`), which the calculus cannot supply in general. Here the premise is discharged at the code of the equality itself by the diagonal axiom, and the bound label is then moved to `z` (`transferBinder_target`). Consequences: `neighborhoodWitness_target` (`∃x x ≈ c`), `universalInstance_target` (`∀x P → r` from `x ≈ y → P → r` and vacuity of `r` at `x`), and the four existential introductions for observational equality of `pa194-model-logic` without their vacuity premise (`targetExistsNeighborhoodLeft`, `…Right`, and the two negated forms; the premise is replaced by `z ≠ c`). |
| `PA194ModelWeakAdjunction` | `weakAdjunctionAtName_target`: for pairwise distinct labels `a, b, c, m` and a reserved label `z ≠ b, c, m`, the calculus proves `∃c ((∀m (m ∈ a → m ∈ c)) ∧ b ∈ c)`. The gate is used at the code of the theorem `∀q ⊤`; the bound member label is renamed by reverse rewriting and the output label by instantiation along observational equality. `weakAdjunction_supplier` is the universally closed form with the labels `lo, …, lo+3` and the source encoding of the implication. |
| `PA194ModelWeakAdjunctionAxiom` | `sourceWeakAdjunction`, the sentence `∀a ∀b ∃c ((∀m (m ∈ a → m ∈ c)) ∧ b ∈ c)` of the relational source language, with the implication written as a disjunction. `weakAdjRoot_quote`: its model-valued quote is an explicit code. `fixedFormulaTranslation_weakAdjRoot`: the fixed formula translation of that code, for arbitrary bound and free stacks, is the code of `weakAdjunction_supplier` with the binder labels `base, …, base+3` (by the constructor equations of `pa194-model-logic` and `fixedTranslation_membershipBound`, a membership atom on two bound variables). `fixedFormulaTranslation_weakAdjunction_target`: the translation is target-provable when the reserved label differs from `base+1`, `base+2`, `base+3`. `simRuleWeakAdjunction`: `(¬ tr e ⌜σ⌝) → 1` under every environment `e` with `base+3 < reserve`. |
| `PA194ModelAdjunctiveTheory` | `adjunctiveTheory`: the five equality axioms of `Theory.eqAxiom` and `sourceWeakAdjunction` (`adjunctiveTheory_eq`), with the `Δ₁` presentation `adjunctiveTheoryDelta` (a disjunction of six equations). `adjunctiveTheory_class`: in a model, the internal axiom class is "one of the five quoted equality axioms or the quoted weak-adjunction sentence". `simRuleAdjunctiveAxiom`: the axiom field of a simulation for this theory, `Pr (tr e p → 1)` for every internal axiom `p`, under the reserve bound `base + p ≤ reserve` that `pa194-model-logic` uses for the equality axioms (`four_le_weakAdjRoot` shows that the bound covers the four binder labels of weak adjunction). |
| `PA194ModelSeparation` | `separationAtName_target`: for a property value `P` of the model, labels `c ≠ a, b`, a reserved label `z ≠ b, c` and a label `q` above `a, b, c, z`, the calculus proves `∃c ∀b (b ∈ c ↔ (b ∈ a ∧ P))` when `P` is vacuous (`P → ∀x P` is target-provable) at `c`, at `q` and at the code `d` of `∀q (b ∈ a ∧ P)`. The gate is used at `d` (`rawSeparation_target`); as a formula `d` is equivalent to `b ∈ a ∧ P` because the quantifier is vacuous (`universalSelf_target`), and `d` is above every label in play. The output label is then renamed from `d` to `c` along observational equality (`separationRenameOutput_target`). This is the model-level port of `separationAtName` of `pa194-source-separation`, with the syntactic conditions "the label does not occur in the property" replaced by provable vacuity. |
| `PA194ModelLowVacuity` | `lowVacuity_all_codes`: the fixed translation of an internal formula `p` of arity `n` (`IsSemiformula n p`, possibly nonstandard) is vacuous at a label `x` below the next binder label, when the first `n` entries of the bound stack and the entries of the free stack up to index `p` differ from `x`, and `x` is not the reserved label. `generalVacuity_all_codes` of `pa194-model-logic` covers labels above the allocation range; this is the complementary case, needed for the output label of separation, which is a binder allocated before the property. The proof is the same internal `𝚺₁` structural induction with the arity carried along (`allocatedBound_low`: after `k` binders the first `k` stack entries are allocated labels and the next `n` are the initial ones). |
| `PA194ModelSeparationAxiom` | `sepRoot φ`, the code of `∀a ∃c ∀b ((b ∉ c ∨ (b ∈ a ∧ φ)) ∧ ((b ∉ a ∨ ¬φ) ∨ b ∈ c))` for an internal formula code `φ`, with Foundation's internal negation. `φ` is placed under the three binders unchanged: a formula of arity one mentions only the innermost bound variable, and its code does not depend on the binders around it, so no internal substitution is needed. `fixedFormulaTranslation_sepRoot`: the translation for arbitrary stacks. `fixedFormulaTranslation_separation_target`: it is target-provable when `IsSemiformula 1 φ`, the free stack does not contain `base+1` up to index `φ`, and the reserved label differs from `base+1` and `base+2`. The three vacuity hypotheses of `separationAtName_target` come from `lowVacuity_all_codes` and `generalVacuity_all_codes`, and the negated property from `translationDual_all_codes`. `simRuleSeparation`: the axiom leaf `(¬ tr e (sepRoot φ)) → 1`. |
| `PA194ModelEmptyIrreflexive` | `irreflexivity_target`: `∀x ¬(x ∈ x)` for an arbitrary bound label; at the label `0` the membership `0 ∈ 0` is the code of falsum, and the bound label is moved to `x` by `transferBinder_target`. `emptySetAtName_target`: `∃c ∀b ¬(b ∈ c)` for `c ≠ b`, from `separationAtName_target` with the property falsum and auxiliary labels chosen above `b, c`. `sourceIrreflexivity`, `sourceEmptySet` with their model-valued quotes, their translations for arbitrary stacks, target-provability with no condition on the reserved label, and the axiom leaves `simRuleIrreflexivity`, `simRuleEmptySet`. |
| `PA194ModelFixedSetTheory` | `fixedSetTheory`: the five equality axioms, `sourceWeakAdjunction`, `sourceEmptySet`, `sourceIrreflexivity` (`fixedSetTheory_eq`: it is `adjunctiveTheory` with the two new sentences), with the `Δ₁` presentation `fixedSetTheoryDelta` (a disjunction of eight equations), the internal axiom class in a model (`fixedSetTheory_class`), and the axiom field of a simulation under `base + p ≤ reserve` (`simRuleFixedSetAxiom`). |

The weak-adjunction sentence has the shape of `M6.PA.RelationalSource.weakAdjunctionFormula`
(`pa194-source-separation`), which is a formula over the free-variable type `ℕ`; that the two
agree under the embedding of sentences is not proved here.

## What is open

- A source theory whose internal axiom class contains the separation instances, with its
  axiom rule. The obstacle is the parameters. `simRuleSeparation` allows free variables in
  `φ` (under a hypothesis on the free stack: no entry up to index `φ` is the label
  `base+1`), but a Foundation theory is a set of sentences, and `Theory.Δ₁.mem_iff` lets
  the class accept a standard formula only if it is a sentence of the theory. So an
  instance with parameters has to be an axiom in universally closed form, `∀…∀ (instance)`.
  Under the closure the parameters are bound variables with indices `3, 4, …` inside the
  property (the indices `1` and `2` are the output set and the given set), so the property
  is no longer a formula of arity one used unchanged: it is a formula of arity `m+1`
  shifted past two binders. The leaf then needs either the translation of a formula under
  such a renaming of bound variables, or the relation between a body with bound parameters
  and the open instance with free parameters. The second relation is also what the
  universal rule of a simulation is about (`pa194-model-logic` has its quantifier rules
  for atoms only). The class restricted to closed `φ`
  (`IsSemiformula 1 φ ∧ shift φ = φ ∧ p = sepRoot φ`) is covered by the leaf as it stands,
  but the standard development uses separation with parameters (for example
  `intersectionAxiomSupplier`), so no theory with only the closed instances is defined
  here.
- `sepRoot φ` is not compared with `separationFormula` of `pa194-source-separation`, which
  lifts the property by a rewriting map instead of using its code unchanged.
- Intersection (`intersectionAxiomSupplier` of the standard development) is an instance of
  separation with a parameter, so it waits for the item above. `sourceEmptySet` and
  `sourceIrreflexivity` have the shapes of `emptyFormula` and `irFormula` of the standard
  development; that they agree under the embedding of sentences is not proved here.
- The other fields of a simulation for `adjunctiveTheory` are those of `pa194-model-logic`;
  the quantifier rules are not complete there.

## Checking

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check.sh
```

runs [`check_bridge.py`](../pa194-model-fairness/check_bridge.py) with each module as the top
module, passing its arguments on (for example `--out DIR` to reuse compiled objects). On
2026-11-14 and 2026-11-15 the modules were compiled directly with `lean` against objects of
the standalone modules they import. The script itself has not been run.
