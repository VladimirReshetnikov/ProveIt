# PA194 equality-theory axiom rule

`finiteEqTheoryDelta` is a specific explicit Δ₁ presentation of Foundation's actual `Theory.eqAxiom` for the function-free binary relational source language. Its characteristic formula is the finite disjunction of the five quoted source equality axioms. `finiteEqTheory_class` proves, for every candidate-PRA/IΣ₁ model and every model-valued p, that this instance's actual Foundation `Theory.Δ₁Class` equals the previously checked `finiteEqAxiomCode` predicate. No such identification is asserted for arbitrary alternative Δ₁ presentations.

`simRuleVerum` proves the exact concrete `ConPA.Sequent.Sim.ruleVerum` conclusion, with numerical `Quant`, numerical negated `Tr`, and bot 1, for any model-valued environment. `simRuleEqAxiom` proves the exact `Sim.ruleAxm` conclusion for the selected equality theory and any model-valued environment e and source code p in its Δ₁ class, assuming `simBase e + p ≤ simReserve e`; the eventual admissibility invariant must supply that bound. `negatedTranslation_any` identifies the four decoded environment fields for all model-valued e. `finiteEqTheory_axiom_sseq` also directly supplies the corresponding finite-set sequent leaf.

These results do not construct a `Sim`, prove a common admissibility invariant, compile any source derivation, cover the other axioms of a PA/set-theory interpretation, or establish a consistency implication. The current upstream `ConPASequent`, `ConPASetSequent`, and `ConPADerivation` sources are included and rebuilt in this retained-overlay same-output replay, which audits ten reports and is not an empty-overlay build.

Run `bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-logic/check-sim-axiom.sh --out DIR` with matching retained prerequisites.
