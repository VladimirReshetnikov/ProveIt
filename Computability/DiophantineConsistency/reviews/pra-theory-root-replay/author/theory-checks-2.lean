import DiophantineConsistency.PRATheory

set_option autoImplicit false
namespace DiophantineConsistency.PRATheoryChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory
local instance : Structure language ℕ := natStructure

example (n : ℕ) : zeroEquation n ∈ PRA := Or.inl (Or.inl (Or.inr (.zero n)))
example {m n : ℕ} (f : Code m) (g : Codes n m) :
    compositionEquation f g ∈ PRA := Or.inl (Or.inl (Or.inr (.composition f g)))
example {n : ℕ} (f : Code n) (g : Code (n+2)) :
    recursionStepEquation f g ∈ PRA := Or.inl (Or.inl (Or.inr (.recursionStep f g)))
example (φ : Semiformula language ℕ 1) (h : φ.Open) :
    (succInd φ).univCl ∈ PRA := Or.inl (Or.inr ⟨φ, h, rfl⟩)
example {n : ℕ} (c : Code n) : Theory.Eq.funcExt (L := language) c ∈ PRA :=
  Or.inl (Or.inl (Or.inl (Theory.eqAxiom.funcExt (L := language) c)))
example : succNonzero ∈ PRA := Or.inr .succNonzero
example : succInjective ∈ PRA := Or.inr .succInjective
example : orderDefinition ∈ PRA := Or.inr .orderDefinition
example : ℕ↓[language] ⊧* PRA := nat_models_PRA

#print axioms compositionEquation_valid
#print axioms recursionStepEquation_valid
#print axioms nat_models_succInd
#print axioms eval_ltBitCode
#print axioms orderDefinition_valid
#print axioms nat_models_PRA
end DiophantineConsistency.PRATheoryChecks
