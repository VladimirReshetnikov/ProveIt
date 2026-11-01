import DiophantineConsistency.IPRAOpenAtomDecision
set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open DiophantineConsistency.PRALanguage DiophantineConsistency.IPRANativeTheory
open DiophantineConsistency.IPRATheoryHilbertBridge DiophantineConsistency.IPRANativeFormula
open DiophantineConsistency.IPRAOpenAtomDecision
example (φ : Proposition language) (h : AtomDecisions φ) :
    extended nativeTheory ⊢! native φ ⋎ ∼native φ := decision φ h
example (φ : Proposition language) (h : AtomDecisions φ) :
    extended nativeTheory ⊢! φᴺ 🡒 native φ := backward φ h
#print axioms decision
#print axioms backward
