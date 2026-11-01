import DiophantineConsistency.IPRANativeOpenDecidable
set_option autoImplicit false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open DiophantineConsistency.PRALanguage DiophantineConsistency.IPRANativeTheory
open DiophantineConsistency.IPRATheoryHilbertBridge DiophantineConsistency.IPRANativeFormula
open DiophantineConsistency.IPRANativeOpenDecidable
example (φ : Proposition language) (h : φ.Open) : extended nativeTheory ⊢! native φ ⋎ ∼native φ := openDecidable φ h
example (φ : Proposition language) (h : φ.Open) : extended nativeTheory ⊢! ∼∼native φ 🡒 native φ := openStable φ h
#print axioms openDecidable
#print axioms openStable
#print axioms orderDecidable
