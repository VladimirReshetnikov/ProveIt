import DiophantineConsistency.IPRANativeAxiomImage
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder
open DiophantineConsistency DiophantineConsistency.PRATheory
open DiophantineConsistency.IPRANativeTheory DiophantineConsistency.IPRANativeAxiomImage
#check native_axiom
#check succNonzero_image
#print axioms native_axiom
#print axioms succNonzero_image
example : nativeTheory ⊢ succNonzeroᴺ := succNonzero_image
