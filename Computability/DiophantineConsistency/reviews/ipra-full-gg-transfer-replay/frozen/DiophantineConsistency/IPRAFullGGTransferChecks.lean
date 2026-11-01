import DiophantineConsistency.IPRAFullGGTransfer
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open DiophantineConsistency DiophantineConsistency.PRALanguage
open DiophantineConsistency.PRATheory DiophantineConsistency.IPRANativeTheory
open DiophantineConsistency.IPRAFullGGTransfer
#check equality_images
#check axiom_images
#check from_classical
#check mapped_noZero_comparison
#print axioms equality_images
#print axioms axiom_images
#print axioms from_classical
#print axioms mapped_noZero_comparison
example {σ : Sentence language} (h : PRA ⊢ σ) : nativeTheory ⊢ σᴺ := from_classical h
