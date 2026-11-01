import DiophantineConsistency.IPRAEqualityTransGG
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open DiophantineConsistency DiophantineConsistency.PRALanguage
open DiophantineConsistency.IPRANativeTheory DiophantineConsistency.IPRAEqualityTransGG
#check trans_closed_context
#check trans_native
#check trans_image
#print axioms trans_closed_context
#print axioms trans_native
#print axioms trans_image
example : nativeTheory ⊢ (Theory.Eq.trans language)ᴺ := trans_image
