import DiophantineConsistency.IPRABinaryRelationGG
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open DiophantineConsistency DiophantineConsistency.PRALanguage
open DiophantineConsistency.IPRANativeTheory DiophantineConsistency.IPRABinaryRelationGG
#check relExt_image
#print axioms relExt_image
example : nativeTheory ⊢ (Theory.Eq.relExt Language.ORing.Rel.eq)ᴺ := relExt_image Language.ORing.Rel.eq
example : nativeTheory ⊢ (Theory.Eq.relExt Language.ORing.Rel.lt)ᴺ := relExt_image Language.ORing.Rel.lt
