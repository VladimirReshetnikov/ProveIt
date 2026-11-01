import DiophantineConsistency.IPRANativeBasicImages
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder
open DiophantineConsistency DiophantineConsistency.PRALanguage
open DiophantineConsistency.PRATheory DiophantineConsistency.IPRANativeTheory
open DiophantineConsistency.IPRANativeBasicImages
#check succInjective_image
#check orderDefinition_image
#check basicAxiom_image
#print axioms succInjective_image
#print axioms orderDefinition_image
#print axioms basicAxiom_image
example : nativeTheory ⊢ succNonzeroᴺ := basicAxiom_image BasicAxiom.succNonzero
example : nativeTheory ⊢ succInjectiveᴺ := basicAxiom_image BasicAxiom.succInjective
example : nativeTheory ⊢ orderDefinitionᴺ := basicAxiom_image BasicAxiom.orderDefinition
