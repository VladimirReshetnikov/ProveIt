import DiophantineConsistency.IPRARelationGGLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder
open DiophantineConsistency DiophantineConsistency.PRALanguage
open DiophantineConsistency.IPRANativeTheory DiophantineConsistency.IPRARelationGGLogic
#check nnConj
#check atomic_relation_closure
#check binary_relExt_adapter
#print axioms nnConj
#print axioms atomic_relation_closure
#print axioms binary_relExt_adapter
example (r : language.Rel 2) : nativeTheory ⊢ relCongruenceI r 🡒 (Theory.Eq.relExt r)ᴺ :=
  binary_relExt_adapter r
