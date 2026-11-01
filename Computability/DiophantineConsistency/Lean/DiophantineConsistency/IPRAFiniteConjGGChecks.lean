import DiophantineConsistency.IPRAFiniteConjGG
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder
open DiophantineConsistency DiophantineConsistency.PRALanguage
open DiophantineConsistency.IPRANativeTheory DiophantineConsistency.IPRAFiniteConjGG
#check ggFiniteConj
#check finite_atomic_imp_closure
#check functionCongruence_adapter
#print axioms ggFiniteConj
#print axioms functionCongruence_adapter
example {k : ℕ} (f : language.Func k) : nativeTheory ⊢
    functionCongruenceI f 🡒 (Theory.Eq.funcExt f)ᴺ := functionCongruence_adapter f
example (f : language.Func 0) : nativeTheory ⊢
    functionCongruenceI f 🡒 (Theory.Eq.funcExt f)ᴺ := functionCongruence_adapter f
