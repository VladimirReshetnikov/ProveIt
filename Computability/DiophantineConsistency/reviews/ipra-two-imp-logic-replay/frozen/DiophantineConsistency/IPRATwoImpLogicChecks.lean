import DiophantineConsistency.IPRATwoImpLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder
open DiophantineConsistency DiophantineConsistency.PRALanguage
open DiophantineConsistency.PRATheory DiophantineConsistency.IPRANativeTheory
open DiophantineConsistency.IPRATwoImpLogic
#check twoImp_dni
#check atomic_twoImp_closure
#print axioms twoImp_dni
#print axioms atomic_twoImp_closure
example {n : ℕ} (a b c : TermN n) : nativeTheory ⊢
  (∀⁰* ((Semiformulaᵢ.rel Language.ORing.Rel.eq ![a,b]) 🡒
    (Semiformulaᵢ.rel Language.ORing.Rel.eq ![b,c]) 🡒 Semiformulaᵢ.rel Language.ORing.Rel.eq ![a,c])) 🡒
  (∀⁰* ((Semiformula.rel Language.ORing.Rel.eq ![a,b]) 🡒
    (Semiformula.rel Language.ORing.Rel.eq ![b,c]) 🡒 Semiformula.rel Language.ORing.Rel.eq ![a,c]))ᴺ :=
  atomic_twoImp_closure Language.ORing.Rel.eq Language.ORing.Rel.eq Language.ORing.Rel.eq _ _ _
