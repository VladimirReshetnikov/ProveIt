import DiophantineConsistency.IPRAErasedEqualityImages

/-! Exploratory syntax for the erased successor-injectivity axiom. -/
set_option autoImplicit false
namespace DiophantineConsistency.IPRAErasedSuccessorShape
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open IPRAOrderErasure IPRAErasedDefiningImages

def injectivity : Sentenceᵢ IPRAEqualityOnlyReference.language :=
  ∀⁰* ((Semiformulaᵢ.rel IPRAEqualityOnlyReference.EqualityRel.eq
      ![IPRAEqualityOnlyReference.applyCode .succ (fun _ => #0),
        IPRAEqualityOnlyReference.applyCode .succ (fun _ => #1)]) 🡒
    (Semiformulaᵢ.rel IPRAEqualityOnlyReference.EqualityRel.eq ![#0, #1]) :
      Semisentenceᵢ IPRAEqualityOnlyReference.language 2)

theorem erase_successorInjectivity :
    erase IPRANativeTheory.succInjectiveI = injectivity := by
  simp only [IPRANativeTheory.succInjectiveI, injectivity, erase_allClosure, erase]
  congr 3
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [PRATheory.applyCode, IPRAEqualityOnlyReference.applyCode,
      Semiterm.lMap_func, termsToReference, Function.comp_def]
  · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    simp [PRATheory.applyCode, IPRAEqualityOnlyReference.applyCode,
      Semiterm.lMap_func, termsToReference, Function.comp_def]
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    rfl

end DiophantineConsistency.IPRAErasedSuccessorShape
