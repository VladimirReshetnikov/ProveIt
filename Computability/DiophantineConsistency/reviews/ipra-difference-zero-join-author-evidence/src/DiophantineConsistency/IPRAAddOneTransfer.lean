import DiophantineConsistency.IPRAFullGGTransfer
import DiophantineConsistency.PRAAddOne
set_option autoImplicit false
namespace DiophantineConsistency.IPRAAddOneTransfer
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open PRALanguage PRATheory PRAAddOne IPRANativeTheory IPRANativeInduction

def succTerm : TermN 1 := applyCode .succ (fun _ => #0)
def addOneNN : Sentenceᵢ language := ∀⁰ (∼∼(.rel .eq ![stepTerm 0, succTerm]))
theorem transfer : nativeTheory ⊢ addOneNN := by
  have h := IPRAFullGGTransfer.from_classical PRA_proves_addOne
  convert h using 1
  simp [addOneNN, addOneSentence, equalClosure, stepTerm, succTerm, applyCode,
    Semiformula.doubleNegation, allClosure_succ]
  congr 3
  funext i
  cases i using Fin.cases with
  | zero =>
    simp only [Matrix.cons_val_zero]
    congr 1
    funext k
    cases k using Fin.cases with
    | zero => rfl
    | succ k =>
      cases k using Fin.cases with
      | zero => rfl
      | succ k => exact Fin.elim0 k
  | succ j =>
    cases j using Fin.cases with
    | zero => rfl
    | succ j => exact Fin.elim0 j
end DiophantineConsistency.IPRAAddOneTransfer
