import DiophantineConsistency.PRASubSuccSelfNonzero
import IPRABridge.FoundationNormalization
import IPRABridge.OrderSymbols

/-! Reuse the shared iPRA strict-order proof for the reduction's exact
subtraction formula. -/

set_option autoImplicit false

namespace DiophantineConsistency.IPRASubSuccSelfNonzero

open LO LO.FirstOrder LeanProofs.ConciseIPRA
open scoped LO.FirstOrder Fm
open PRALanguage (language)
open PRATheory (subCode)
open IPRANativeTheory (nativeTheory)
open IPRABridge
open LeanProofs.ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA (neg not_succ_le_self)
open Syn (var)

def result : Sentenceᵢ language :=
  ∀⁰ ∼(Semiformulaᵢ.rel .eq ![PRASubSuccSelfNonzero.term, PRASubSuccSelfNonzero.zero])

private theorem conciseNonzero :
    ([] : List (Fm PTm 1)) ⊢[PRAAx] neg (translatedApp subCode ![succ (var 0), var 0] ≐ zero) := by
  apply Prf.impI
  exact not_succ_le_self (var 0) _ (((translated_subCode _ _).eqSymm).eqTrans Prf.hyp0)

private theorem image :
    toConciseSentence result =
      Fm.all (neg (translatedApp subCode ![succ (var 0), var 0] ≐ zero)) := by
  simp only [result, toConciseSentence, toConciseClosed, Semiformulaᵢ.neg_def,
    IPRAOrderErasure.erase, IPRAOrderErasure.termsToReference,
    PRASubSuccSelfNonzero.term, PRASubSuccSelfNonzero.zero, Semiterm.lMap_func,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    toConciseFormula, toConciseTerm, toConciseCode, neg]
  congr 4 <;> funext i <;> fin_cases i <;> rfl

theorem native : nativeTheory ⊢ result := by
  apply (IPRAStandardTheory.provable_iff result).mp
  apply (standardProvable_iff result).mpr
  rw [image]
  exact .allI conciseNonzero

end DiophantineConsistency.IPRASubSuccSelfNonzero
