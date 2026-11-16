import DiophantineConsistency.PRAAddOne
import DiophantineConsistency.IPRANativeInduction
import IPRABridge.FoundationNormalization
import IPRABridge.OrderSymbols

/-! The native induction step uses the ordinary iPRA successor identity. -/

set_option autoImplicit false

namespace DiophantineConsistency.IPRAAddOneTransfer

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LeanProofs.ConciseIPRA.Fm
open PRALanguage PRATheory IPRANativeTheory IPRANativeInduction
open IPRABridge
open LeanProofs.ConciseIPRA (Fm PTm PR Prf PRAAx)
open LeanProofs.IPRA (congrAdd neg succ_eq_add_one)

def succTerm : TermN 1 := applyCode .succ (fun _ => #0)
def addOneNN : Sentenceᵢ language := ∀⁰ (∼∼(.rel .eq ![stepTerm 0, succTerm]))

private abbrev addition : PTm 1 :=
  translatedApp addCode ![PTm.var 0, translatedApp oneCode Fin.elim0]

private theorem conciseAddOne {Γ : List (Fm PTm 1)} :
    Prf PRAAx Γ (addition ≐ PTm.succ (PTm.var 0)) :=
  (translated_addCode _ _).eqTrans
    ((congrAdd (.eqRefl _) translated_oneCode).eqTrans (succ_eq_add_one _).eqSymm)

private theorem mapPair {α β : Type} (f : α → β) (a b : α) :
    (fun i : Fin 2 => f (![a, b] i)) = ![f a, f b] := by
  funext i
  fin_cases i <;> rfl

private theorem nullaryApp {n : ℕ} (c : PR 0) (args : Fin 0 → PTm n) :
    PTm.app c args = PTm.app c Fin.elim0 := by
  rw [Subsingleton.elim args (Fin.elim0 : Fin 0 → PTm n)]

private theorem image :
    toConciseSentence addOneNN = Fm.all (neg (neg (addition ≐ PTm.succ (PTm.var 0)))) := by
  simp only [addOneNN, toConciseSentence, toConciseClosed, Semiformulaᵢ.neg_def,
    IPRAOrderErasure.erase, IPRAOrderErasure.termsToReference, stepTerm, succTerm, applyCode,
    Semiterm.lMap_func, Semiterm.lMap_bvar, Function.comp_def, mapPair,
    Matrix.cons_val_zero, Matrix.cons_val_one, toConciseFormula, toConciseTerm,
    addition, translatedApp, PTm.succ, neg, nullaryApp, LeanProofs.ConciseIPRA.Syn.up_zero]
  rfl

theorem transfer : nativeTheory ⊢ addOneNN := by
  apply (IPRAStandardTheory.provable_iff addOneNN).mp
  apply (standardProvable_iff addOneNN).mpr
  rw [image]
  exact .allI (.impI (.impE Prf.hyp0 conciseAddOne))

end DiophantineConsistency.IPRAAddOneTransfer
