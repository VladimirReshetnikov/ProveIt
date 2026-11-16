import DiophantineConsistency.PRASubPredZero
import DiophantineConsistency.IPRAFullGGTransfer
import DiophantineConsistency.IPRAZeroStepNative
import DiophantineConsistency.IPRATheoryInstantiation
import IPRABridge.FoundationNormalization
import IPRABridge.OrderSymbols

set_option autoImplicit false
noncomputable section

namespace DiophantineConsistency.IPRASubPredZeroNative

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic LeanProofs.ConciseIPRA.Fm
open PRAFiniteFunctionCodes PRALanguage PRATheory PRASubPredZero
open IPRANativeTheory IPRABridge
open LeanProofs.ConciseIPRA (Fm PTm PR Prf PRAAx)
open LeanProofs.ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA (congrPred monus_succ)

def eqA : Semisentence language 2 := .rel .eq ![leftTerm, zeroTerm]
def eqB : Semisentence language 2 := .rel .eq ![rightTerm, zeroTerm]
def matrix : Semisentence language 2 := eqA 🡒 eqB
def result : Sentenceᵢ language := ∀⁰ ∀⁰ ((.rel .eq ![leftTerm,zeroTerm]) 🡒 (.rel .eq ![rightTerm,zeroTerm]))

theorem transfer : nativeTheory ⊢ (∀⁰ ∀⁰ matrix)ᴺ :=
  IPRAFullGGTransfer.from_classical (by simpa [sentence, matrix, eqA, eqB] using proved)

private abbrev left : PTm 2 := translatedApp subCode ![PTm.var 1, succ (PTm.var 0)]
private abbrev right : PTm 2 :=
  translatedApp predCode ![translatedApp subCode ![PTm.var 1, PTm.var 0]]

private theorem conciseImplication : Prf PRAAx ([] : List (Fm PTm 2)) ((left ≐ zero) ⟶ (right ≐ zero)) := by
  apply Prf.impI
  let x : PTm 2 := PTm.var 1
  let y : PTm 2 := PTm.var 0
  have h : Prf PRAAx [left ≐ zero] (left ≐ right) := (translated_subCode x (succ y)).eqTrans
    ((monus_succ x y).eqTrans
      ((congrPred (translated_subCode x y).eqSymm).eqTrans
        (translated_predCode _).eqSymm))
  exact h.eqSymm.eqTrans Prf.hyp0

private theorem mapPair {α β : Type} (f : α → β) (a b : α) :
    (fun i : Fin 2 => f (![a, b] i)) = ![f a, f b] := by
  funext i
  fin_cases i <;> rfl

private theorem nullaryApp {n : ℕ} (c : PR 0) (args : Fin 0 → PTm n) :
    PTm.app c args = PTm.app c Fin.elim0 := by
  rw [Subsingleton.elim args (Fin.elim0 : Fin 0 → PTm n)]

private theorem image :
    toConciseSentence result = Fm.all (Fm.all ((left ≐ zero) ⟶ (right ≐ zero))) := by
  simp only [result, toConciseSentence, toConciseClosed, IPRAOrderErasure.erase,
    IPRAOrderErasure.termsToReference, leftTerm, rightTerm, zeroTerm, Semiterm.lMap_func,
    Semiterm.lMap_bvar, Function.comp_def, mapPair, Matrix.cons_val_zero, Matrix.cons_val_one,
    toConciseFormula, toConciseTerm, left, right, translatedApp, PTm.zero, PTm.succ, nullaryApp]
  congr 5
  funext i
  fin_cases i
  rfl

def native : nativeTheory ⊢! result := by
  apply Nonempty.some
  apply (IPRAStandardTheory.provable_iff result).mp
  apply (standardProvable_iff result).mpr
  rw [image]
  exact .allI (.allI conciseImplication)

theorem native_provable : nativeTheory ⊢ result := ⟨native⟩

end DiophantineConsistency.IPRASubPredZeroNative
