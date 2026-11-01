import DiophantineConsistency.PRAEqualityCode
import DiophantineConsistency.IPRAFullGGTransfer
import DiophantineConsistency.IPRATheoryInstantiation
import Foundation.Meta.IntProver
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRANativeSubSelf
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRATheory DiophantineConsistency.PRAFiniteFunctionCodes
open DiophantineConsistency.PRAAddOne DiophantineConsistency.PRAEqualityCode

def subSelfSentence : Sentence language := equalClosure (n := 1)
  (applyCode subCode ![#0,#0]) (applyCode (.zero 0) Fin.elim0)

theorem classicalSubSelf : PRA ⊢ subSelfSentence := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  apply (eqClosureModels _ _).mpr
  intro e
  have hz : (fun i : Fin 0 => Semiterm.val e Empty.elim (Fin.elim0 i : TermN 1)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  simpa [subSelfSentence, applyCode, Semiterm.val_func, Semiterm.val_bvar,
    Function.comp_def, Matrix.fun_eq_vec_two, hz] using modelSubSelf (M := M) (e 0)
theorem translatedSubSelf : DiophantineConsistency.IPRANativeTheory.nativeTheory ⊢ subSelfSentenceᴺ :=
  DiophantineConsistency.IPRAFullGGTransfer.from_classical classicalSubSelf
open DiophantineConsistency.IPRANativeTheory DiophantineConsistency.IPRANativeInduction
open DiophantineConsistency.IPRATheoryHilbertBridge DiophantineConsistency.IPRATheoryInstantiation
open Rewriting HilbertProofᵢ
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance
local instance : Entailment.Int (extended nativeTheory) where
  efq := HilbertProofᵢ.eaxm (Or.inl (by simp [Hilbertᵢ.Intuitionistic]))

def zeroEq : Semisentenceᵢ language 1 := .rel .eq ![#0, zeroTerm 1]
def zeroDec : Semisentenceᵢ language 1 := zeroEq ⋎ ∼zeroEq
def zeroDecSentence : Sentenceᵢ language := ∀⁰ zeroDec
def subSelfBody : Semisentenceᵢ language 1 :=
  .rel .eq ![.func subCode ![#0,#0], zeroTerm 1]
def nativeSubSelfSentence : Sentenceᵢ language := ∀⁰ subSelfBody

def nativeSubSelf (hz : nativeTheory ⊢! zeroDecSentence) : nativeTheory ⊢! nativeSubSelfSentence := by
  have hgg : nativeTheory ⊢! ∀⁰ (∼∼subSelfBody) := by
    have h := Classical.choice translatedSubSelf
    exact h
  let x : Term language ℕ := &0
  let z : Term language ℕ := .func (.zero 0) Fin.elim0
  let t : Term language ℕ := .func subCode ![x,x]
  let e : Propositionᵢ language := .rel .eq ![t,z]
  have hnn := instantiateTheory (T := nativeTheory) (∼∼subSelfBody) hgg ![x]
  have hdec := instantiateTheory (T := nativeTheory) zeroDec hz ![t]
  have hv1 : (fun i : Fin 2 => Rew.embSubsts ![x] (![.func subCode ![#0,#0], zeroTerm 1] i)) = ![t,z] := by
    funext i
    cases i using Fin.cases with
    | zero => simp [t, Rew.func, Function.comp_def]; funext k; cases k using Fin.cases with
      | zero => simp
      | succ j => cases j using Fin.cases with
        | zero => simp
        | succ j => exact Fin.elim0 j
    | succ j => cases j using Fin.cases with
      | zero => simp [z, zeroTerm, Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
      | succ j => exact Fin.elim0 j
  have hv2 : (fun i : Fin 2 => Rew.embSubsts ![t] (![#0, zeroTerm 1] i)) = ![t,z] := by
    funext i
    cases i using Fin.cases with
    | zero => simp
    | succ j => cases j using Fin.cases with
      | zero => simp [z, zeroTerm, Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
      | succ j => exact Fin.elim0 j
  have he : extended nativeTheory ⊢! ∼∼e := by
    simpa [subSelfBody, e, Semiformulaᵢ.rewAux, Semiformulaᵢ.rew_rel, Function.comp_def, hv1] using hnn
  have hd : extended nativeTheory ⊢! e ⋎ ∼e := by
    simpa [zeroDec, zeroEq, e, Semiformulaᵢ.rewAux, Semiformulaᵢ.rew_rel, Function.comp_def, hv2] using hdec
  have hst : extended nativeTheory ⊢! (e ⋎ ∼e) 🡒 (∼∼e 🡒 e) := by
    apply Classical.choice
    change extended nativeTheory ⊢ _
    int_prover
  have hp := hst ⨀ hd ⨀ he
  apply extendedToTheory nativeTheory
  simp only [nativeSubSelfSentence, Rewriting.app_all, Rew.q_emb]
  apply HilbertProofᵢ.gen
  change extended nativeTheory ⊢! _
  have hv3 : (fun i : Fin 2 => Rew.free (Rew.emb (![.func subCode ![#0,#0], zeroTerm 1] i))) = ![t,z] := by
    funext i
    cases i using Fin.cases with
    | zero => simp [t, x, Rew.func, Function.comp_def]; funext k; cases k using Fin.cases with
      | zero => simp
      | succ j => cases j using Fin.cases with
        | zero => simp
        | succ j => exact Fin.elim0 j
    | succ j => cases j using Fin.cases with
      | zero => simp [z, zeroTerm, Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
      | succ j => exact Fin.elim0 j
  simpa [subSelfBody, e, Semiformulaᵢ.rewAux, Semiformulaᵢ.rew_rel, Function.comp_def, hv3] using hp
end DiophantineConsistency.IPRANativeSubSelf
