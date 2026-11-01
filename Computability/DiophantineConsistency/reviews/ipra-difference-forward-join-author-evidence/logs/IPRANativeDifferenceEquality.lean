import DiophantineConsistency.IPRANativeAtomStability
import DiophantineConsistency.IPRANativeOpenDecision
/-! Equality decidability from zero decidability and explicit native two-difference correctness. Neither correctness direction is assumed proved. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRANativeDifferenceEquality
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRATheory DiophantineConsistency.PRAFiniteFunctionCodes
open DiophantineConsistency.IPRANativeTheory DiophantineConsistency.IPRANativeInduction
open DiophantineConsistency.IPRATheoryHilbertBridge DiophantineConsistency.IPRATheoryInstantiation
open DiophantineConsistency.IPRANativeAtomStability DiophantineConsistency.IPRANativeOpenDecision
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

/-- The same native zero-decidability sentence used by `IPRAZeroDecidable`. -/
def zeroEq : Semisentenceᵢ language 1 := .rel .eq ![#0, zeroTerm 1]
def zeroDec : Semisentenceᵢ language 1 := zeroEq ⋎ ∼zeroEq
def zeroDecSentence : Sentenceᵢ language := ∀⁰ zeroDec

def diff1 : Semisentenceᵢ language 2 := Semiformulaᵢ.rel .eq ![.func subCode ![#0,#1], zeroTerm 2]
def diff2 : Semisentenceᵢ language 2 := Semiformulaᵢ.rel .eq ![.func subCode ![#1,#0], zeroTerm 2]
def forwardSentence : Sentenceᵢ language := ∀⁰* (eqMatrix 🡒 (diff1 ⋏ diff2))
def backwardSentence : Sentenceᵢ language := ∀⁰* ((diff1 ⋏ diff2) 🡒 eqMatrix)
def zeroOpen (t : Term language ℕ) : Propositionᵢ language := eqAt t (.func (.zero 0) Fin.elim0)

def zeroDecOpen (hz : nativeTheory ⊢! zeroDecSentence) (t : Term language ℕ) :
    extended nativeTheory ⊢! zeroOpen t ⋎ ∼zeroOpen t := by
  have hp := instantiateTheory (T := nativeTheory) zeroDec hz ![t]
  have hv : (fun i : Fin 2 => Rew.embSubsts ![t] (![#0, zeroTerm 1] i)) = ![t, .func (.zero 0) Fin.elim0] := by
    funext i
    cases i using Fin.cases with
    | zero => simp
    | succ j => cases j using Fin.cases with
      | zero =>
        simp [zeroTerm, Rew.func, Function.comp_def]
        funext k
        exact Fin.elim0 k
      | succ j => exact Fin.elim0 j
  simpa [zeroDec, zeroEq, zeroOpen, eqAt, Semiformulaᵢ.rewAux,
    Semiformulaᵢ.rew_rel, Function.comp_def, hv] using hp

def forwardOpen (hf : nativeTheory ⊢! forwardSentence) (x y : Term language ℕ) :
    extended nativeTheory ⊢! eqAt x y 🡒
      (zeroOpen (.func subCode ![x,y]) ⋏ zeroOpen (.func subCode ![y,x])) := by
  have hp := instantiateTheory (T := nativeTheory) (eqMatrix 🡒 (diff1 ⋏ diff2)) hf ![x,y]
  have he : (fun i : Fin 2 => Rew.embSubsts ![x,y] (![#0,#1] i)) = ![x,y] := by
    funext i
    cases i using Fin.cases with
    | zero => simp
    | succ j => cases j using Fin.cases with
      | zero => simp
      | succ j => exact Fin.elim0 j
  have heswap : (fun i : Fin 2 => Rew.embSubsts ![x,y] (![#1,#0] i)) = ![y,x] := by
    funext i
    cases i using Fin.cases with
    | zero => simp
    | succ j => cases j using Fin.cases with
      | zero => simp
      | succ j => exact Fin.elim0 j
  have hf1 : (fun i : Fin 2 => Rew.embSubsts ![x,y] (![.func subCode ![#0,#1], zeroTerm 2] i)) =
      ![.func subCode ![x,y], .func (.zero 0) Fin.elim0] := by
    funext i
    cases i using Fin.cases with
    | zero => simp [Rew.func, Function.comp_def, he]
    | succ j => cases j using Fin.cases with
      | zero => simp [zeroTerm, Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
      | succ j => exact Fin.elim0 j
  have hf2 : (fun i : Fin 2 => Rew.embSubsts ![x,y] (![.func subCode ![#1,#0], zeroTerm 2] i)) =
      ![.func subCode ![y,x], .func (.zero 0) Fin.elim0] := by
    funext i
    cases i using Fin.cases with
    | zero => simp [Rew.func, Function.comp_def, heswap]
    | succ j => cases j using Fin.cases with
      | zero => simp [zeroTerm, Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
      | succ j => exact Fin.elim0 j
  simpa [eqMatrix, diff1, diff2, zeroOpen, eqAt, Semiformulaᵢ.rewAux,
    Semiformulaᵢ.rew_rel, Function.comp_def, he, hf1, hf2] using hp

def backwardOpen (hf : nativeTheory ⊢! backwardSentence) (x y : Term language ℕ) :
    extended nativeTheory ⊢! (zeroOpen (.func subCode ![x,y]) ⋏ zeroOpen (.func subCode ![y,x])) 🡒 eqAt x y := by
  have hp := instantiateTheory (T := nativeTheory) ((diff1 ⋏ diff2) 🡒 eqMatrix) hf ![x,y]
  have he : (fun i : Fin 2 => Rew.embSubsts ![x,y] (![#0,#1] i)) = ![x,y] := by
    funext i
    cases i using Fin.cases with
    | zero => simp
    | succ j => cases j using Fin.cases with
      | zero => simp
      | succ j => exact Fin.elim0 j
  have heswap : (fun i : Fin 2 => Rew.embSubsts ![x,y] (![#1,#0] i)) = ![y,x] := by
    funext i
    cases i using Fin.cases with
    | zero => simp
    | succ j => cases j using Fin.cases with
      | zero => simp
      | succ j => exact Fin.elim0 j
  have hf1 : (fun i : Fin 2 => Rew.embSubsts ![x,y] (![.func subCode ![#0,#1], zeroTerm 2] i)) =
      ![.func subCode ![x,y], .func (.zero 0) Fin.elim0] := by
    funext i
    cases i using Fin.cases with
    | zero => simp [Rew.func, Function.comp_def, he]
    | succ j => cases j using Fin.cases with
      | zero => simp [zeroTerm, Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
      | succ j => exact Fin.elim0 j
  have hf2 : (fun i : Fin 2 => Rew.embSubsts ![x,y] (![.func subCode ![#1,#0], zeroTerm 2] i)) =
      ![.func subCode ![y,x], .func (.zero 0) Fin.elim0] := by
    funext i
    cases i using Fin.cases with
    | zero => simp [Rew.func, Function.comp_def, heswap]
    | succ j => cases j using Fin.cases with
      | zero => simp [zeroTerm, Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
      | succ j => exact Fin.elim0 j
  simpa [eqMatrix, diff1, diff2, zeroOpen, eqAt, Semiformulaᵢ.rewAux,
    Semiformulaᵢ.rew_rel, Function.comp_def, he, hf1, hf2] using hp

def equalityOpen (hz : nativeTheory ⊢! zeroDecSentence)
    (hf : nativeTheory ⊢! forwardSentence) (hb : nativeTheory ⊢! backwardSentence)
    (x y : Term language ℕ) : extended nativeTheory ⊢! eqAt x y ⋎ ∼eqAt x y := by
  let a := zeroOpen (.func subCode ![x,y])
  let b := zeroOpen (.func subCode ![y,x])
  have hd : extended nativeTheory ⊢! (a ⋏ b) ⋎ ∼(a ⋏ b) :=
    decAnd a b ⨀ zeroDecOpen hz (.func subCode ![x,y]) ⨀ zeroDecOpen hz (.func subCode ![y,x])
  exact Entailment.of_C_of_C_of_A
    (Entailment.C_trans (backwardOpen hb x y) Entailment.or₁)
    (Entailment.C_trans (Entailment.contra (forwardOpen hf x y)) Entailment.or₂) hd

def equalityDecidable (hz : nativeTheory ⊢! zeroDecSentence)
    (hf : nativeTheory ⊢! forwardSentence) (hb : nativeTheory ⊢! backwardSentence) :
    nativeTheory ⊢! eqDecSentence := by
  have ho := equalityOpen hz hf hb (&0) (&1)
  apply extendedToTheory nativeTheory
  simp only [eqDecSentence, allClosure_succ, allClosure_zero]
  apply HilbertProofᵢ.gen
  apply HilbertProofᵢ.gen
  change extended nativeTheory ⊢! _
  have hv : (fun i : Fin 2 => Rew.free (Rew.free (Rew.emb ((![#0,#1] : Fin 2 → Semiterm language Empty 2) i)))) = ![&0, &1] := by
    funext i
    cases i using Fin.cases with
    | zero =>
      change Rew.free (Rew.free (#(0 : Fin 2) : Semiterm language ℕ 2)) = &0
      rw [Rew.free_bvar_castSucc_zero, Rew.free_bvar_last_zero]
    | succ j => cases j using Fin.cases with
      | zero =>
        change Rew.free (Rew.free (#(Fin.last 1) : Semiterm language ℕ 2)) = &1
        rw [Rew.free_bvar_last, Rew.free_fvar]
      | succ j => exact Fin.elim0 j
  simpa [eqMatrix, eqAt, Semiformulaᵢ.neg_def, Semiformulaᵢ.rewAux, Semiformulaᵢ.rew_rel,
    Rewriting.free, Function.comp_def, hv] using ho
end DiophantineConsistency.IPRANativeDifferenceEquality
