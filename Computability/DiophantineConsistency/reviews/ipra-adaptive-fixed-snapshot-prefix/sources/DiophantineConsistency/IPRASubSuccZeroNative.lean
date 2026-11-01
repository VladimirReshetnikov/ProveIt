import DiophantineConsistency.PRASubSuccZero
import DiophantineConsistency.IPRAFullGGTransfer
import DiophantineConsistency.IPRAZeroStepNative
import DiophantineConsistency.IPRATheoryInstantiation
import Foundation.Meta.IntProver
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRASubSuccZeroNative
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRASubSuccZero
open IPRANativeTheory IPRANativeInduction IPRATheoryHilbertBridge IPRATheoryInstantiation
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

def eqA : Semisentence language 2 := .rel .eq ![leftTerm, zeroTerm]
def eqB : Semisentence language 2 := .rel .eq ![rightTerm, zeroTerm]
def matrix : Semisentence language 2 := eqA 🡒 eqB
def result : Sentenceᵢ language := ∀⁰ ∀⁰ ((.rel .eq ![leftTerm,zeroTerm]) 🡒 (.rel .eq ![rightTerm,zeroTerm]))

theorem transfer : nativeTheory ⊢ (∀⁰ ∀⁰ matrix)ᴺ :=
  IPRAFullGGTransfer.from_classical (by simpa [sentence, matrix, eqA, eqB] using proved)

def native : nativeTheory ⊢! result := by
  have hgg : nativeTheory ⊢! ∀⁰* matrixᴺ := by
    have h := Classical.choice transfer
    simpa [allClosure_succ, Semiformula.doubleNegation] using h
  let x : Term language ℕ := &1
  let y : Term language ℕ := &0
  let z : Term language ℕ := .func (.zero 0) Fin.elim0
  let a : Proposition language := .rel .eq ![.func subCode ![.func .succ (fun _ => x),y],z]
  let b : Proposition language := .rel .eq ![.func subCode ![x,y],z]
  let bi : Propositionᵢ language := .rel .eq ![.func subCode ![x,y],z]
  have hh := instantiateTheory (T := nativeTheory) matrixᴺ hgg ![y,x]
  have ha : Rew.embSubsts ![y,x] ▹ eqA = a := by
    simp [a, eqA, leftTerm, PRASubSuccZero.zeroTerm, Function.comp_def]
    funext i; cases i using Fin.cases with
    | zero => simp [Rew.embSubsts, Rew.func, Function.comp_def]; funext j; cases j using Fin.cases <;> simp [Rew.func, Function.comp_def]
    | succ i => cases i using Fin.cases with
      | zero => simp [z, Rew.embSubsts, Rew.func, Function.comp_def]; funext j; exact Fin.elim0 j
      | succ i => exact Fin.elim0 i
  have hb : Rew.embSubsts ![y,x] ▹ eqB = b := by
    simp [b, eqB, rightTerm, PRASubSuccZero.zeroTerm, Function.comp_def]
    funext i; cases i using Fin.cases with
    | zero => simp [Rew.embSubsts, Rew.func, Function.comp_def]; funext j; cases j using Fin.cases <;> simp
    | succ i => cases i using Fin.cases with
      | zero => simp [z, Rew.embSubsts, Rew.func, Function.comp_def]; funext j; exact Fin.elim0 j
      | succ i => exact Fin.elim0 i
  have hgg' : extended nativeTheory ⊢! (a 🡒 b)ᴺ := by
    simpa only [matrix, Semiformula.rew_doubleNegation, LogicalConnective.HomClass.map_imply, ha, hb] using hh
  have himp : extended nativeTheory ⊢! aᴺ 🡒 bᴺ := by
    have h := Classical.choice (Derivation.imply_doubleNegation (Λ := extended nativeTheory) a b)
    exact Entailment.K_right h ⨀ hgg'
  have hz : nativeTheory ⊢! IPRAZeroDecidable.zeroDecSentence := Classical.choice IPRAZeroStepNative.zero_decidable
  let t : Term language ℕ := .func subCode ![x,y]
  have hdec := instantiateTheory (T := nativeTheory) IPRAZeroDecidable.zeroDec hz ![t]
  have hv : (fun i : Fin 2 => Rew.embSubsts ![t] (![#0, IPRANativeInduction.zeroTerm 1] i)) = ![t,z] := by
    funext i; cases i using Fin.cases with
    | zero => simp
    | succ i => cases i using Fin.cases with
      | zero => simp [z, IPRANativeInduction.zeroTerm, Rew.func, Function.comp_def]; funext j; exact Fin.elim0 j
      | succ i => exact Fin.elim0 i
  have hd : extended nativeTheory ⊢! bi ⋎ ∼bi := by
    simpa [IPRAZeroDecidable.zeroDec, IPRAZeroDecidable.zeroEq, bi, t, z, Semiformulaᵢ.rewAux, Semiformulaᵢ.rew_rel, Function.comp_def, hv] using hdec
  have himp' : extended nativeTheory ⊢! (∼∼(.rel .eq ![.func subCode ![.func .succ (fun _ => x),y],z]) 🡒 ∼∼bi) := by
    simpa only [a, b, bi, Semiformula.doubleNegation_rel] using himp
  have hst : extended nativeTheory ⊢! (bi ⋎ ∼bi) 🡒 (∼∼bi 🡒 bi) := by
    apply Classical.choice
    change extended nativeTheory ⊢ _
    int_prover
  have hp := Entailment.C_trans (Entailment.C_trans Entailment.dni himp') (hst ⨀ hd)
  apply extendedToTheory nativeTheory
  simp only [result, Rewriting.app_all, Rew.q_emb]
  apply HilbertProofᵢ.gen
  apply HilbertProofᵢ.gen
  have hvA : (fun i : Fin 2 => Rew.free (Rew.free (Rew.emb (![leftTerm,PRASubSuccZero.zeroTerm] i)))) =
      ![.func subCode ![.func .succ (fun _ => x),y],z] := by
    funext i; cases i using Fin.cases with
    | zero =>
      simp [leftTerm, x, y, Rew.func, Function.comp_def]
      funext k; cases k using Fin.cases with
      | zero =>
        simp [Rew.func, Function.comp_def]
        funext j; cases j using Fin.cases with
        | zero =>
          change Rew.free (Rew.free (#(Fin.last 1) : Semiterm language ℕ 2)) = &1
          rw [Rew.free_bvar_last, Rew.free_fvar]
        | succ j => exact Fin.elim0 j
      | succ k => cases k using Fin.cases with
        | zero =>
          change Rew.free (Rew.free (#(0 : Fin 2) : Semiterm language ℕ 2)) = &0
          rw [Rew.free_bvar_castSucc_zero, Rew.free_bvar_last_zero]
        | succ k => exact Fin.elim0 k
    | succ j => cases j using Fin.cases with
      | zero => simp [PRASubSuccZero.zeroTerm, z, Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
      | succ j => exact Fin.elim0 j
  have hvB : (fun i : Fin 2 => Rew.free (Rew.free (Rew.emb (![rightTerm,PRASubSuccZero.zeroTerm] i)))) =
      ![.func subCode ![x,y],z] := by
    funext i; cases i using Fin.cases with
    | zero =>
      simp [rightTerm, x, y, Rew.func, Function.comp_def]
      funext k; cases k using Fin.cases with
      | zero =>
          change Rew.free (Rew.free (#(Fin.last 1) : Semiterm language ℕ 2)) = &1
          rw [Rew.free_bvar_last, Rew.free_fvar]
      | succ k => cases k using Fin.cases with
        | zero =>
          change Rew.free (Rew.free (#(0 : Fin 2) : Semiterm language ℕ 2)) = &0
          rw [Rew.free_bvar_castSucc_zero, Rew.free_bvar_last_zero]
        | succ k => exact Fin.elim0 k
    | succ j => cases j using Fin.cases with
      | zero => simp [PRASubSuccZero.zeroTerm, z, Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
      | succ j => exact Fin.elim0 j
  change extended nativeTheory ⊢! _
  simpa [bi, Semiformulaᵢ.rewAux, Semiformulaᵢ.rew_rel, Rewriting.free, Function.comp_def, hvA, hvB] using hp
theorem native_provable : nativeTheory ⊢ result := ⟨native⟩
end DiophantineConsistency.IPRASubSuccZeroNative
