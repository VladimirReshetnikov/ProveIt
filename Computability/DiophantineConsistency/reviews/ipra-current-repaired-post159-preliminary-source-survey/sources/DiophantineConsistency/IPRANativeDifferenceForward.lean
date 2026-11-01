import DiophantineConsistency.IPRANativeSubSelf
import DiophantineConsistency.IPRAAllSpecialize
/-! Native forward correctness of the two-difference equality test, from an explicit zero-decidability proof. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRANativeDifferenceForward
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRATheory DiophantineConsistency.PRAFiniteFunctionCodes
open DiophantineConsistency.IPRANativeTheory DiophantineConsistency.IPRANativeInduction DiophantineConsistency.IPRAAllSpecialize
open DiophantineConsistency.IPRATheoryHilbertBridge DiophantineConsistency.IPRATheoryInstantiation
open DiophantineConsistency.IPRANativeSubSelf
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

local instance : Entailment.Int (extended nativeTheory) where
  efq := HilbertProofᵢ.eaxm (Or.inl (by simp [Hilbertᵢ.Intuitionistic]))

/-- Formulas are definitionally identical to those in the equality-decision client. -/
def eqMatrix : Semisentenceᵢ language 2 := .rel .eq ![#0,#1]
def eqAt (a b : Term language ℕ) : Propositionᵢ language := .rel .eq ![a,b]
def diff1 : Semisentenceᵢ language 2 := .rel .eq ![.func subCode ![#0,#1], zeroTerm 2]
def diff2 : Semisentenceᵢ language 2 := .rel .eq ![.func subCode ![#1,#0], zeroTerm 2]
def forwardSentence : Sentenceᵢ language := ∀⁰* (eqMatrix 🡒 (diff1 ⋏ diff2))
def zeroOpen (t : Term language ℕ) : Propositionᵢ language := eqAt t (.func (.zero 0) Fin.elim0)

def leftMatrix : Semisentenceᵢ language 2 :=
  .rel .eq ![.func subCode ![#0,#1], zeroTerm 2]
def rightMatrix : Semisentenceᵢ language 2 :=
  .rel .eq ![.func subCode ![#1,#0], zeroTerm 2]

def leftLeib (x y : Term language ℕ) : extended nativeTheory ⊢!
    eqAt x y 🡒 (zeroOpen (.func subCode ![x,x]) 🡒 zeroOpen (.func subCode ![y,x])) := by
  have ha : nativeTheory ⊢! eqSubstitutionI leftMatrix :=
    Axiomatized.prfAxm (NativeAxiom.equality (EqualityAxiomI.substitution leftMatrix))
  have hp := instantiateTheory (T := nativeTheory) (leibnizBody leftMatrix) ha ![x,y,x]
  have hv : (Rew.embSubsts ![x,y,x] ▹ leibnizBody leftMatrix) =
      (eqAt x y 🡒 (zeroOpen (.func subCode ![x,x]) 🡒 zeroOpen (.func subCode ![y,x]))) := by
    simp [leibnizBody, eqLeft, eqRight, leftMatrix, eqAt, zeroOpen, zeroTerm,
      Semiformulaᵢ.rew_rel]
    refine ⟨?_, ?_, ?_⟩ <;> funext i <;> cases i using Fin.cases with
    | zero =>
      simp [Rew.func, Function.comp_def]
      try funext j
      try cases j using Fin.cases <;> simp
      all_goals change (Rew.embSubsts ![x,y,x]) (#(2 : Fin 3)) = x
      all_goals simp
    | succ j => cases j using Fin.cases with
      | zero => simp [Rew.func, Function.comp_def]; try funext j; try exact Fin.elim0 j
      | succ j => exact Fin.elim0 j
  rw [hv] at hp
  exact hp
def rightLeib (x y : Term language ℕ) : extended nativeTheory ⊢!
    eqAt x y 🡒 (zeroOpen (.func subCode ![x,x]) 🡒 zeroOpen (.func subCode ![x,y])) := by
  have ha : nativeTheory ⊢! eqSubstitutionI rightMatrix :=
    Axiomatized.prfAxm (NativeAxiom.equality (EqualityAxiomI.substitution rightMatrix))
  have hp := instantiateTheory (T := nativeTheory) (leibnizBody rightMatrix) ha ![x,y,x]
  have hv : (Rew.embSubsts ![x,y,x] ▹ leibnizBody rightMatrix) =
      (eqAt x y 🡒 (zeroOpen (.func subCode ![x,x]) 🡒 zeroOpen (.func subCode ![x,y]))) := by
    simp [leibnizBody, eqLeft, eqRight, rightMatrix, eqAt, zeroOpen, zeroTerm,
      Semiformulaᵢ.rew_rel]
    refine ⟨?_, ?_, ?_⟩ <;> funext i <;> cases i using Fin.cases with
    | zero =>
      simp [Rew.func, Function.comp_def]
      try funext j
      try cases j using Fin.cases <;> simp
      all_goals change (Rew.embSubsts ![x,y,x]) (#(2 : Fin 3)) = x
      all_goals simp
    | succ j => cases j using Fin.cases with
      | zero => simp [Rew.func, Function.comp_def]; try funext j; try exact Fin.elim0 j
      | succ j => exact Fin.elim0 j
  rw [hv] at hp
  exact hp

def selfOpen (hz : nativeTheory ⊢! DiophantineConsistency.IPRANativeSubSelf.zeroDecSentence) (x : Term language ℕ) :
    extended nativeTheory ⊢! zeroOpen (.func subCode ![x,x]) := by
  have hp := instantiateTheory (T := nativeTheory) subSelfBody (nativeSubSelf hz) ![x]
  have hv : (fun i : Fin 2 => Rew.embSubsts ![x] (![.func subCode ![#0,#0], zeroTerm 1] i)) =
      ![.func subCode ![x,x], .func (.zero 0) Fin.elim0] := by
    funext i
    cases i using Fin.cases with
    | zero => simp [Rew.func, Function.comp_def]; funext k; cases k using Fin.cases with
      | zero => simp
      | succ j => cases j using Fin.cases with
        | zero => simp
        | succ j => exact Fin.elim0 j
    | succ j => cases j using Fin.cases with
      | zero => simp [zeroTerm, Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
      | succ j => exact Fin.elim0 j
  simpa [subSelfBody, zeroOpen, eqAt, Semiformulaᵢ.rewAux,
    Semiformulaᵢ.rew_rel, Function.comp_def, hv] using hp

def forwardProofOpen (hz : nativeTheory ⊢! DiophantineConsistency.IPRANativeSubSelf.zeroDecSentence) (x y : Term language ℕ) :
    extended nativeTheory ⊢! eqAt x y 🡒
      (zeroOpen (.func subCode ![x,y]) ⋏ zeroOpen (.func subCode ![y,x])) := by
  have hs := selfOpen hz x
  have hleft := leftLeib x y
  have hright := rightLeib x y
  have tacticProof (a b c : Propositionᵢ language) :
      extended nativeTheory ⊢! b 🡒 ((a 🡒 (b 🡒 c)) 🡒 (a 🡒 c)) := by
    apply Classical.choice
    change extended nativeTheory ⊢ _
    int_prover
  exact Entailment.CK_of_C_of_C (tacticProof _ _ _ ⨀ hs ⨀ hright)
    (tacticProof _ _ _ ⨀ hs ⨀ hleft)

def forwardProof (hz : nativeTheory ⊢! DiophantineConsistency.IPRANativeSubSelf.zeroDecSentence) :
    nativeTheory ⊢! forwardSentence := by
  have ho := forwardProofOpen hz (&0) (&1)
  apply extendedToTheory nativeTheory
  simp only [forwardSentence, allClosure_succ, allClosure_zero]
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
  have hf1 : (fun i : Fin 2 => Rew.free (Rew.free (Rew.emb (![.func subCode ![#0,#1], zeroTerm 2] i)))) =
      ![.func subCode ![&0,&1], .func (.zero 0) Fin.elim0] := by
    funext i
    cases i using Fin.cases with
    | zero => simp [Rew.func, Function.comp_def, hv]
    | succ j => cases j using Fin.cases with
      | zero => simp [zeroTerm, Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
      | succ j => exact Fin.elim0 j
  have hf2 : (fun i : Fin 2 => Rew.free (Rew.free (Rew.emb (![.func subCode ![#1,#0], zeroTerm 2] i)))) =
      ![.func subCode ![&1,&0], .func (.zero 0) Fin.elim0] := by
    funext i
    cases i using Fin.cases with
    | zero => simp [Rew.func, Function.comp_def]; funext k; cases k using Fin.cases with
      | zero => change Rew.free (Rew.free (#(Fin.last 1) : Semiterm language ℕ 2)) = &1; rw [Rew.free_bvar_last, Rew.free_fvar]
      | succ j => cases j using Fin.cases with
        | zero => change Rew.free (Rew.free (#(0 : Fin 2) : Semiterm language ℕ 2)) = &0; rw [Rew.free_bvar_castSucc_zero, Rew.free_bvar_last_zero]
        | succ j => exact Fin.elim0 j
    | succ j => cases j using Fin.cases with
      | zero => simp [zeroTerm, Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
      | succ j => exact Fin.elim0 j
  simpa [eqMatrix, diff1, diff2, zeroOpen, eqAt, Semiformulaᵢ.rewAux,
    Semiformulaᵢ.rew_rel, Rewriting.free, Rew.func, Function.comp_def, hv, hf1, hf2] using ho
end DiophantineConsistency.IPRANativeDifferenceForward
