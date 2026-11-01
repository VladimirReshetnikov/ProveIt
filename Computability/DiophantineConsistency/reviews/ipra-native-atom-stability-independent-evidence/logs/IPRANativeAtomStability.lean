import DiophantineConsistency.IPRATheoryInstantiation
import DiophantineConsistency.IPRANativeTheory
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRANativeAtomStability
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRATheory DiophantineConsistency.PRAFiniteFunctionCodes
open DiophantineConsistency.IPRANativeTheory DiophantineConsistency.IPRATheoryHilbertBridge DiophantineConsistency.IPRATheoryInstantiation
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

def eqMatrix : Semisentenceᵢ language 2 := Semiformulaᵢ.rel Language.ORing.Rel.eq ![#0,#1]
def eqDecSentence : Sentenceᵢ language := ∀⁰* (eqMatrix ⋎ ∼eqMatrix)
def orderMatrix : Semisentenceᵢ language 2 :=
  (Semiformulaᵢ.rel Language.ORing.Rel.lt ![#0,#1]) 🡘
    (Semiformulaᵢ.rel Language.ORing.Rel.eq ![applyCode ltBitCode (fun i => .bvar i), applyCode oneCode Fin.elim0])

def eqAt (a b : Term language ℕ) : Propositionᵢ language := Semiformulaᵢ.rel Language.ORing.Rel.eq ![a,b]
def ltAt (a b : Term language ℕ) : Propositionᵢ language := Semiformulaᵢ.rel Language.ORing.Rel.lt ![a,b]

def eqDecOpen (h : nativeTheory ⊢! eqDecSentence) (a b : Term language ℕ) :
    extended nativeTheory ⊢! eqAt a b ⋎ ∼eqAt a b := by
  have hp := instantiateTheory (T := nativeTheory) (eqMatrix ⋎ ∼eqMatrix) h ![a,b]
  have hv : (fun i : Fin 2 => (Rew.embSubsts ![a,b]) (![#0,#1] i)) = ![a,b] := by
    funext i
    cases i using Fin.cases with
    | zero => simp
    | succ j => cases j using Fin.cases with
      | zero => simp
      | succ j => exact Fin.elim0 j
  simpa [eqAt, eqMatrix, Semiformulaᵢ.rewAux,
    Semiformulaᵢ.rew_rel, Function.comp_def, hv] using hp

def orderOpen (a b : Term language ℕ) :
    extended nativeTheory ⊢! ltAt a b 🡘 eqAt (Semiterm.func ltBitCode ![a,b]) (Semiterm.func oneCode Fin.elim0) := by
  have ho : nativeTheory ⊢! orderDefinitionI := Axiomatized.prfAxm (NativeAxiom.basic BasicAxiomI.orderDefinition)
  have hp := instantiateTheory (T := nativeTheory) orderMatrix ho ![a,b]
  have hv : (fun i : Fin 2 => (Rew.embSubsts ![a,b]) (![#0,#1] i)) = ![a,b] := by
    funext i
    cases i using Fin.cases with
    | zero => simp
    | succ j => cases j using Fin.cases with
      | zero => simp
      | succ j => exact Fin.elim0 j
  have ht : (fun i : Fin 2 => (Rew.embSubsts ![a,b]) (![applyCode ltBitCode (fun j => #j), applyCode oneCode Fin.elim0] i)) =
      ![Semiterm.func ltBitCode ![a,b], Semiterm.func oneCode Fin.elim0] := by
    funext i
    cases i using Fin.cases with
    | zero => simp [applyCode, Rew.func, Function.comp_def]
    | succ j => cases j using Fin.cases with
      | zero =>
        simp [applyCode, Rew.func, Function.comp_def]
        funext k
        exact Fin.elim0 k
      | succ j => exact Fin.elim0 j
  simpa [orderMatrix, ltAt, eqAt, Semiformulaᵢ.rewAux,
    Semiformulaᵢ.rew_rel, Function.comp_def, hv, ht] using hp

def orderDecOpen (h : nativeTheory ⊢! eqDecSentence) (a b : Term language ℕ) :
    extended nativeTheory ⊢! ltAt a b ⋎ ∼ltAt a b := by
  have ho := orderOpen a b
  have hd := eqDecOpen h (Semiterm.func ltBitCode ![a,b]) (Semiterm.func oneCode Fin.elim0)
  apply Entailment.of_C_of_C_of_A ?_ ?_ hd
  · exact Entailment.C_trans (Entailment.K_right ho) Entailment.or₁
  · exact Entailment.C_trans (Entailment.contra (Entailment.K_left ho)) Entailment.or₂
local instance : Entailment.Int (extended nativeTheory) where
  efq := HilbertProofᵢ.eaxm (Or.inl (by simp [Hilbertᵢ.Intuitionistic]))

def stableOfDec (A : Propositionᵢ language)
    (h : extended nativeTheory ⊢! A ⋎ ∼A) :
    extended nativeTheory ⊢! ∼∼A 🡒 A := by
  have hy : extended nativeTheory ⊢! A 🡒 (∼∼A 🡒 A) := Entailment.implyK
  have hn : extended nativeTheory ⊢! ∼A 🡒 (∼∼A 🡒 A) := by
    apply Entailment.FiniteContext.deduct'
    apply Entailment.FiniteContext.deduct
    have hna : [∼∼A, ∼A] ⊢[extended nativeTheory]! ∼A := Entailment.FiniteContext.byAxm₁
    have hnna : [∼∼A, ∼A] ⊢[extended nativeTheory]! ∼∼A := Entailment.FiniteContext.byAxm₀
    exact Entailment.FiniteContext.of Entailment.efq ⨀ (hnna ⨀ hna)
  exact Entailment.of_C_of_C_of_A hy hn h

def eqStableOpen (h : nativeTheory ⊢! eqDecSentence) (a b : Term language ℕ) :
    extended nativeTheory ⊢! ∼∼eqAt a b 🡒 eqAt a b := stableOfDec _ (eqDecOpen h a b)

def orderStableOpen (h : nativeTheory ⊢! eqDecSentence) (a b : Term language ℕ) :
    extended nativeTheory ⊢! ∼∼ltAt a b 🡒 ltAt a b := stableOfDec _ (orderDecOpen h a b)
end DiophantineConsistency.IPRANativeAtomStability
