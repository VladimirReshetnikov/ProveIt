import DiophantineConsistency.IPRADifferenceInvariantBase
import DiophantineConsistency.IPRASubSuccSelfNonzero
import DiophantineConsistency.IPRAAllSpecialize
import Foundation.Meta.IntProver
/-! Native substitution consequence needed by the two-difference successor step. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRADifferenceSuccEq
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRATheory DiophantineConsistency.PRAFiniteFunctionCodes
open DiophantineConsistency.IPRANativeInduction DiophantineConsistency.IPRANativeTheory
open DiophantineConsistency.IPRATheoryHilbertBridge DiophantineConsistency.IPRATheoryInstantiation
open DiophantineConsistency.IPRADifferenceInvariant DiophantineConsistency.IPRANativeDifferenceEquality
open DiophantineConsistency.IPRANativeAtomStability DiophantineConsistency.IPRAAllSpecialize
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

local instance : Entailment.Int (extended nativeTheory) where
  efq := HilbertProofᵢ.eaxm (Or.inl (by simp [Hilbertᵢ.Intuitionistic]))

def sx (x : Term language ℕ) : Term language ℕ := .func Code.succ (fun _ => x)
def negativeMatrix : Semisentenceᵢ language 2 :=
  ∼(.rel .eq ![.func subCode ![.func Code.succ (fun _ => #1),#0], zeroTerm 2])
set_option linter.unnecessarySeqFocus false in
def negativeLeib (x y : Term language ℕ) : extended nativeTheory ⊢!
    eqAt x y 🡒 (∼zeroOpen (.func subCode ![sx x,x]) 🡒 ∼zeroOpen (.func subCode ![sx x,y])) := by
  have ha : nativeTheory ⊢! eqSubstitutionI negativeMatrix :=
    Axiomatized.prfAxm (NativeAxiom.equality (EqualityAxiomI.substitution negativeMatrix))
  have hp := instantiateTheory (T := nativeTheory) (leibnizBody negativeMatrix) ha ![x,y,x]
  have hv : (Rew.embSubsts ![x,y,x] ▹ leibnizBody negativeMatrix) =
      (eqAt x y 🡒 (∼zeroOpen (.func subCode ![sx x,x]) 🡒 ∼zeroOpen (.func subCode ![sx x,y]))) := by
    simp [leibnizBody, eqLeft, eqRight, negativeMatrix, eqAt, zeroOpen, zeroTerm,
      Semiformulaᵢ.rew_rel, sx]
    refine ⟨?_, ?_, ?_⟩
    all_goals try (congr 2)
    all_goals funext i <;> cases i using Fin.cases with
    | zero =>
      simp [Rew.func, Function.comp_def]
      try funext j
      try cases j using Fin.cases <;> simp [Rew.func, Function.comp_def]
      all_goals try (funext k)
      all_goals change (Rew.embSubsts ![x,y,x]) (#(2 : Fin 3)) = x
      all_goals simp
    | succ j => cases j using Fin.cases with
      | zero => simp [Rew.func, Function.comp_def]; try funext k; try exact Fin.elim0 k
      | succ j => exact Fin.elim0 j
  rw [hv] at hp
  exact hp
def subSuccSelfOpen (x : Term language ℕ) : extended nativeTheory ⊢!
    ∼zeroOpen (.func subCode ![sx x,x]) := by
  let m : Semisentenceᵢ language 1 :=
    ∼(.rel .eq ![.func subCode ![.func Code.succ (fun _ => #0), #0], zeroTerm 1])
  have hp := instantiateTheory (T := nativeTheory) m (Classical.choice DiophantineConsistency.IPRASubSuccSelfNonzero.native) ![x]
  have hv : (fun i : Fin 2 => Rew.embSubsts ![x] (![.func subCode ![.func Code.succ (fun _ => #0),#0],zeroTerm 1] i)) =
      ![.func subCode ![sx x,x], .func (Code.zero 0) Fin.elim0] := by
    funext i
    cases i using Fin.cases with
    | zero =>
      simp [Rew.func, Function.comp_def, sx]
      funext k; cases k using Fin.cases with
      | zero => simp [Rew.func, Function.comp_def]
      | succ j => cases j using Fin.cases with
        | zero => simp
        | succ j => exact Fin.elim0 j
    | succ j => cases j using Fin.cases with
      | zero => simp [zeroTerm, Rew.func, Function.comp_def]; funext k; exact Fin.elim0 k
      | succ j => exact Fin.elim0 j
  simpa [m, zeroOpen, eqAt, Semiformulaᵢ.rewAux, Semiformulaᵢ.rew_rel, Function.comp_def, hv] using hp

def equalityNotSuccDiff (x y : Term language ℕ) : extended nativeTheory ⊢!
    eqAt x y 🡒 ∼zeroOpen (.func subCode ![sx x,y]) := by
  have h := negativeLeib x y
  have hself := subSuccSelfOpen x
  exact (Entailment.C_swap h) ⨀ hself

end DiophantineConsistency.IPRADifferenceSuccEq
