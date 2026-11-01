import DiophantineConsistency.IPRANativeAtomStability
import DiophantineConsistency.IPRABoundedErasureLogic
import Foundation.Meta.IntProver
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRANativeBoundedGuard
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open DiophantineConsistency.PRALanguage DiophantineConsistency.PRAFiniteFunctionCodes
open DiophantineConsistency.IPRANativeTheory DiophantineConsistency.IPRATheoryHilbertBridge
open DiophantineConsistency.IPRANativeAtomStability DiophantineConsistency.IPRABoundedErasureLogic
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance
local instance : Entailment.Int (extended nativeTheory) where
  efq := HilbertProofᵢ.eaxm (Or.inl (by simp [Hilbertᵢ.Intuitionistic]))

def logicGuard (p q : Propositionᵢ language) :
    extended nativeTheory ⊢! (p ⋎ ∼p) 🡒 ((∼p ⋎ q) 🡘 (p 🡒 q)) := by
  apply Classical.choice
  change extended nativeTheory ⊢ _
  int_prover

def orderGuard (heq : nativeTheory ⊢! eqDecSentence) (a b : Term language ℕ) (q : Propositionᵢ language) :
    extended nativeTheory ⊢! (∼ltAt a b ⋎ q) 🡘 (ltAt a b 🡒 q) :=
  logicGuard (ltAt a b) q ⨀ orderDecOpen heq a b

def allOrderGuard (heq : nativeTheory ⊢! eqDecSentence)
    (a b : Semiterm language ℕ 1) (q : Semipropositionᵢ language 1) :
    extended nativeTheory ⊢!
      (∀⁰ (∼(Semiformulaᵢ.rel Language.ORing.Rel.lt ![a,b]) ⋎ q)) 🡘
      (∀⁰ ((Semiformulaᵢ.rel Language.ORing.Rel.lt ![a,b]) 🡒 q)) := by
  have he := orderGuard heq (Rew.free a) (Rew.free b) (free q)
  have hv : (fun i : Fin 2 => Rew.free (![a,b] i)) = ![Rew.free a, Rew.free b] := by
    funext i
    cases i using Fin.cases with
    | zero => simp
    | succ j => cases j using Fin.cases with
      | zero => simp
      | succ j => exact Fin.elim0 j
  have hleft := Entailment.K_left he
  have hright := Entailment.K_right he
  apply Entailment.K_intro
  · apply eraseAll
    simpa [ltAt, Semiformulaᵢ.rew_rel, Function.comp_def, hv] using hleft
  · apply eraseAll
    simpa [ltAt, Semiformulaᵢ.rew_rel, Function.comp_def, hv] using hright
end DiophantineConsistency.IPRANativeBoundedGuard
