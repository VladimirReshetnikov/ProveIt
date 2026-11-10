import DiophantineConsistency.Sign14Positive74ObjectGuard
import DiophantineConsistency.IPRAPredReconstruct
import DiophantineConsistency.IPRANativeAtomStability
import DiophantineConsistency.IPRATheoryInstantiation
import Foundation.Meta.IntProver

/-! SOURCE-ONLY: open native reconstruction under nonzero assumption. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74ObjectPredecessor
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open PRALanguage PRATheory PRAFiniteFunctionCodes IPRANativeTheory IPRANativeInduction
open IPRATheoryHilbertBridge IPRATheoryInstantiation IPRANativeAtomStability
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance
local instance : Entailment.Int (extended nativeTheory) where
  efq := HilbertProofᵢ.eaxm (Or.inl (by simp [Hilbertᵢ.Intuitionistic]))

def zero : Term language ℕ := .func (Code.zero 0) Fin.elim0
def pred (x : Term language ℕ) : Term language ℕ := .func predCode (fun _ => x)
def succ (x : Term language ℕ) : Term language ℕ := .func Code.succ (fun _ => x)

def reconstructionOpen (x : Term language ℕ) :
    extended nativeTheory ⊢! (eqAt x zero ⋎ eqAt x (succ (pred x))) := by
  have h := instantiateTheory (T := nativeTheory) IPRAPredReconstruct.reconstruct
    (Classical.choice IPRAPredReconstruct.reconstruction) ![x]
  have hv0 : (fun i : Fin 2 => (Rew.embSubsts ![x]) (![.bvar 0, zeroTerm 1] i)) = ![x, zero] := by
    apply funext
    simp [Fin.forall_fin_two, zero, zeroTerm, Rew.func, funext_iff]
  have hv1 : (fun i : Fin 2 => (Rew.embSubsts ![x])
      (![.bvar 0, .func Code.succ (fun _ => .func predCode (fun _ => .bvar 0))] i)) =
      ![x, succ (pred x)] := by
    apply funext
    simp [Fin.forall_fin_two, succ, pred, Rew.func, funext_iff]
  simpa [IPRAPredReconstruct.reconstruct, IPRAPredReconstruct.reconEq,
    IPRAZeroDecidable.zeroEq, zeroTerm, eqAt, zero, pred, succ,
    Semiformulaᵢ.rewAux, Semiformulaᵢ.rew_rel, Rew.func, Function.comp_def, hv0, hv1] using h

def nonzeroReconstructionOpen (x : Term language ℕ) :
    extended nativeTheory ⊢! (∼eqAt x zero 🡒 eqAt x (succ (pred x))) := by
  have t : extended nativeTheory ⊢!
      ((eqAt x zero ⋎ eqAt x (succ (pred x))) 🡒
        (∼eqAt x zero 🡒 eqAt x (succ (pred x)))) := by
    apply Classical.choice
    change extended nativeTheory ⊢ _
    int_prover
  exact t ⨀ reconstructionOpen x
end DiophantineConsistency.Sign14Positive74ObjectPredecessor
#print axioms DiophantineConsistency.Sign14Positive74ObjectPredecessor.reconstructionOpen
#print axioms DiophantineConsistency.Sign14Positive74ObjectPredecessor.nonzeroReconstructionOpen
