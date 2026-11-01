import DiophantineConsistency.IPRAReconstructBridge
import DiophantineConsistency.IPRATheoryInstantiation
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAReconstructBridgeOpen
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory IPRANativeTheory
open IPRAFunctionCongruenceOpen IPRAAddOneDirect IPRASubArithmetic IPRAReconstructAlgebra
open IPRATheoryHilbertBridge IPRATheoryInstantiation
local instance : language.DecidableEq where
  func := fun k => by
    change DecidableEq (Code k)
    infer_instance
  rel := fun k => by
    change DecidableEq (Language.ORing.Rel k)
    infer_instance

def open_bridge (x y : Term language ℕ) : extended nativeTheory ⊢!
    Z (sub y (sc x)) 🡒 ∼Z (sub y x) 🡒 equal (sc x) y := by
  have h : nativeTheory ⊢! ∀⁰* IPRAReconstructBridge.matrix := by
    simpa [allClosure_succ] using Classical.choice IPRAReconstructBridge.successor_bridge
  have hs := instantiateTheory (T := nativeTheory) IPRAReconstructBridge.matrix h ![x,y]
  convert hs using 1
  simp [IPRAReconstructBridge.matrix, Z, z, IPRASubArithmetic.sub, sc, equal,
    IPRANativeInduction.zeroTerm, Semiformulaᵢ.rew_rel]
  have h1 : ![.func subCode ![y,.func Code.succ (fun _ => x)], .func (Code.zero 0) Fin.elim0] =
      (fun i : Fin 2 => Rew.embSubsts ![x,y] ((![.func subCode ![#1,.func Code.succ (fun _ => #0)], IPRANativeInduction.zeroTerm 2] : Fin 2 → TermN 2) i)) := by
    funext i; cases i using Fin.cases with
    | zero => simp [Rew.func, Function.comp_def, Matrix.fun_eq_vec_two]
    | succ i => cases i using Fin.cases with
      | zero => simp [IPRANativeInduction.zeroTerm, Rew.func, Function.comp_def]; funext j; exact Fin.elim0 j
      | succ i => exact Fin.elim0 i
  have h2 : ![.func subCode ![y,x], .func (Code.zero 0) Fin.elim0] =
      (fun i : Fin 2 => Rew.embSubsts ![x,y] ((![.func subCode ![#1,#0], IPRANativeInduction.zeroTerm 2] : Fin 2 → TermN 2) i)) := by
    funext i; cases i using Fin.cases with
    | zero => simp [Rew.func, Matrix.fun_eq_vec_two]
    | succ i => cases i using Fin.cases with
      | zero => simp [IPRANativeInduction.zeroTerm, Rew.func, Function.comp_def]; funext j; exact Fin.elim0 j
      | succ i => exact Fin.elim0 i
  have h3 : ![.func Code.succ (fun _ => x),y] =
      (fun i : Fin 2 => Rew.embSubsts ![x,y] ((![.func Code.succ (fun _ => #0),#1] : Fin 2 → TermN 2) i)) := by
    funext i; cases i using Fin.cases with
    | zero => simp [Rew.func, Function.comp_def]
    | succ i => cases i using Fin.cases with
      | zero => rfl
      | succ i => exact Fin.elim0 i
  simpa [IPRANativeInduction.zeroTerm, Semiformulaᵢ.neg_def] using And.intro h1 (And.intro h2 h3)
end DiophantineConsistency.IPRAReconstructBridgeOpen
