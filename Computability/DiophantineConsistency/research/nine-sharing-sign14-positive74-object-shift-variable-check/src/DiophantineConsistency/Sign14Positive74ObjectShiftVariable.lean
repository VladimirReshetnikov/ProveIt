import DiophantineConsistency.Sign14Positive74ObjectShiftBase
import DiophantineConsistency.IPRAAddOneDirect

/-! SOURCE ONLY: positive branch of split/shift variable case. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74ObjectShiftVariable
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open PRALanguage PRATheory PRAFiniteFunctionCodes IPRANativeTheory IPRANativeInduction
open IPRATheoryHilbertBridge IPRATheoryInstantiation IPRANativeAtomStability
open Sign14Positive74ObjectPredecessor AdaptiveEquationSyntax2011
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

theorem shiftedVariablePositive :
    (positiveShift (Expr.var (0 : Fin 1))).splitNatural.1 =
      NatExpr.add (NatExpr.var 0) (NatExpr.constant 1) := by rfl

def addOneOpen (x : Term language ℕ) : extended nativeTheory ⊢!
    eqAt (.func addCode ![x, .func oneCode Fin.elim0]) (.func .succ (fun _ => x)) := by
  let m : Semisentenceᵢ language 1 :=
    Semiformulaᵢ.rel .eq ![.func addCode ![#0, .func oneCode Fin.elim0],
      .func .succ (fun _ => #0)]
  have ha : nativeTheory ⊢! ∀⁰* m := by
    apply Classical.choice
    simpa [m, IPRAAddOneDirect.addOneI, stepTerm, applyCode, allClosure_succ,
      Entailment.Provable] using IPRAAddOneDirect.add_one_native
  have hp := instantiateTheory (T := nativeTheory) m ha ![x]
  have hv : (fun i : Fin 2 => (Rew.embSubsts ![x])
      (![.func addCode ![#0, .func oneCode Fin.elim0], .func .succ (fun _ => #0)] i)) =
        ![.func addCode ![x, .func oneCode Fin.elim0], .func .succ (fun _ => x)] := by
    apply funext
    simp [Fin.forall_fin_two, Rew.func, funext_iff]
  simpa [m, eqAt, Semiformulaᵢ.rewAux, Semiformulaᵢ.rew_rel, Function.comp_def, hv] using hp
end DiophantineConsistency.Sign14Positive74ObjectShiftVariable
#print axioms DiophantineConsistency.Sign14Positive74ObjectShiftVariable.shiftedVariablePositive
#print axioms DiophantineConsistency.Sign14Positive74ObjectShiftVariable.addOneOpen
