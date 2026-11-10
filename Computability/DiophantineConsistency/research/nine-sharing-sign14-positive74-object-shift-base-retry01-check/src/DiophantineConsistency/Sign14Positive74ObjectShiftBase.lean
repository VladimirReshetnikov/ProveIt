import DiophantineConsistency.Sign14Positive74ObjectMatrixGuard
import DiophantineConsistency.IPRAAddRecursion

/-! SOURCE-ONLY: variable split/shift base and a native zero-addition ingredient. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74ObjectShiftBase
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open Rewriting HilbertProofᵢ
open PRALanguage PRATheory PRAFiniteFunctionCodes IPRANativeTheory IPRANativeInduction
open IPRATheoryHilbertBridge IPRATheoryInstantiation IPRANativeAtomStability
open Sign14Positive74ObjectPredecessor AdaptiveEquationSyntax2011
local instance : language.DecidableEq where
  func := fun k => by change DecidableEq (Code k); infer_instance
  rel := fun k => by change DecidableEq (Language.ORing.Rel k); infer_instance

theorem shiftedVariableNegative :
    (positiveShift (Expr.var (0 : Fin 1))).splitNatural.2 =
      NatExpr.add (NatExpr.constant 0) (NatExpr.constant 0) := by rfl

theorem unshiftedVariableNegative :
    (Expr.var (0 : Fin 1)).splitNatural.2 = NatExpr.constant 0 := by rfl

def zeroAddZero : extended nativeTheory ⊢!
    eqAt (.func addCode ![zero,zero]) zero := by
  let m : Semisentenceᵢ language 1 :=
    Semiformulaᵢ.rel .eq ![.func addCode ![#0, zeroTerm 1], #0]
  have ha : nativeTheory ⊢! ∀⁰* m := by
    apply Classical.choice
    simpa [m, zeroTerm, IPRAAddRecursion.addZeroI, allClosure_succ] using IPRAAddRecursion.add_zero_native
  have hp := instantiateTheory (T := nativeTheory) m ha ![zero]
  have hv : (fun i : Fin 2 => (Rew.embSubsts ![zero])
      (![.func addCode ![#0, zeroTerm 1], #0] i)) = ![.func addCode ![zero,zero],zero] := by
    apply funext
    simp [Fin.forall_fin_two, zeroTerm, zero, Rew.func, funext_iff]
  simpa [m, eqAt, Semiformulaᵢ.rewAux, Semiformulaᵢ.rew_rel, Function.comp_def, hv] using hp
end DiophantineConsistency.Sign14Positive74ObjectShiftBase
#print axioms DiophantineConsistency.Sign14Positive74ObjectShiftBase.shiftedVariableNegative
#print axioms DiophantineConsistency.Sign14Positive74ObjectShiftBase.unshiftedVariableNegative
#print axioms DiophantineConsistency.Sign14Positive74ObjectShiftBase.zeroAddZero
