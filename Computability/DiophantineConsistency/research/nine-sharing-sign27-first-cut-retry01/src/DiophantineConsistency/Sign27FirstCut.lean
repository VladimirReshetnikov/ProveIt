import DiophantineConsistency.SharingSign27Squares
import DiophantineConsistency.SharingSign28Squares

/-! SOURCE-ONLY: lift, deleted N1 and first common residual. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign27FirstCut
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def lift {S : Type*} [CommSemiring S] (v : Fin 28 → S) : Fin 29 → S :=
  ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12, v 13, v 14, v 15, v 16, v 17, v 18, v 19, v 20, v 21 + 1, v 21 * (v 21 + 2), v 22, v 23, v 24, v 25, v 26, v 27]

def oldN1 : Expr (Fin 29) :=
  (Expr.var 21 * Expr.var 21 - Expr.var 22) - Expr.constant (1 : ℤ)

theorem oldN1_row (p : Fin 4 → ℤ) :
    oldN1 ∈ SharingSeed28Sextic.firstResidual p :: SharingSeed28Sextic.remainingResiduals p := by
  simp [SharingSeed28Sextic.remainingResiduals, oldN1]

theorem oldN1_zero (v : Fin 28 → V) :
    InternalZero oldN1 (lift v) := by
  apply (internalZero_iff _ _).mpr
  simp [oldN1, lift, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant, map_add, map_mul, map_ofNat]
  <;> ring

theorem first_eval (p : Fin 4 → ℤ) (v : Fin 28 → V) :
    (SharingSeed28Sextic.firstResidual p).evalRing (fun j => ι (lift v j)) =
      (SharingSeed27Sextic.firstResidual p).evalRing (fun j => ι (v j)) := by
  simp [SharingSeed28Sextic.firstResidual, SharingSeed27Sextic.firstResidual,
    lift, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant]
end DiophantineConsistency.Sign27FirstCut
#print axioms DiophantineConsistency.Sign27FirstCut.oldN1_row
#print axioms DiophantineConsistency.Sign27FirstCut.oldN1_zero
#print axioms DiophantineConsistency.Sign27FirstCut.first_eval
