import DirectMainOrdinary
import DirectMainFirst

/-! Bind the old first unit at the same transformed valuation. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DirectMainOldFirst
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency FreeJDirectMainGraph DirectMainOrdinary
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ModelDifferenceRing
open ArithmeticAdaptiveFactorMagnitude2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem old_first_zero (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hz : InternalZero (graph (integerPorts p)).output v) :
    InternalZero (FreeJSumSquares.firstResidual (integerPorts p)) (oldVal p v) := by
  have hd := (internalZero_iff _ _).mp (DirectMainFirst.first_zero p v hz)
  change (graph (integerPorts p)).first.evalRing (fun i => ι (v i)) = 0 at hd
  have hsame : (graph (integerPorts p)).first = (FreeJXQ91.graph (integerPorts p)).first := by rfl
  rw [hsame] at hd
  have h92 := (FreeJXQ91.first_eval (integerPorts p) (fun i => ι (v i))).trans hd
  have h95 := FreeJQCube92.first_eval (integerPorts p)
    (FreeJXQ91.liftX (integerPorts p) (fun i => ι (v i)))
  rw [h92,mul_zero] at h95
  have hlift := FreeJXQ91Model.lift_cast p v
  change (fun j => ι (FreeJXQ91Model.transform p v j)) =
    FreeJXQ91.liftX (integerPorts p) (fun i => ι (v i)) at hlift
  have hlift2 := FreeJQCube92Model.lift_cast p (FreeJXQ91Model.transform p v)
  change (fun j => ι (oldVal p v j)) =
    FreeJQCube92.lift (integerPorts p) (fun j => ι (FreeJXQ91Model.transform p v j)) at hlift2
  rw [←hlift, ←hlift2] at h95
  exact (internalZero_iff _ _).mpr h95

theorem old_first_unit (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hz : InternalZero (graph (integerPorts p)).output v) :
    (pairEval (Ordinary12FreeJ.core (integerPorts p)).first (oldVal p v)).1 =
      (pairEval (Ordinary12FreeJ.core (integerPorts p)).first (oldVal p v)).2+1 := by
  rw [FreeJSumSquares.first_decompose]
  have h := old_first_zero p v hz
  simpa [pairEval,Expr.splitNatural,NatExpr.evalSemiring,InternalZero,add_comm] using h

#print axioms DirectMainOldFirst.old_first_zero
#print axioms DirectMainOldFirst.old_first_unit
end DirectMainOldFirst
