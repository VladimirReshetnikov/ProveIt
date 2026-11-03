import DirectMainGraph
import XQ91Model
import QCube92Model

/-! Bind the unchanged ordinary factor without asserting an old graph zero. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DirectMainOrdinary
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency FreeJDirectMainGraph
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ModelDifferenceRing
open ArithmeticAdaptiveFactorMagnitude2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def integerPorts (p : Fin 4 → ℕ) : Fin 4 → ℤ := fun i => (p i : ℤ)
def oldVal (p : Fin 4 → ℕ) (v : Fin 12 → V) : Fin 12 → V :=
  FreeJQCube92Model.transform p (FreeJXQ91Model.transform p v)

theorem ordinary_zero (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hz : InternalZero (graph (integerPorts p)).output v) :
    InternalZero (graph (integerPorts p)).ordinary v := by
  rw [internalZero_iff] at hz ⊢
  have hshape : (graph (integerPorts p)).output =
      (graph (integerPorts p)).first*(graph (integerPorts p)).first+
      (graph (integerPorts p)).main*(graph (integerPorts p)).main+
      (graph (integerPorts p)).ordinary*(graph (integerPorts p)).ordinary := by rfl
  rw [hshape] at hz
  simp only [Expr.evalRing_add,Expr.evalRing_mul] at hz
  have ha := sq_nonneg ((graph (integerPorts p)).first.evalRing (fun j => ι (v j)))
  have hb := sq_nonneg ((graph (integerPorts p)).main.evalRing (fun j => ι (v j)))
  have hc := sq_nonneg ((graph (integerPorts p)).ordinary.evalRing (fun j => ι (v j)))
  have h : (graph (integerPorts p)).ordinary.evalRing (fun j => ι (v j)) *
      (graph (integerPorts p)).ordinary.evalRing (fun j => ι (v j)) = 0 := by nlinarith
  exact mul_self_eq_zero.mp h

theorem old_ordinary_zero (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hz : InternalZero (graph (integerPorts p)).output v) :
    InternalZero (FreeJSumSquares.ordinaryResidual (integerPorts p)) (oldVal p v) := by
  have hd := (internalZero_iff _ _).mp (ordinary_zero p v hz)
  have hsame : (graph (integerPorts p)).ordinary = (FreeJXQ91.graph (integerPorts p)).ordinary := by rfl
  rw [hsame] at hd
  have h92 := (FreeJXQ91.ordinary_eval (integerPorts p) (fun i => ι (v i))).trans hd
  have h95 := (FreeJQCube92.ordinary_eval (integerPorts p)
    (FreeJXQ91.liftX (integerPorts p) (fun i => ι (v i)))).trans h92
  change (FreeJSumSquares.ordinaryResidual (integerPorts p)).evalRing
    (FreeJQCube92.lift (integerPorts p) (FreeJXQ91.liftX (integerPorts p) (fun i => ι (v i)))) = 0 at h95
  have hlift := FreeJXQ91Model.lift_cast p v
  change (fun j => ι (FreeJXQ91Model.transform p v j)) =
    FreeJXQ91.liftX (integerPorts p) (fun i => ι (v i)) at hlift
  have hlift2 := FreeJQCube92Model.lift_cast p (FreeJXQ91Model.transform p v)
  change (fun j => ι (oldVal p v j)) =
    FreeJQCube92.lift (integerPorts p) (fun j => ι (FreeJXQ91Model.transform p v j)) at hlift2
  rw [←hlift, ←hlift2] at h95
  exact (internalZero_iff _ _).mpr h95

theorem old_ordinary_unit (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hz : InternalZero (graph (integerPorts p)).output v) :
    (pairEval (Ordinary12FreeJ.core (integerPorts p)).ordinary (oldVal p v)).1 =
      (pairEval (Ordinary12FreeJ.core (integerPorts p)).ordinary (oldVal p v)).2+1 := by
  rw [FreeJSumSquares.ordinary_decompose]
  have h := old_ordinary_zero p v hz
  simpa [pairEval,Expr.splitNatural,NatExpr.evalSemiring,InternalZero,add_comm] using h

#print axioms DirectMainOrdinary.ordinary_zero
#print axioms DirectMainOrdinary.old_ordinary_zero
#print axioms DirectMainOrdinary.old_ordinary_unit
end DirectMainOrdinary
