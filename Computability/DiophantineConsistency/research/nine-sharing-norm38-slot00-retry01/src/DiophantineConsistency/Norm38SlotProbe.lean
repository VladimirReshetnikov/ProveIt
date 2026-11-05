import DiophantineConsistency.SharingNormSquares
import DiophantineConsistency.NormAssignment38

/-! UNCOMPILED DRAFT. Exact slot-to-gate identities and conditional extraction.
Imports, tactic scripts and every theorem in this file are unverified. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38SlotExtraction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def residuals (p : Fin 4 → ℤ) : List (Expr (Fin 39)) :=
  SharingSeed38.firstResidual p :: SharingSeed38.remainingResiduals p

def residualAt (p : Fin 4 → ℤ) (i : Fin 29) : Expr (Fin 39) :=
  (residuals p).get ⟨i.val, by simpa [residuals, SharingSeed38.remainingResiduals] using i.isLt⟩

/-- Slot 0: q2 / positive. -/
theorem slot00 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 0).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; positiveResidual ι GateOp.mul (v 22) (v 22) (v 23)) := by
  have h15 : (Fin.cons (1 : V) w : Fin 39 → V) 15 = w 14 := by
    simpa only [] using (Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (14 : Fin 38))
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul, h15] <;> ring


end DiophantineConsistency.Norm38SlotExtraction
