import DiophantineConsistency.Norm38SlotsBase
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38SlotExtraction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Slot 24: normalized_S2 / positive. -/
theorem slot24 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 24).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; positiveResidual ι GateOp.mul (v 72) (v 72) (v 73)) := by
  have h35 : (Fin.cons (1 : V) w : Fin 39 → V) 35 = w 34 := by
    have hindex : (34 : Fin 38).succ = (35 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (34 : Fin 38)
  have h36 : (Fin.cons (1 : V) w : Fin 39 → V) 36 = w 35 := by
    have hindex : (35 : Fin 38).succ = (36 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (35 : Fin 38)
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul, map_ofNat, h35, h36] <;> ring

/-- Slot 25: V2minusY2 / positive. -/
theorem slot25 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 25).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; positiveResidual ι GateOp.sub (v 74) (v 75) (v 76)) := by
  have h33 : (Fin.cons (1 : V) w : Fin 39 → V) 33 = w 32 := by
    have hindex : (32 : Fin 38).succ = (33 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (32 : Fin 38)
  have h34 : (Fin.cons (1 : V) w : Fin 39 → V) 34 = w 33 := by
    have hindex : (33 : Fin 38).succ = (34 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (33 : Fin 38)
  have h37 : (Fin.cons (1 : V) w : Fin 39 → V) 37 = w 36 := by
    have hindex : (36 : Fin 38).succ = (37 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (36 : Fin 38)
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul, map_ofNat, h33, h34, h37] <;> ring

/-- Slot 26: V2minusY2 / negative. -/
theorem slot26 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 26).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; negativeResidual ι GateOp.sub (v 74) (v 75) (v 76)) := by
  have h13 : (Fin.cons (1 : V) w : Fin 39 → V) 13 = w 12 := by
    have hindex : (12 : Fin 38).succ = (13 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (12 : Fin 38)
  have h33 : (Fin.cons (1 : V) w : Fin 39 → V) 33 = w 32 := by
    have hindex : (32 : Fin 38).succ = (33 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (32 : Fin 38)
  have h34 : (Fin.cons (1 : V) w : Fin 39 → V) 34 = w 33 := by
    have hindex : (33 : Fin 38).succ = (34 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (33 : Fin 38)
  have h38 : (Fin.cons (1 : V) w : Fin 39 → V) 38 = w 37 := by
    have hindex : (37 : Fin 38).succ = (38 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (37 : Fin 38)
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul, map_ofNat, h13, h33, h34, h38] <;> ring


end DiophantineConsistency.Norm38SlotExtraction
