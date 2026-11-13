import DiophantineConsistency.Norm38SlotsBase
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38SlotExtraction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Slot 9: c2 / positive. -/
theorem slot09 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 9).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; positiveResidual ι GateOp.mul (v 31) (v 31) (v 41)) := by
  have h11 : (Fin.cons (1 : V) w : Fin 39 → V) 11 = w 10 := by
    have hindex : (10 : Fin 38).succ = (11 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (10 : Fin 38)
  have h20 : (Fin.cons (1 : V) w : Fin 39 → V) 20 = w 19 := by
    have hindex : (19 : Fin 38).succ = (20 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (19 : Fin 38)
  have h24 : (Fin.cons (1 : V) w : Fin 39 → V) 24 = w 23 := by
    have hindex : (23 : Fin 38).succ = (24 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (23 : Fin 38)
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul, h11, h20, h24] <;> ring

/-- Slot 10: Dc2 / positive. -/
theorem slot10 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 10).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; positiveResidual ι GateOp.mul (v 36) (v 41) (v 42)) := by
  have h22 : (Fin.cons (1 : V) w : Fin 39 → V) 22 = w 21 := by
    have hindex : (21 : Fin 38).succ = (22 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (21 : Fin 38)
  have h24 : (Fin.cons (1 : V) w : Fin 39 → V) 24 = w 23 := by
    have hindex : (23 : Fin 38).succ = (24 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (23 : Fin 38)
  have h25 : (Fin.cons (1 : V) w : Fin 39 → V) 25 = w 24 := by
    have hindex : (24 : Fin 38).succ = (25 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (24 : Fin 38)
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul, h22, h24, h25] <;> ring

/-- Slot 11: N1 / norm. -/
theorem slot11 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 11).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; pairValue ι (v 44) - 1) := by
  have h23 : (Fin.cons (1 : V) w : Fin 39 → V) 23 = w 22 := by
    have hindex : (22 : Fin 38).succ = (23 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (22 : Fin 38)
  have h25 : (Fin.cons (1 : V) w : Fin 39 → V) 25 = w 24 := by
    have hindex : (24 : Fin 38).succ = (25 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (24 : Fin 38)
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul, h23, h25] <;> ring


end DiophantineConsistency.Norm38SlotExtraction
