import DiophantineConsistency.Norm38SlotsBase
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38SlotExtraction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Slot 18: f2 / positive. -/
theorem slot18 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 18).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; positiveResidual ι GateOp.mul (v 4) (v 4) (v 67)) := by
  have h05 : (Fin.cons (1 : V) w : Fin 39 → V) 5 = w 4 := by
    have hindex : (4 : Fin 38).succ = (5 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (4 : Fin 38)
  have h30 : (Fin.cons (1 : V) w : Fin 39 → V) 30 = w 29 := by
    have hindex : (29 : Fin 38).succ = (30 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (29 : Fin 38)
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul, h05, h30] <;> ring

/-- Slot 19: cTminusR / positive. -/
theorem slot19 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 19).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; positiveResidual ι GateOp.sub (v 68) (v 54) (v 69)) := by
  have h07 : (Fin.cons (1 : V) w : Fin 39 → V) 7 = w 6 := by
    have hindex : (6 : Fin 38).succ = (7 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (6 : Fin 38)
  have h11 : (Fin.cons (1 : V) w : Fin 39 → V) 11 = w 10 := by
    have hindex : (10 : Fin 38).succ = (11 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (10 : Fin 38)
  have h15 : (Fin.cons (1 : V) w : Fin 39 → V) 15 = w 14 := by
    have hindex : (14 : Fin 38).succ = (15 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (14 : Fin 38)
  have h20 : (Fin.cons (1 : V) w : Fin 39 → V) 20 = w 19 := by
    have hindex : (19 : Fin 38).succ = (20 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (19 : Fin 38)
  have h26 : (Fin.cons (1 : V) w : Fin 39 → V) 26 = w 25 := by
    have hindex : (25 : Fin 38).succ = (26 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (25 : Fin 38)
  have h27 : (Fin.cons (1 : V) w : Fin 39 → V) 27 = w 26 := by
    have hindex : (26 : Fin 38).succ = (27 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (26 : Fin 38)
  have h31 : (Fin.cons (1 : V) w : Fin 39 → V) 31 = w 30 := by
    have hindex : (30 : Fin 38).succ = (31 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (30 : Fin 38)
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul, h07, h11, h15, h20, h26, h27, h31] <;> ring

/-- Slot 20: cTminusR / negative. -/
theorem slot20 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 20).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; negativeResidual ι GateOp.sub (v 68) (v 54) (v 69)) := by
  have h01 : (Fin.cons (1 : V) w : Fin 39 → V) 1 = w 0 := by
    have hindex : (0 : Fin 38).succ = (1 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (0 : Fin 38)
  have h15 : (Fin.cons (1 : V) w : Fin 39 → V) 15 = w 14 := by
    have hindex : (14 : Fin 38).succ = (15 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (14 : Fin 38)
  have h26 : (Fin.cons (1 : V) w : Fin 39 → V) 26 = w 25 := by
    have hindex : (25 : Fin 38).succ = (26 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (25 : Fin 38)
  have h27 : (Fin.cons (1 : V) w : Fin 39 → V) 27 = w 26 := by
    have hindex : (26 : Fin 38).succ = (27 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (26 : Fin 38)
  have h32 : (Fin.cons (1 : V) w : Fin 39 → V) 32 = w 31 := by
    have hindex : (31 : Fin 38).succ = (32 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (31 : Fin 38)
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul, h01, h15, h26, h27, h32] <;> ring


end DiophantineConsistency.Norm38SlotExtraction
