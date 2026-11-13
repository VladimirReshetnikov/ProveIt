import DiophantineConsistency.Norm38SlotsBase
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38SlotExtraction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Slot 15: tau / negative. -/
theorem slot15 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 15).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; negativeResidual ι GateOp.sub (v 56) (v 54) (v 57)) := by
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
  have h29 : (Fin.cons (1 : V) w : Fin 39 → V) 29 = w 28 := by
    have hindex : (28 : Fin 38).succ = (29 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (28 : Fin 38)
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul, h01, h15, h26, h27, h29] <;> ring

/-- Slot 16: N0 / norm. -/
theorem slot16 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 16).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; pairValue ι (v 61) - 1) := by
  have h11 : (Fin.cons (1 : V) w : Fin 39 → V) 11 = w 10 := by
    have hindex : (10 : Fin 38).succ = (11 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (10 : Fin 38)
  have h12 : (Fin.cons (1 : V) w : Fin 39 → V) 12 = w 11 := by
    have hindex : (11 : Fin 38).succ = (12 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (11 : Fin 38)
  have h21 : (Fin.cons (1 : V) w : Fin 39 → V) 21 = w 20 := by
    have hindex : (20 : Fin 38).succ = (21 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (20 : Fin 38)
  have h28 : (Fin.cons (1 : V) w : Fin 39 → V) 28 = w 27 := by
    have hindex : (27 : Fin 38).succ = (28 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (27 : Fin 38)
  have h29 : (Fin.cons (1 : V) w : Fin 39 → V) 29 = w 28 := by
    have hindex : (28 : Fin 38).succ = (29 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (28 : Fin 38)
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul, h11, h12, h21, h28, h29] <;> ring

/-- Slot 17: Nt / norm. -/
theorem slot17 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 17).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; pairValue ι (v 66) - 1) := by
  have h01 : (Fin.cons (1 : V) w : Fin 39 → V) 1 = w 0 := by
    have hindex : (0 : Fin 38).succ = (1 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (0 : Fin 38)
  have h02 : (Fin.cons (1 : V) w : Fin 39 → V) 2 = w 1 := by
    have hindex : (1 : Fin 38).succ = (2 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (1 : Fin 38)
  have h03 : (Fin.cons (1 : V) w : Fin 39 → V) 3 = w 2 := by
    have hindex : (2 : Fin 38).succ = (3 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (2 : Fin 38)
  have h04 : (Fin.cons (1 : V) w : Fin 39 → V) 4 = w 3 := by
    have hindex : (3 : Fin 38).succ = (4 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (3 : Fin 38)
  have h09 : (Fin.cons (1 : V) w : Fin 39 → V) 9 = w 8 := by
    have hindex : (8 : Fin 38).succ = (9 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (8 : Fin 38)
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul, h01, h02, h03, h04, h09] <;> ring


end DiophantineConsistency.Norm38SlotExtraction
