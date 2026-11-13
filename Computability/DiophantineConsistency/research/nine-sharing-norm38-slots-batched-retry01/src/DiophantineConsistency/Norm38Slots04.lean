import DiophantineConsistency.Norm38SlotsBase
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38SlotExtraction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Slot 12: gap / positive. -/
theorem slot12 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 12).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; positiveResidual ι GateOp.add (v 47) (v 2) (v 48)) := by
  have h01 : (Fin.cons (1 : V) w : Fin 39 → V) 1 = w 0 := by
    have hindex : (0 : Fin 38).succ = (1 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (0 : Fin 38)
  have h03 : (Fin.cons (1 : V) w : Fin 39 → V) 3 = w 2 := by
    have hindex : (2 : Fin 38).succ = (3 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (2 : Fin 38)
  have h26 : (Fin.cons (1 : V) w : Fin 39 → V) 26 = w 25 := by
    have hindex : (25 : Fin 38).succ = (26 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (25 : Fin 38)
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul, map_ofNat, h01, h03, h26] <;> ring

/-- Slot 13: gap / negative. -/
theorem slot13 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 13).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; negativeResidual ι GateOp.add (v 47) (v 2) (v 48)) := by
  have h01 : (Fin.cons (1 : V) w : Fin 39 → V) 1 = w 0 := by
    have hindex : (0 : Fin 38).succ = (1 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (0 : Fin 38)
  have h02 : (Fin.cons (1 : V) w : Fin 39 → V) 2 = w 1 := by
    have hindex : (1 : Fin 38).succ = (2 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (1 : Fin 38)
  have h27 : (Fin.cons (1 : V) w : Fin 39 → V) 27 = w 26 := by
    have hindex : (26 : Fin 38).succ = (27 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (26 : Fin 38)
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul, map_ofNat, h01, h02, h27] <;> ring

/-- Slot 14: tau / positive. -/
theorem slot14 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 14).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; positiveResidual ι GateOp.sub (v 56) (v 54) (v 57)) := by
  have h10 : (Fin.cons (1 : V) w : Fin 39 → V) 10 = w 9 := by
    have hindex : (9 : Fin 38).succ = (10 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (9 : Fin 38)
  have h11 : (Fin.cons (1 : V) w : Fin 39 → V) 11 = w 10 := by
    have hindex : (10 : Fin 38).succ = (11 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (10 : Fin 38)
  have h12 : (Fin.cons (1 : V) w : Fin 39 → V) 12 = w 11 := by
    have hindex : (11 : Fin 38).succ = (12 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (11 : Fin 38)
  have h15 : (Fin.cons (1 : V) w : Fin 39 → V) 15 = w 14 := by
    have hindex : (14 : Fin 38).succ = (15 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (14 : Fin 38)
  have h19 : (Fin.cons (1 : V) w : Fin 39 → V) 19 = w 18 := by
    have hindex : (18 : Fin 38).succ = (19 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (18 : Fin 38)
  have h26 : (Fin.cons (1 : V) w : Fin 39 → V) 26 = w 25 := by
    have hindex : (25 : Fin 38).succ = (26 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (25 : Fin 38)
  have h27 : (Fin.cons (1 : V) w : Fin 39 → V) 27 = w 26 := by
    have hindex : (26 : Fin 38).succ = (27 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (26 : Fin 38)
  have h28 : (Fin.cons (1 : V) w : Fin 39 → V) 28 = w 27 := by
    have hindex : (27 : Fin 38).succ = (28 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (27 : Fin 38)
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul, map_ofNat, h10, h11, h12, h15, h19, h26, h27, h28] <;> ring


end DiophantineConsistency.Norm38SlotExtraction
