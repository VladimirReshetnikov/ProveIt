import DiophantineConsistency.Norm38SlotsBase
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38SlotExtraction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Slot 21: V / positive. -/
theorem slot21 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 21).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; positiveResidual ι GateOp.sub (v 70) (v 31) (v 71)) := by
  have h30 : (Fin.cons (1 : V) w : Fin 39 → V) 30 = w 29 := by
    have hindex : (29 : Fin 38).succ = (30 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (29 : Fin 38)
  have h31 : (Fin.cons (1 : V) w : Fin 39 → V) 31 = w 30 := by
    have hindex : (30 : Fin 38).succ = (31 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (30 : Fin 38)
  have h33 : (Fin.cons (1 : V) w : Fin 39 → V) 33 = w 32 := by
    have hindex : (32 : Fin 38).succ = (33 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (32 : Fin 38)
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul, h30, h31, h33] <;> ring

/-- Slot 22: V / negative. -/
theorem slot22 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 22).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; negativeResidual ι GateOp.sub (v 70) (v 31) (v 71)) := by
  have h11 : (Fin.cons (1 : V) w : Fin 39 → V) 11 = w 10 := by
    have hindex : (10 : Fin 38).succ = (11 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (10 : Fin 38)
  have h20 : (Fin.cons (1 : V) w : Fin 39 → V) 20 = w 19 := by
    have hindex : (19 : Fin 38).succ = (20 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (19 : Fin 38)
  have h30 : (Fin.cons (1 : V) w : Fin 39 → V) 30 = w 29 := by
    have hindex : (29 : Fin 38).succ = (30 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (29 : Fin 38)
  have h32 : (Fin.cons (1 : V) w : Fin 39 → V) 32 = w 31 := by
    have hindex : (31 : Fin 38).succ = (32 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (31 : Fin 38)
  have h34 : (Fin.cons (1 : V) w : Fin 39 → V) 34 = w 33 := by
    have hindex : (33 : Fin 38).succ = (34 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (33 : Fin 38)
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul, h11, h20, h30, h32, h34] <;> ring

/-- Slot 23: normalized_S / positive. -/
theorem slot23 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 23).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; positiveResidual ι GateOp.mul (v 5) (v 42) (v 72)) := by
  have h06 : (Fin.cons (1 : V) w : Fin 39 → V) 6 = w 5 := by
    have hindex : (5 : Fin 38).succ = (6 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (5 : Fin 38)
  have h25 : (Fin.cons (1 : V) w : Fin 39 → V) 25 = w 24 := by
    have hindex : (24 : Fin 38).succ = (25 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (24 : Fin 38)
  have h35 : (Fin.cons (1 : V) w : Fin 39 → V) 35 = w 34 := by
    have hindex : (34 : Fin 38).succ = (35 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (34 : Fin 38)
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul, h06, h25, h35] <;> ring


end DiophantineConsistency.Norm38SlotExtraction
