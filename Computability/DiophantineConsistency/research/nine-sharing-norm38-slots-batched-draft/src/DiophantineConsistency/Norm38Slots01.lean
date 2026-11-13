import DiophantineConsistency.Norm38SlotsBase
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38SlotExtraction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Slot 3: Y / positive. -/
theorem slot03 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 3).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; positiveResidual ι GateOp.mul (v 7) (v 24) (v 26)) := by
  have h08 : (Fin.cons (1 : V) w : Fin 39 → V) 8 = w 7 := by
    have hindex : (7 : Fin 38).succ = (8 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (7 : Fin 38)
  have h16 : (Fin.cons (1 : V) w : Fin 39 → V) 16 = w 15 := by
    have hindex : (15 : Fin 38).succ = (16 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (15 : Fin 38)
  have h18 : (Fin.cons (1 : V) w : Fin 39 → V) 18 = w 17 := by
    have hindex : (17 : Fin 38).succ = (18 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (17 : Fin 38)
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul, h08, h16, h18] <;> ring

/-- Slot 4: E / positive. -/
theorem slot04 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 4).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; positiveResidual ι GateOp.mul (v 25) (v 26) (v 27)) := by
  have h17 : (Fin.cons (1 : V) w : Fin 39 → V) 17 = w 16 := by
    have hindex : (16 : Fin 38).succ = (17 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (16 : Fin 38)
  have h18 : (Fin.cons (1 : V) w : Fin 39 → V) 18 = w 17 := by
    have hindex : (17 : Fin 38).succ = (18 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (17 : Fin 38)
  have h19 : (Fin.cons (1 : V) w : Fin 39 → V) 19 = w 18 := by
    have hindex : (18 : Fin 38).succ = (19 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (18 : Fin 38)
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul, h17, h18, h19] <;> ring

/-- Slot 5: kY / positive. -/
theorem slot05 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 5).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; positiveResidual ι GateOp.mul (v 28) (v 26) (v 29)) := by
  have h11 : (Fin.cons (1 : V) w : Fin 39 → V) 11 = w 10 := by
    have hindex : (10 : Fin 38).succ = (11 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (10 : Fin 38)
  have h12 : (Fin.cons (1 : V) w : Fin 39 → V) 12 = w 11 := by
    have hindex : (11 : Fin 38).succ = (12 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (11 : Fin 38)
  have h18 : (Fin.cons (1 : V) w : Fin 39 → V) 18 = w 17 := by
    have hindex : (17 : Fin 38).succ = (18 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (17 : Fin 38)
  have h20 : (Fin.cons (1 : V) w : Fin 39 → V) 20 = w 19 := by
    have hindex : (19 : Fin 38).succ = (20 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (19 : Fin 38)
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul, h11, h12, h18, h20] <;> ring


end DiophantineConsistency.Norm38SlotExtraction
