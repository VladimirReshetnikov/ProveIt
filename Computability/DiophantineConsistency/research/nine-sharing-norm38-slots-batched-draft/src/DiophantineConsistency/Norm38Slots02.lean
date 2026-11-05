import DiophantineConsistency.Norm38SlotsBase
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38SlotExtraction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Slot 6: ell / positive. -/
theorem slot06 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 6).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; positiveResidual ι GateOp.mul (v 27) (v 29) (v 30)) := by
  have h19 : (Fin.cons (1 : V) w : Fin 39 → V) 19 = w 18 := by
    have hindex : (18 : Fin 38).succ = (19 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (18 : Fin 38)
  have h20 : (Fin.cons (1 : V) w : Fin 39 → V) 20 = w 19 := by
    have hindex : (19 : Fin 38).succ = (20 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (19 : Fin 38)
  have h21 : (Fin.cons (1 : V) w : Fin 39 → V) 21 = w 20 := by
    have hindex : (20 : Fin 38).succ = (21 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (20 : Fin 38)
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul, h19, h20, h21] <;> ring

/-- Slot 7: Delta / positive. -/
theorem slot07 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 7).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; positiveResidual ι GateOp.add (v 35) (v 34) (v 36)) := by
  have h18 : (Fin.cons (1 : V) w : Fin 39 → V) 18 = w 17 := by
    have hindex : (17 : Fin 38).succ = (18 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (17 : Fin 38)
  have h19 : (Fin.cons (1 : V) w : Fin 39 → V) 19 = w 18 := by
    have hindex : (18 : Fin 38).succ = (19 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (18 : Fin 38)
  have h22 : (Fin.cons (1 : V) w : Fin 39 → V) 22 = w 21 := by
    have hindex : (21 : Fin 38).succ = (22 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (21 : Fin 38)
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul, h18, h19, h22] <;> ring

/-- Slot 8: main_root / positive. -/
theorem slot08 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 8).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; positiveResidual ι GateOp.add (v 38) (v 39) (v 40)) := by
  have h11 : (Fin.cons (1 : V) w : Fin 39 → V) 11 = w 10 := by
    have hindex : (10 : Fin 38).succ = (11 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (10 : Fin 38)
  have h14 : (Fin.cons (1 : V) w : Fin 39 → V) 14 = w 13 := by
    have hindex : (13 : Fin 38).succ = (14 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (13 : Fin 38)
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
  have h20 : (Fin.cons (1 : V) w : Fin 39 → V) 20 = w 19 := by
    have hindex : (19 : Fin 38).succ = (20 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (19 : Fin 38)
  have h23 : (Fin.cons (1 : V) w : Fin 39 → V) 23 = w 22 := by
    have hindex : (22 : Fin 38).succ = (23 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (22 : Fin 38)
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul, h11, h14, h17, h18, h19, h20, h23] <;> ring


end DiophantineConsistency.Norm38SlotExtraction
