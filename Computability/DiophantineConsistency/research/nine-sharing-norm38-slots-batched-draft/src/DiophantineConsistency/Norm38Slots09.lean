import DiophantineConsistency.Norm38SlotsBase
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.Norm38SlotExtraction
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 SharingGateModel
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Slot 27: Na / norm. -/
theorem slot27 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 27).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; pairValue ι (v 78) - 1) := by
  have h13 : (Fin.cons (1 : V) w : Fin 39 → V) 13 = w 12 := by
    have hindex : (12 : Fin 38).succ = (13 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (12 : Fin 38)
  have h36 : (Fin.cons (1 : V) w : Fin 39 → V) 36 = w 35 := by
    have hindex : (35 : Fin 38).succ = (36 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (35 : Fin 38)
  have h37 : (Fin.cons (1 : V) w : Fin 39 → V) 37 = w 36 := by
    have hindex : (36 : Fin 38).succ = (37 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (36 : Fin 38)
  have h38 : (Fin.cons (1 : V) w : Fin 39 → V) 38 = w 37 := by
    have hindex : (37 : Fin 38).succ = (38 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (37 : Fin 38)
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul, h13, h36, h37, h38] <;> ring

/-- Slot 28: scaled_Ns / norm. -/
theorem slot28 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 28).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; pairValue ι (v 80) - pairValue ι (v 36)) := by
  have h22 : (Fin.cons (1 : V) w : Fin 39 → V) 22 = w 21 := by
    have hindex : (21 : Fin 38).succ = (22 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (21 : Fin 38)
  have h30 : (Fin.cons (1 : V) w : Fin 39 → V) 30 = w 29 := by
    have hindex : (29 : Fin 38).succ = (30 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (29 : Fin 38)
  have h36 : (Fin.cons (1 : V) w : Fin 39 → V) 36 = w 35 := by
    have hindex : (35 : Fin 38).succ = (36 : Fin 39) := by decide
    rw [← hindex]
    exact Fin.cons_succ (α := fun _ : Fin 39 => V) (1 : V) w (35 : Fin 38)
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul, h22, h30, h36] <;> ring


end DiophantineConsistency.Norm38SlotExtraction
