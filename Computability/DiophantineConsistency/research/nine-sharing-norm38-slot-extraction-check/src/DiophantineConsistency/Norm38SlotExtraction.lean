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
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul] <;> ring

/-- Slot 1: q3 / positive. -/
theorem slot01 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 1).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; positiveResidual ι GateOp.mul (v 23) (v 22) (v 24)) := by
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul] <;> ring

/-- Slot 2: X / positive. -/
theorem slot02 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 2).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; positiveResidual ι GateOp.mul (v 8) (v 22) (v 25)) := by
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul] <;> ring

/-- Slot 3: Y / positive. -/
theorem slot03 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 3).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; positiveResidual ι GateOp.mul (v 7) (v 24) (v 26)) := by
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul] <;> ring

/-- Slot 4: E / positive. -/
theorem slot04 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 4).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; positiveResidual ι GateOp.mul (v 25) (v 26) (v 27)) := by
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul] <;> ring

/-- Slot 5: kY / positive. -/
theorem slot05 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 5).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; positiveResidual ι GateOp.mul (v 28) (v 26) (v 29)) := by
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul] <;> ring

/-- Slot 6: ell / positive. -/
theorem slot06 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 6).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; positiveResidual ι GateOp.mul (v 27) (v 29) (v 30)) := by
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul] <;> ring

/-- Slot 7: Delta / positive. -/
theorem slot07 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 7).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; positiveResidual ι GateOp.add (v 35) (v 34) (v 36)) := by
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul] <;> ring

/-- Slot 8: main_root / positive. -/
theorem slot08 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 8).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; positiveResidual ι GateOp.add (v 38) (v 39) (v 40)) := by
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul] <;> ring

/-- Slot 9: c2 / positive. -/
theorem slot09 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 9).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; positiveResidual ι GateOp.mul (v 31) (v 31) (v 41)) := by
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul] <;> ring

/-- Slot 10: Dc2 / positive. -/
theorem slot10 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 10).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; positiveResidual ι GateOp.mul (v 36) (v 41) (v 42)) := by
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul] <;> ring

/-- Slot 11: N1 / norm. -/
theorem slot11 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 11).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; pairValue ι (v 44) - 1) := by
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul] <;> ring

/-- Slot 12: gap / positive. -/
theorem slot12 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 12).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; positiveResidual ι GateOp.add (v 47) (v 2) (v 48)) := by
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul] <;> ring

/-- Slot 13: gap / negative. -/
theorem slot13 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 13).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; negativeResidual ι GateOp.add (v 47) (v 2) (v 48)) := by
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul] <;> ring

/-- Slot 14: tau / positive. -/
theorem slot14 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 14).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; positiveResidual ι GateOp.sub (v 56) (v 54) (v 57)) := by
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul] <;> ring

/-- Slot 15: tau / negative. -/
theorem slot15 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 15).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; negativeResidual ι GateOp.sub (v 56) (v 54) (v 57)) := by
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul] <;> ring

/-- Slot 16: N0 / norm. -/
theorem slot16 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 16).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; pairValue ι (v 61) - 1) := by
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul] <;> ring

/-- Slot 17: Nt / norm. -/
theorem slot17 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 17).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; pairValue ι (v 66) - 1) := by
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul] <;> ring

/-- Slot 18: f2 / positive. -/
theorem slot18 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 18).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; positiveResidual ι GateOp.mul (v 4) (v 4) (v 67)) := by
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul] <;> ring

/-- Slot 19: cTminusR / positive. -/
theorem slot19 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 19).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; positiveResidual ι GateOp.sub (v 68) (v 54) (v 69)) := by
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul] <;> ring

/-- Slot 20: cTminusR / negative. -/
theorem slot20 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 20).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; negativeResidual ι GateOp.sub (v 68) (v 54) (v 69)) := by
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul] <;> ring

/-- Slot 21: V / positive. -/
theorem slot21 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 21).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; positiveResidual ι GateOp.sub (v 70) (v 31) (v 71)) := by
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul] <;> ring

/-- Slot 22: V / negative. -/
theorem slot22 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 22).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; negativeResidual ι GateOp.sub (v 70) (v 31) (v 71)) := by
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul] <;> ring

/-- Slot 23: normalized_S / positive. -/
theorem slot23 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 23).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; positiveResidual ι GateOp.mul (v 5) (v 42) (v 72)) := by
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul] <;> ring

/-- Slot 24: normalized_S2 / positive. -/
theorem slot24 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 24).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; positiveResidual ι GateOp.mul (v 72) (v 72) (v 73)) := by
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul] <;> ring

/-- Slot 25: V2minusY2 / positive. -/
theorem slot25 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 25).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; positiveResidual ι GateOp.sub (v 74) (v 75) (v 76)) := by
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul] <;> ring

/-- Slot 26: V2minusY2 / negative. -/
theorem slot26 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 26).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; negativeResidual ι GateOp.sub (v 74) (v 75) (v 76)) := by
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul] <;> ring

/-- Slot 27: Na / norm. -/
theorem slot27 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 27).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; pairValue ι (v 78) - 1) := by
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul] <;> ring

/-- Slot 28: scaled_Ns / norm. -/
theorem slot28 (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j)) :
    (residualAt p 28).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) =
      (let v := NormAssignment38.assignment ports w; pairValue ι (v 80) - pairValue ι (v 36)) := by
  simp [residualAt, residuals, SharingSeed38.firstResidual,
    SharingSeed38.remainingResiduals, NormAssignment38.assignment,
    positiveResidual, negativeResidual, pairValue, pairCompute,
    Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var,
    Expr.evalRing_constant, hp, map_add, map_mul] <;> ring

/-- The sum-of-squares theorem supplies a zero at each indexed slot. -/
theorem each_slot_zero (p : Fin 4 → ℤ) (w : Fin 38 → V)
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w))
    (i : Fin 29) : (residualAt p i).evalRing (fun j => ι ((Fin.cons (1 : V) w) j)) = 0 := by
  have all := (SharingNormSquares.seed_zero_iff_residuals p (Fin.cons (1 : V) w)).mp hz
  have hm : residualAt p i ∈ residuals p := List.get_mem _ _
  exact (internalZero_iff.mp (all _ hm))

/-- Proposed extraction from the 29 literal equalities to the static graph
constraints. It is not a source-expression identification or model bridge. -/
theorem seed_zero_static (p : Fin 4 → ℤ) (ports : Fin 4 → V) (w : Fin 38 → V)
    (hp : ∀ j, ((p j : ℤ) : DiffRing V) = ι (ports j))
    (hz : InternalZero (SharingSeed38.seed p) (Fin.cons (1 : V) w)) :
    NormAssignment38.gatesHold ι ports w ∧ NormAssignment38.fiveNorms ι ports w := by
  have h00 := each_slot_zero p w hz 0
  rw [slot00 p ports w hp] at h00
  have h01 := each_slot_zero p w hz 1
  rw [slot01 p ports w hp] at h01
  have h02 := each_slot_zero p w hz 2
  rw [slot02 p ports w hp] at h02
  have h03 := each_slot_zero p w hz 3
  rw [slot03 p ports w hp] at h03
  have h04 := each_slot_zero p w hz 4
  rw [slot04 p ports w hp] at h04
  have h05 := each_slot_zero p w hz 5
  rw [slot05 p ports w hp] at h05
  have h06 := each_slot_zero p w hz 6
  rw [slot06 p ports w hp] at h06
  have h07 := each_slot_zero p w hz 7
  rw [slot07 p ports w hp] at h07
  have h08 := each_slot_zero p w hz 8
  rw [slot08 p ports w hp] at h08
  have h09 := each_slot_zero p w hz 9
  rw [slot09 p ports w hp] at h09
  have h10 := each_slot_zero p w hz 10
  rw [slot10 p ports w hp] at h10
  have h11 := each_slot_zero p w hz 11
  rw [slot11 p ports w hp] at h11
  have h12 := each_slot_zero p w hz 12
  rw [slot12 p ports w hp] at h12
  have h13 := each_slot_zero p w hz 13
  rw [slot13 p ports w hp] at h13
  have h14 := each_slot_zero p w hz 14
  rw [slot14 p ports w hp] at h14
  have h15 := each_slot_zero p w hz 15
  rw [slot15 p ports w hp] at h15
  have h16 := each_slot_zero p w hz 16
  rw [slot16 p ports w hp] at h16
  have h17 := each_slot_zero p w hz 17
  rw [slot17 p ports w hp] at h17
  have h18 := each_slot_zero p w hz 18
  rw [slot18 p ports w hp] at h18
  have h19 := each_slot_zero p w hz 19
  rw [slot19 p ports w hp] at h19
  have h20 := each_slot_zero p w hz 20
  rw [slot20 p ports w hp] at h20
  have h21 := each_slot_zero p w hz 21
  rw [slot21 p ports w hp] at h21
  have h22 := each_slot_zero p w hz 22
  rw [slot22 p ports w hp] at h22
  have h23 := each_slot_zero p w hz 23
  rw [slot23 p ports w hp] at h23
  have h24 := each_slot_zero p w hz 24
  rw [slot24 p ports w hp] at h24
  have h25 := each_slot_zero p w hz 25
  rw [slot25 p ports w hp] at h25
  have h26 := each_slot_zero p w hz 26
  rw [slot26 p ports w hp] at h26
  have h27 := each_slot_zero p w hz 27
  rw [slot27 p ports w hp] at h27
  have h28 := each_slot_zero p w hz 28
  rw [slot28 p ports w hp] at h28
  constructor
  · unfold NormAssignment38.gatesHold
    simp only [NormAssignment38.gates, List.mem_cons, forall_eq_or_imp]
    repeat' constructor
    all_goals simp_all [NormAssignment38.assignment, positiveResidual, negativeResidual, pairCompute]
  · unfold NormAssignment38.fiveNorms
    exact ⟨sub_eq_zero.mp h16, sub_eq_zero.mp h11, sub_eq_zero.mp h27, sub_eq_zero.mp h17, sub_eq_zero.mp h28⟩

-- Remaining: compile and repair these statements; prove the static-to-source
-- topological evaluation, fixed-port casts, forward witness construction,
-- Jones instantiation and consistency transfer.
end DiophantineConsistency.Norm38SlotExtraction
