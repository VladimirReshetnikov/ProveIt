import DiophantineConsistency.Compact44.QCube92

/-! A model-level comparison at the transformed valuation; no quotient
existence or file/TeX binding is asserted by this module. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace FreeJQCube92Model
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ModelDifferenceRing
open FreeJQCube92

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def integerPorts (p : Fin 4 → ℕ) : Fin 4 → ℤ := fun i => (p i : ℤ)

def transform (p : Fin 4 → ℕ) (v : Fin 12 → V) : Fin 12 → V :=
  let q := 1 + v 0 * (p 0 : V)
  Function.update v 6 (q * (q * q) * v 6)

theorem lift_cast (p : Fin 4 → ℕ) (v : Fin 12 → V) :
    (fun i => ι (transform p v i)) =
      lift (integerPorts p) (fun i => ι (v i)) := by
  funext i
  by_cases h : i = 6
  · subst i
    simp [transform, lift, qcube, integerPorts, map_add, map_mul, Int.cast_natCast]
  · simp [transform, lift, h]

theorem cube_ne_zero (p : Fin 4 → ℕ) (v : Fin 12 → V) :
    qcube (integerPorts p) (fun i => ι (v i)) ≠ 0 := by
  have hv : (0 : DiffRing V) ≤ ι (v 0) := ι_nonneg _
  have hp : (0 : DiffRing V) ≤ ((p 0 : ℕ) : DiffRing V) := by positivity
  have hq : (0 : DiffRing V) < 1 + ι (v 0) * ((p 0 : ℕ) : DiffRing V) := by positivity
  simp only [qcube, integerPorts, Int.cast_natCast]
  exact mul_ne_zero hq.ne' (mul_ne_zero hq.ne' hq.ne')

private theorem three_squares_iff {σ : Type*} (a b c : Expr σ) (v : σ → V) :
    InternalZero (a*a+b*b+c*c) v ↔ InternalZero a v ∧ InternalZero b v ∧ InternalZero c v := by
  rw [internalZero_iff, internalZero_iff, internalZero_iff, internalZero_iff]
  simp only [Expr.evalRing_add, Expr.evalRing_mul]
  constructor
  · intro h
    have ha := sq_nonneg (a.evalRing fun j => ι (v j))
    have hb := sq_nonneg (b.evalRing fun j => ι (v j))
    have hc := sq_nonneg (c.evalRing fun j => ι (v j))
    have ha0 : a.evalRing (fun j => ι (v j)) * a.evalRing (fun j => ι (v j)) = 0 := by nlinarith
    have hb0 : b.evalRing (fun j => ι (v j)) * b.evalRing (fun j => ι (v j)) = 0 := by nlinarith
    have hc0 : c.evalRing (fun j => ι (v j)) * c.evalRing (fun j => ι (v j)) = 0 := by nlinarith
    exact ⟨mul_self_eq_zero.mp ha0, mul_self_eq_zero.mp hb0, mul_self_eq_zero.mp hc0⟩
  · rintro ⟨ha,hb,hc⟩
    rw [ha,hb,hc]
    simp

theorem zero_iff_transformed (p : Fin 4 → ℕ) (v : Fin 12 → V) :
    InternalZero (graph (integerPorts p)).output v ↔
      InternalZero (FreeJSumSquares.squareLiteral (integerPorts p)) (transform p v) := by
  let a := (graph (integerPorts p)).first
  let b := (graph (integerPorts p)).main
  let c := (graph (integerPorts p)).ordinary
  have hout : (graph (integerPorts p)).output = a*a+b*b+c*c := by rfl
  have hsquare : FreeJSumSquares.squareLiteral (integerPorts p) =
      FreeJSumSquares.firstResidual (integerPorts p) * FreeJSumSquares.firstResidual (integerPorts p) +
      FreeJSumSquares.mainResidual (integerPorts p) * FreeJSumSquares.mainResidual (integerPorts p) +
      FreeJSumSquares.ordinaryResidual (integerPorts p) * FreeJSumSquares.ordinaryResidual (integerPorts p) := by rfl
  rw [hout, three_squares_iff, hsquare, three_squares_iff]
  simp only [internalZero_iff]
  rw [lift_cast, first_eval, main_eval, ordinary_eval]
  simp only [mul_eq_zero, cube_ne_zero, false_or]
  rfl

#print axioms FreeJQCube92Model.lift_cast
#print axioms FreeJQCube92Model.cube_ne_zero
#print axioms FreeJQCube92Model.zero_iff_transformed
end FreeJQCube92Model
