import FreeJCompletenessFactorBridge
import DiophantineConsistency.ModelDifferenceRing

/-! Same-valuation bridge for a five-operation residual-square tail. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace FreeJSumSquares
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs Ordinary12FreeJ ModelDifferenceRing
open ArithmeticAdaptiveFactorMagnitude2011

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def rightAdd {σ : Type*} : Expr σ → Expr σ
  | .add _ b => b
  | _ => 0

def firstResidual (p : Fin 4 → ℤ) : Expr (Fin 12) := rightAdd (core p).first
def mainResidual (p : Fin 4 → ℤ) : Expr (Fin 12) := rightAdd (core p).main
def ordinaryResidual (p : Fin 4 → ℤ) : Expr (Fin 12) := rightAdd (core p).ordinary

theorem first_decompose (p : Fin 4 → ℤ) : (core p).first = 1 + firstResidual p := by rfl
theorem main_decompose (p : Fin 4 → ℤ) : (core p).main = 1 + mainResidual p := by rfl
theorem ordinary_decompose (p : Fin 4 → ℤ) : (core p).ordinary = 1 + ordinaryResidual p := by rfl

def squareLiteral (p : Fin 4 → ℤ) : Expr (Fin 12) :=
  let a := firstResidual p
  let b := mainResidual p
  let c := ordinaryResidual p
  a*a + b*b + c*c

private theorem unit_iff_zero {σ : Type*} (e : Expr σ) (v : σ → V) :
    (pairEval (1+e) v).1 = (pairEval (1+e) v).2+1 ↔ InternalZero e v := by
  simp [pairEval, Expr.splitNatural, NatExpr.evalSemiring, InternalZero,
    add_comm, add_left_comm, add_assoc]

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

/-- Same valuation, all IΣ₁ models. No positivity assumption on the valuation. -/
theorem zero_iff_literal (p : Fin 4 → ℤ) (v : Fin 12 → V) :
    InternalZero (squareLiteral p) v ↔ InternalZero (literal p) v := by
  rw [squareLiteral, three_squares_iff, FreeJCompletenessFactorBridge.zero_iff_factor_units,
      first_decompose, main_decompose, ordinary_decompose]
  simp only [unit_iff_zero]

#print axioms FreeJSumSquares.zero_iff_literal
end FreeJSumSquares
