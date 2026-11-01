import DiophantineConsistency.AdaptiveSquareWitnessDirect14

/-! A finite list of signed residual squares vanishes exactly when every
residual vanishes, in every model of IΣ₁. This is a model-level lemma for
future quadratic-gate reductions, not an iPRA endpoint. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace DiophantineConsistency.InternalResidualSquares
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveSquareWitnessDirect14 AdaptiveDirectOrdinateSquareSums
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def squareSum {σ : Type*} : List (Expr σ) → Expr σ
  | [] => 0
  | e::es => e*e + squareSum es

def squareValue {σ : Type*} (v : σ → V) : List (Expr σ) → V
  | [] => 0
  | e::es => magnitude (pairEval e v)*magnitude (pairEval e v)+squareValue v es

theorem squareSum_rep {σ : Type*} (es : List (Expr σ)) (v : σ → V) :
    SignedRep (squareSum es) v (natural (squareValue v es)) := by
  induction es with
  | nil => exact rep_nat v 0
  | cons e es ih => exact rep_add_nat (rawSquare_rep e v) ih

theorem squareSum_zero_iff {σ : Type*} (es : List (Expr σ)) (v : σ → V) :
    InternalZero (squareSum es) v ↔ ∀ e ∈ es, InternalZero e v := by
  rw [rep_zero_iff (squareSum_rep es v)]
  induction es with
  | nil => simp [squareValue]
  | cons e es ih =>
    change (magnitude (pairEval e v)*magnitude (pairEval e v)+squareValue v es=0) ↔ _
    rw [sum_eq_zero_iff,mul_self_eq_zero,magnitude_zero_iff,ih]
    simp only [List.mem_cons,forall_eq_or_imp]
    rfl
end DiophantineConsistency.InternalResidualSquares
