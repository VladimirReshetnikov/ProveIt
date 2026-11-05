import DiophantineConsistency.SharingSeed38

/-! UNCOMPILED DRAFT. Extract individual residual zeros from the sum of
squares in a model difference ring. No all-model bridge is claimed. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.SharingNormSquares
open LO LO.FirstOrder LO.FirstOrder.Arithmetic ModelDifferenceRing ModelArithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def squareSum {σ : Type*} : List (Expr σ) → Expr σ
  | [] => 0
  | e :: es => e * e + squareSum es

theorem squareSum_nonneg {σ : Type*} (es : List (Expr σ)) (v : σ → V) :
    0 ≤ (squareSum es).evalRing (fun i => ι (v i)) := by
  induction es with
  | nil => simp [squareSum, Expr.evalRing_ofNat]
  | cons e es ih =>
    simp only [squareSum, Expr.evalRing_add, Expr.evalRing_mul]
    exact add_nonneg (mul_self_nonneg _) ih

theorem squareSum_zero_iff {σ : Type*} (es : List (Expr σ)) (v : σ → V) :
    InternalZero (squareSum es) v ↔ ∀ e ∈ es, InternalZero e v := by
  induction es with
  | nil => simp [squareSum, internalZero_iff, Expr.evalRing_ofNat]
  | cons e es ih =>
    rw [internalZero_iff]
    simp only [squareSum, Expr.evalRing_add, Expr.evalRing_mul]
    rw [add_eq_zero_iff_of_nonneg (mul_self_nonneg _) (squareSum_nonneg es v), mul_self_eq_zero]
    rw [← internalZero_iff, ← internalZero_iff, ih]
    simp only [List.mem_cons, forall_eq_or_imp]

theorem square_syntax {σ : Type*} (es : List (Expr σ)) :
    squareSum es = QuarticSyntax.sumExpressions (es.map fun e => e * e) := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [squareSum, List.map_cons, QuarticSyntax.sumExpressions, ih]

/-- Candidate extraction for the literal 38-seed, still uncompiled. -/
theorem seed_zero_iff_residuals (p : Fin 4 → ℤ) (v : Fin 39 → V) :
    InternalZero (SharingSeed38.seed p) v ↔
      ∀ e ∈ SharingSeed38.firstResidual p :: SharingSeed38.remainingResiduals p,
        InternalZero e v := by
  have h := squareSum_zero_iff
    (SharingSeed38.firstResidual p :: SharingSeed38.remainingResiduals p) v
  simpa only [squareSum, square_syntax, SharingSeed38.seed] using h

-- Unresolved: map each of the 29 residual zero statements to its generated
-- semiring pair identity or one of the five Carrier65 norm hypotheses.
end DiophantineConsistency.SharingNormSquares
