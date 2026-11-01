import DiophantineConsistency.AdaptiveNamedValues42
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace DiophantineConsistency.AdaptiveFoldSquares
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveSquareWitnessDirect14 AdaptiveDirectOrdinateSquareSums
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def foldSquares {σ : Type*} (a : Expr σ) : List (Expr σ) → Expr σ
  | [] => a
  | e::es => foldSquares (a + e*e) es

theorem foldSquares_zero_iff {σ : Type*} (v : σ → V) (es : List (Expr σ))
    (a : Expr σ) (n : V) (ha : SignedRep a v (natural n)) :
    InternalZero (foldSquares a es) v ↔ InternalZero a v ∧ ∀ e ∈ es, InternalZero e v := by
  induction es generalizing a n with
  | nil => simp [foldSquares]
  | cons e es ih =>
    have hb := rep_add_nat ha (rawSquare_rep e v)
    change SignedRep (a + e*e) v (natural _) at hb
    change InternalZero (foldSquares (a + e*e) es) v ↔ _
    rw [ih _ _ hb, AdaptiveNamedValues22.append_square_zero_iff _ _ _ _ ha]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto
#print axioms foldSquares_zero_iff
end DiophantineConsistency.AdaptiveFoldSquares
