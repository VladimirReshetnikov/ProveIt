import DiophantineConsistency.AdaptiveAQ35Zeros
import DiophantineConsistency.AdaptiveAQ35Literal
set_option autoImplicit false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveAQ35Positive
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticSignedPairExpressions ArithmeticAdaptiveFactorMagnitude2011
open AdaptiveFirstRootFactor87 AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Context AdaptiveDirectOrdinate86Lift AdaptiveSquareWitnessDirect14 AdaptiveDirectOrdinateSquareSums
open AdaptiveAQ35Context AdaptiveAQ35Zeros
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def squareValue (v : Fin 35 → V) : V :=
  magnitude (pairEval ((.var 26 - .var 27) : Expr (Fin 35)) v) *
    magnitude (pairEval ((.var 26 - .var 27) : Expr (Fin 35)) v)

theorem square_positive (p : Fin 4 → ℤ) (v : Fin 35 → V)
    (hv : ∀ i, 0 < v i) (hz : InternalZero (AdaptiveAQ35Literal.literal p) v) : 0 < squareValue v := by
  have hn : InternalZero ((newSum p).subst newFill) v := by rw [AdaptiveAQ35Literal.new_literal]; exact hz
  have haux := (new_zero p newFill v).mp hn |>.2 ⟨1, by decide⟩
  change InternalZero (((.var 11 * .var 11) - .var 34 * ((.var 11 * .var 11) - ((.var 26 - .var 27) * (.var 26 - .var 27)))) - 1 : Expr (Fin 35)) v at haux
  by_contra hnot
  have hs : squareValue v = 0 := le_antisymm (le_of_not_gt hnot) (Arithmetic.zero_le _)
  have hsq := rawSquare_rep ((.var 26 - .var 27) : Expr (Fin 35)) v
  change SignedRep ((.var 26 - .var 27) * (.var 26 - .var 27) : Expr (Fin 35)) v (natural (squareValue v)) at hsq
  rw [hs] at hsq
  have hy := rep_mul_nat (rep_var v 11) (rep_var v 11)
  have ha := rep_sub (rep_sub hy (rep_mul (rep_var v 34) (rep_sub hy hsq))) (rep_one v)
  have he := (equivalent_zero_iff ha).mp haux
  simp [minus, multiply, natural] at he
  have hle : v 11*v 11 ≤ v 34*(v 11*v 11) := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (pos_iff_one_le.mp (hv 34)) (Arithmetic.zero_le (v 11*v 11))
  have hlt : v 34*(v 11*v 11) < v 11*v 11 := by
    calc
      _ < v 34*(v 11*v 11) + 1 := lt_add_one _
      _ = v 11*v 11 := he.symm
  exact (not_lt_of_ge hle) hlt
#print axioms square_positive
end DiophantineConsistency.AdaptiveAQ35Positive
