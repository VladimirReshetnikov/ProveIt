import GRHArticle.SingularModuli.Prime17DiagonalData
import GRHArticle.SingularModuli.Prime17SigmaLiterals

/-!
# The discriminant and normalized invariant prefixes.
-/

namespace GRHArticle.SingularModuli.Prime17Data

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem discriminant_check : DiscriminantCheck := by
  unfold DiscriminantCheck discriminantExpr sigmaCoefficients linearDiscriminantCoefficients
  rewrite [← sigma3Literal_eq, ← sigma5Literal_eq]
  decide +kernel

theorem invariant_check : InvariantCheck := by
  unfold InvariantCheck eisensteinCubedExpr sigmaCoefficients
  rewrite [← sigma3Literal_eq, ← sigma5Literal_eq]
  decide +kernel

theorem invariant_nonnegative : ∀ a ∈ invariant, 0 ≤ a := by
  have h : invariant.all (fun a ↦ decide (0 ≤ a)) = true := by decide +kernel
  intro a ha
  exact of_decide_eq_true (List.all_eq_true.mp h a ha)

end GRHArticle.SingularModuli.Prime17Data
