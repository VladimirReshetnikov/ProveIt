import OAI.Combinatorics.Progressions.Geometry.RelativePatchWholeBoxConclusion
import OAI.Combinatorics.Progressions.Probability.RestrictedWeightedLawModeledTransfer

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem relativePatchSliceConclusion_of_recovered_patch
    {X : Type*} [Fintype X] [DecidableEq X] {s d rankBound : ℕ}
    (N : X → ℕ) (f : (X → ℤ) → ℝ) (target cost gain : ℝ)
    (A : PolynomialPatch X s d) (lip : ℝ≥0)
    (hrank : d ≤ rankBound) (hcost : 0 ≤ cost)
    (hlip : A.kernel.lip ≤ lip)
    (hbudget : (d : ℝ) + Real.log (1 + (lip : ℝ)) ≤ cost)
    (hgain : Real.exp (-cost) ≤ gain)
    (hscore : gain ≤
      (𝔼 x : ↥(integerBox N), (f x.val - target) * A.value (fun i => (x.val i : ℝ)))) :
    RelativePatchSliceConclusion s N f target rankBound cost := by
  have hcomplexity : relativePatchComplexity A ≤ cost := by
    apply le_trans _ hbudget
    unfold relativePatchComplexity
    apply add_le_add le_rfl
    apply Real.log_le_log (by positivity)
    exact add_le_add le_rfl (show (A.kernel.lip : ℝ) ≤ lip from hlip)
  exact (relativePatchSliceConclusion_of_subtypeScore N f target cost A hcost
    hcomplexity (hgain.trans hscore)).mono hrank le_rfl

end Erdos3

end

end OAI
