/-
Modified for ProveIt: extract the quantitative-density conclusion used by the
Gowers Theorem 1.3 bridge. Prove it directly from uniform relative lifting,
without the combined manuscript theorem or reciprocal-sum conclusion.
-/
import OAI.Combinatorics.Progressions.Estimates.PreparedRelativePositivePassage
import OAI.Combinatorics.Progressions.Estimates.RelativePatchScalarBaseFin
import OAI.Combinatorics.Progressions.Estimates.UniformRelativePatchSource

namespace OAI

section

namespace Erdos3

theorem exists_manuscriptRelativePatchPower (s : ℕ) (hs : 1 ≤ s)
    (discount : ℝ) (hdiscount : 0 < discount) (hhalf : discount ≤ 1 / 2) :
    ∃ power : ℕ, 2 ≤ power ∧
      RelativePatchPowerInductionRule s (VectorPolynomial.scalarNativeDimension s)
        s discount power := by
  have hone : discount ≤ 1 := by linarith only [hhalf]
  apply exists_relativePatchPowerInductionRule_of_fin_base_positive_successors
    ⟨hdiscount.le, hone⟩
  · exact VectorPolynomial.exists_relativePatch_scalarBase_fin_power s hdiscount hhalf
  · intro stage _hstage power hpower ih
    apply exists_relativePatchFinPositivePower_of_prepared
    exact exists_preparedRelativePatchPowerPassage s
      (VectorPolynomial.scalarNativeDimension s) stage power discount
      hs hpower hdiscount hone ih

theorem manuscriptQuantitativeDensityTheorem : QuantitativeDensityTheorem := by
  intro k hk
  let n₀ := VectorPolynomial.scalarNativeDimension (k - 2)
  letI : NeZero n₀ := ⟨Nat.ne_of_gt (VectorPolynomial.scalarNativeDimension_pos (k - 2))⟩
  apply quantitative_density_bound_of_uniform_relative_lifting k n₀ hk
  intro discount hdiscount hhalf
  exact exists_manuscriptRelativePatchPower (k - 2) (by omega) discount hdiscount hhalf

end Erdos3

end

end OAI
