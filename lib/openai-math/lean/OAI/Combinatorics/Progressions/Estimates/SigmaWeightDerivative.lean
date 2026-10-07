/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.SplitSmoothProductProfile

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {D : Type*} [Fintype D] [DecidableEq D] {I : D → Type*}
  [∀ d, Fintype (I d)] [∀ d, DecidableEq (I d)]

omit [Fintype D] [∀ d, Fintype (I d)] in
theorem sigmaAxisCoordinates_single (d : D) (i : I d) :
    sigmaAxisCoordinates I (Pi.single ⟨d, i⟩ (1 : ℝ)) = Pi.single d (Pi.single i 1) := by
  ext e j
  by_cases he : e = d
  · subst e
    simp [sigmaAxisCoordinates, Pi.single_apply]
  · have hs : (⟨e, j⟩ : Σ d, I d) ≠ ⟨d, i⟩ := fun h => he (congrArg Sigma.fst h)
    simp [sigmaAxisCoordinates, Pi.single_eq_of_ne he, Pi.single_eq_of_ne hs]

theorem sigmaAxisWeight_coordinate_fderiv (w : ∀ d, (I d → ℝ) → ℝ)
    (hw : ∀ d, ContDiff ℝ 1 (w d)) (x : (Σ d, I d) → ℝ) (d : D) (i : I d) :
    fderiv ℝ (sigmaAxisWeight w) x (Pi.single ⟨d, i⟩ 1) =
      fderiv ℝ (tensorCutoffWeight w) (sigmaAxisCoordinates I x) (Pi.single d (Pi.single i 1)) := by
  have hd := ((tensorCutoffWeight_contDiff w hw).differentiable one_ne_zero
    (sigmaAxisCoordinates I x)).hasFDerivAt.comp x (sigmaAxisCoordinates I).toContinuousLinearMap.hasFDerivAt
  change fderiv ℝ (tensorCutoffWeight w ∘ sigmaAxisCoordinates I) x (Pi.single ⟨d, i⟩ 1) = _
  rw [hd.fderiv, ContinuousLinearMap.comp_apply]
  exact congrArg (fderiv ℝ (tensorCutoffWeight w) (sigmaAxisCoordinates I x))
    (sigmaAxisCoordinates_single d i)

theorem sigmaAxisWeight_coordinate_integral (w : ∀ d, (I d → ℝ) → ℝ)
    (hw : ∀ d, ContDiff ℝ 1 (w d)) (d : D) (i : I d) :
    (∫ x, |fderiv ℝ (sigmaAxisWeight w) x (Pi.single ⟨d, i⟩ 1)|) =
      (∫ y, |fderiv ℝ (w d) y (Pi.single i 1)|) * ∏ e ∈ Finset.univ.erase d, ∫ y, |w e y| := by
  simp_rw [sigmaAxisWeight_coordinate_fderiv w hw]
  rw [(sigmaAxisCoordinates_measurePreserving I).integral_comp
    (sigmaAxisCoordinates I).toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (fun y => |fderiv ℝ (tensorCutoffWeight w) y (Pi.single d (Pi.single i 1))|)]
  exact tensorCutoffWeight_derivative_integral w hw d (Pi.single i 1)

theorem sigmaAxisWeight_coordinate_integral_le (w : ∀ d, (I d → ℝ) → ℝ)
    (hw : ∀ d, ContDiff ℝ 1 (w d)) (hm : ∀ d, (∫ y, |w d y|) ≤ 1) (d : D) (i : I d) :
    (∫ x, |fderiv ℝ (sigmaAxisWeight w) x (Pi.single ⟨d, i⟩ 1)|) ≤
      ∫ y, |fderiv ℝ (w d) y (Pi.single i 1)| := by
  rw [sigmaAxisWeight_coordinate_integral w hw]
  exact mul_le_of_le_one_right (integral_nonneg (fun _ => abs_nonneg _))
    (Finset.prod_le_one₀ (fun e _ => integral_nonneg (fun _ => abs_nonneg _)) (fun e _ => hm e))

theorem sigmaAxisWeight_derivative_sum_le (w : ∀ d, (I d → ℝ) → ℝ)
    (hw : ∀ d, ContDiff ℝ 1 (w d)) (hm : ∀ d, (∫ y, |w d y|) ≤ 1) :
    (∑ s : Σ d, I d, ∫ x, |fderiv ℝ (sigmaAxisWeight w) x (Pi.single s 1)|) ≤
      ∑ d, ∑ i : I d, ∫ y, |fderiv ℝ (w d) y (Pi.single i 1)| := by
  rw [Fintype.sum_sigma]
  exact Finset.sum_le_sum (fun d _ => Finset.sum_le_sum (fun i _ =>
    sigmaAxisWeight_coordinate_integral_le w hw hm d i))

end Erdos3

end

end OAI
