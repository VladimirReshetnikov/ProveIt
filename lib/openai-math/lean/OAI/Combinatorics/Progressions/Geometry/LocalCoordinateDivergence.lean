import OAI.Combinatorics.Progressions.Estimates.LocalProductContinuity
import OAI.Combinatorics.Progressions.Geometry.DivergenceSupport

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem local_coordinate_vectorField_integration_by_parts
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : ι → (ι → ℝ) → ℝ) (hQ : ∀ i, ContDiff ℝ 1 (Q i))
    (hs : ∀ i, HasCompactSupport (Q i)) (ψ : (ι → ℝ) → ℝ)
    (hψ : ∀ i x, x ∈ tsupport (Q i) → ContDiffAt ℝ 1 ψ x) :
    (∫ x, fderiv ℝ ψ x (fun i => Q i x)) = -∫ x, coordinateDivergence Q x * ψ x := by
  have hDQ (i : ι) : Continuous (fun x => fderiv ℝ (Q i) x (Pi.single i 1)) :=
    ((hQ i).continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hleft (i : ι) : Integrable (fun x => Q i x * fderiv ℝ ψ x (Pi.single i 1)) := by
    apply (continuous_mul_of_local_right (hQ i).continuous ?_).integrable_of_hasCompactSupport
      ((hs i).mul_right)
    intro x hx
    exact ((hψ i x hx).continuousAt_fderiv (by norm_num)).clm_apply continuousAt_const
  have hright (i : ι) : Integrable (fun x => fderiv ℝ (Q i) x (Pi.single i 1) * ψ x) := by
    apply (continuous_mul_of_local_right (hDQ i) ?_).integrable_of_hasCompactSupport
      (((hs i).fderiv_apply ℝ (Pi.single i 1)).mul_right)
    intro x hx
    exact (hψ i x ((tsupport_fderiv_apply_subset ℝ (Pi.single i 1)) hx)).continuousAt
  have hprod (i : ι) : Integrable (fun x => Q i x * ψ x) :=
    (continuous_mul_of_local_right (hQ i).continuous (fun x hx => (hψ i x hx).continuousAt)).integrable_of_hasCompactSupport
      ((hs i).mul_right)
  have hibp (i : ι) : (∫ x, Q i x * fderiv ℝ ψ x (Pi.single i 1)) =
      -∫ x, fderiv ℝ (Q i) x (Pi.single i 1) * ψ x :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (hright i) (hleft i) (hprod i)
      (fun x _ => (hQ i).differentiable (by norm_num) x)
      (fun x hx => (hψ i x hx).differentiableAt (by norm_num))
  calc
    (∫ x, fderiv ℝ ψ x (fun i => Q i x)) =
        ∫ x, ∑ i, Q i x * fderiv ℝ ψ x (Pi.single i 1) := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact continuousLinearMap_coordinate_sum _ _
    _ = ∑ i, ∫ x, Q i x * fderiv ℝ ψ x (Pi.single i 1) :=
      integral_finsetSum _ (fun i _ => hleft i)
    _ = -(∑ i, ∫ x, fderiv ℝ (Q i) x (Pi.single i 1) * ψ x) := by
      simp only [hibp, Finset.sum_neg_distrib]
    _ = -(∫ x, ∑ i, fderiv ℝ (Q i) x (Pi.single i 1) * ψ x) := by
      rw [integral_finsetSum _ (fun i _ => hright i)]
    _ = -∫ x, coordinateDivergence Q x * ψ x := by simp only [coordinateDivergence, Finset.sum_mul]

end Erdos3

end

end OAI
