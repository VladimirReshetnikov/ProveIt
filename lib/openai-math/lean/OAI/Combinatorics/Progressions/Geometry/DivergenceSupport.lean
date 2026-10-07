import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem continuousLinearMap_coordinate_sum (L : (ι → ℝ) →L[ℝ] ℝ) (v : ι → ℝ) :
    L v = ∑ i, v i * L (Pi.single i 1) := by
  have hv : (∑ i, v i • Pi.single i (1 : ℝ)) = v := by
    ext j
    simp [Pi.single_apply]
  calc
    L v = L (∑ i, v i • Pi.single i (1 : ℝ)) := congrArg L hv.symm
    _ = ∑ i, v i * L (Pi.single i 1) := by simp only [map_sum, map_smul, smul_eq_mul]

noncomputable def coordinateDivergence (Q : ι → (ι → ℝ) → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i, fderiv ℝ (Q i) x (Pi.single i 1)

theorem coordinateDivergence_continuous (Q : ι → (ι → ℝ) → ℝ)
    (hQ : ∀ i, ContDiff ℝ 1 (Q i)) : Continuous (coordinateDivergence Q) := by
  apply continuous_finsetSum
  intro i _
  exact ((hQ i).continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem coordinateDivergence_hasCompactSupport (Q : ι → (ι → ℝ) → ℝ)
    (hQ : ∀ i, HasCompactSupport (Q i)) : HasCompactSupport (coordinateDivergence Q) := by
  have h := HasCompactSupport.finset_sum (s := Finset.univ)
    (fun i _ => (hQ i).fderiv_apply ℝ (Pi.single i 1))
  have heq : (∑ i, fun x => fderiv ℝ (Q i) x (Pi.single i 1)) = coordinateDivergence Q := by
    ext x
    simp [coordinateDivergence]
  rw [heq] at h
  exact h

theorem coordinate_vectorField_integration_by_parts (Q : ι → (ι → ℝ) → ℝ)
    (hQ : ∀ i, ContDiff ℝ 1 (Q i)) (hs : ∀ i, HasCompactSupport (Q i))
    (ψ : (ι → ℝ) → ℝ) (hψ : ContDiff ℝ 1 ψ) :
    (∫ x, fderiv ℝ ψ x (fun i => Q i x)) = - ∫ x, coordinateDivergence Q x * ψ x := by
  have hDQ (i : ι) : Continuous (fun x => fderiv ℝ (Q i) x (Pi.single i 1)) :=
    ((hQ i).continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hDψ (i : ι) : Continuous (fun x => fderiv ℝ ψ x (Pi.single i 1)) :=
    (hψ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hleft (i : ι) : Integrable (fun x => Q i x * fderiv ℝ ψ x (Pi.single i 1)) :=
    ((hQ i).continuous.mul (hDψ i)).integrable_of_hasCompactSupport ((hs i).mul_right)
  have hright (i : ι) : Integrable (fun x => fderiv ℝ (Q i) x (Pi.single i 1) * ψ x) :=
    ((hDQ i).mul hψ.continuous).integrable_of_hasCompactSupport
      (((hs i).fderiv_apply ℝ (Pi.single i 1)).mul_right)
  have hprod (i : ι) : Integrable (fun x => Q i x * ψ x) :=
    ((hQ i).continuous.mul hψ.continuous).integrable_of_hasCompactSupport ((hs i).mul_right)
  have hibp (i : ι) : (∫ x, Q i x * fderiv ℝ ψ x (Pi.single i 1)) =
      -∫ x, fderiv ℝ (Q i) x (Pi.single i 1) * ψ x :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (hright i) (hleft i) (hprod i)
      (fun x _ => (hQ i).differentiable (by norm_num) x)
      (fun x _ => hψ.differentiable (by norm_num) x)
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
    _ = -∫ x, coordinateDivergence Q x * ψ x := by
      simp only [coordinateDivergence, Finset.sum_mul]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem coordinateDivergence_tsupport_subset
    (Q : ι → (ι → ℝ) → ℝ) {K : Set (ι → ℝ)} (hK : IsClosed K)
    (hQ : ∀ i, tsupport (Q i) ⊆ K) : tsupport (coordinateDivergence Q) ⊆ K := by
  apply closure_minimal _ hK
  intro x hx
  by_contra hxK
  have hzero : coordinateDivergence Q x = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hnot : x ∉ tsupport (fun y => fderiv ℝ (Q i) y (Pi.single i 1)) :=
      fun h => hxK (hQ i ((tsupport_fderiv_apply_subset ℝ (Pi.single i 1)) h))
    exact image_eq_zero_of_notMem_tsupport
      (f := fun y => fderiv ℝ (Q i) y (Pi.single i 1)) (x := x) hnot
  exact hx hzero

theorem integral_abs_divergence_eq_setIntegral
    (Q : ι → (ι → ℝ) → ℝ) (w : (ι → ℝ) → ℝ) (hQ : ∀ i, tsupport (Q i) ⊆ tsupport w)
    {s : Set (ι → ℝ)} (hs : tsupport w ⊆ s) :
    (∫ x, |coordinateDivergence Q x|) = ∫ x in s, |coordinateDivergence Q x| := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [image_eq_zero_of_notMem_tsupport (fun h =>
    hx (hs (coordinateDivergence_tsupport_subset Q (isClosed_tsupport w) hQ h))), abs_zero]

end Erdos3

end

end OAI
