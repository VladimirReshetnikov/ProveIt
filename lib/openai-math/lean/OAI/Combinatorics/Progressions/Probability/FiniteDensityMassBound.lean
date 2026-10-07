import OAI.Combinatorics.Progressions.Estimates.LocalAverageAmplitude
import OAI.Combinatorics.Progressions.Estimates.RealWeightPMF
import OAI.Combinatorics.Progressions.Linear.TruncatedProjectionError

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finite_supported_weight_sum_tsum {X R : Type*} [Fintype R]
    (w : R → X → ℝ) (S : Finset X) (hw : ∀ r x, x ∉ S → w r x = 0) :
    (∑' x, ∑ r, w r x) = ∑ r, ∑' x, w r x := by
  have hcut (v : X → ℝ) (hv : ∀ x ∉ S, v x = 0) : (∑' x, v x) = ∑ x ∈ S, v x :=
    (hasSum_sum_of_ne_finset_zero hv).tsum_eq
  have hsum (x : X) (hx : x ∉ S) : (∑ r, w r x) = 0 := by
    apply Finset.sum_eq_zero
    intro r _
    exact hw r x hx
  have hcutEach (r : R) := hcut (w r) (hw r)
  rw [hcut (fun x => ∑ r, w r x) hsum]
  simp_rw [hcutEach]
  exact Finset.sum_comm

theorem finite_normalized_test_sum {X : Type*} (w : X → ℝ) (S : Finset X)
    (hw : ∀ x ∉ S, w x = 0) (Z : ℝ) (φ : X → ℂ) :
    (∑' x, ((w x / Z : ℝ) : ℂ) * φ x) = ∑ x ∈ S, ((w x / Z : ℝ) : ℂ) * φ x := by
  apply (hasSum_sum_of_ne_finset_zero (s := S) _).tsum_eq
  intro x hx
  simp only [hw x hx, zero_div, Complex.ofReal_zero, zero_mul]

theorem finite_supported_normalized_mixture {X R : Type*} [Fintype R]
    (w : R → X → ℝ) (S : Finset X) (hw : ∀ r x, x ∉ S → w r x = 0)
    (hZr : ∀ r, 0 < ∑' x, w r x) (hZ : 0 < ∑ r, ∑' x, w r x) (φ : X → ℂ) :
    (∑' x, (((∑ r, w r x) / (∑ r, ∑' y, w r y) : ℝ) : ℂ) * φ x) =
      ∑ r, (((∑' y, w r y) / (∑ s, ∑' y, w s y) : ℝ) : ℂ) *
        (∑' x, ((w r x / (∑' y, w r y) : ℝ) : ℂ) * φ x) := by
  have hsum (x : X) (hx : x ∉ S) : (∑ r, w r x) = 0 := by
    apply Finset.sum_eq_zero
    intro r _
    exact hw r x hx
  have hcut := finite_normalized_test_sum (fun x => ∑ r, w r x) S hsum
    (∑ r, ∑' y, w r y) φ
  rw [hcut]
  simp_rw [finite_normalized_test_sum _ S (hw _) _ φ, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  have hc r : (((∑' y, w r y) / (∑ s, ∑' y, w s y) : ℝ) : ℂ) *
      (((w r x / (∑' y, w r y) : ℝ) : ℂ) * φ x) =
      ((w r x / (∑ s, ∑' y, w s y) : ℝ) : ℂ) * φ x := by
    rw [← mul_assoc, ← Complex.ofReal_mul]
    congr 2
    field_simp [hZ.ne', (hZr r).ne']
  simp_rw [hc]
  rw [← Finset.sum_mul, ← Complex.ofReal_sum, ← Finset.sum_div]

theorem finite_supported_normalized_mixture_bound {X R : Type*} [Fintype R]
    (w : R → X → ℝ) (S : Finset X) (hw : ∀ r x, x ∉ S → w r x = 0)
    (hZr : ∀ r, 0 < ∑' x, w r x) (hZ : 0 < ∑ r, ∑' x, w r x)
    (φ : X → ℂ) {ε : ℝ}
    (hφ : ∀ r, ‖∑' x, ((w r x / (∑' y, w r y) : ℝ) : ℂ) * φ x‖ ≤ ε) :
    ‖∑' x, (((∑ r, w r x) / (∑ r, ∑' y, w r y) : ℝ) : ℂ) * φ x‖ ≤ ε := by
  rw [finite_supported_normalized_mixture w S hw hZr hZ φ]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ r, ((∑' y, w r y) / (∑ s, ∑' y, w s y)) * ε := by
      apply Finset.sum_le_sum
      intro r _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (div_pos (hZr r) hZ).le]
      exact mul_le_mul_of_nonneg_left (hφ r) (div_pos (hZr r) hZ).le
    _ = ε := by rw [← Finset.sum_mul, ← Finset.sum_div, div_self hZ.ne', one_mul]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem sum_support_eq_tsum {X : Type*} (w : X → ℝ) (S : Finset X)
    (hw : ∀ x ∉ S, w x = 0) : (∑ x : S, w x.val) = ∑' x, w x := by
  calc
    _ = ∑ x ∈ S, w x := Finset.sum_coe_sort S w
    _ = _ := (hasSum_sum_of_ne_finset_zero hw).tsum_eq.symm

noncomputable def finiteSupportProbability {X : Type*} (w : X → ℝ) (S : Finset X)
    (hw0 : ∀ x, 0 ≤ w x) (hw : ∀ x ∉ S, w x = 0) (hZ : 0 < ∑' x, w x) :
    FiniteProbabilityWeights S where
  weight x := w x.val / ∑' y, w y
  nonneg x := div_nonneg (hw0 x.val) hZ.le
  total := by
    rw [← Finset.sum_div, sum_support_eq_tsum w S hw, div_self hZ.ne']

theorem finiteSupportProbability_complexMean {X : Type*} (w : X → ℝ) (S : Finset X)
    (hw0 : ∀ x, 0 ≤ w x) (hw : ∀ x ∉ S, w x = 0) (hZ : 0 < ∑' x, w x)
    (f : X → ℂ) :
    (finiteSupportProbability w S hw0 hw hZ).complexMean (fun x => f x.val) =
      ∑' x, ((w x / (∑' y, w y) : ℝ) : ℂ) * f x := by
  change (∑ x : S, ((w x.val / (∑' y, w y) : ℝ) : ℂ) * f x.val) = _
  calc
    _ = ∑ x ∈ S, ((w x / (∑' y, w y) : ℝ) : ℂ) * f x :=
      Finset.sum_coe_sort S _
    _ = _ := (finite_normalized_test_sum w S hw _ f).symm

theorem normalized_finite_weight_discard_error {X J : Type*} [Fintype J]
    (v : X → ℝ) (S : Finset X) (hv0 : ∀ x, 0 ≤ v x)
    (hv : ∀ x ∉ S, v x = 0) (hZ : 0 < ∑' x, v x)
    (w : X → ℂ) (c : J → ℂ) (u : J → X → ℂ)
    (keep : J → Prop) [DecidablePred keep] {C τ : ℝ}
    (hc : (∑ j, ‖c j‖) ≤ C) (hτ : 0 ≤ τ)
    (hdiscard : ∀ j, ¬keep j →
      ‖∑' x, ((v x / (∑' y, v y) : ℝ) : ℂ) * (w x * u j x)‖ ≤ τ) :
    ‖(∑' x, ((v x / (∑' y, v y) : ℝ) : ℂ) * (w x * ∑ j, c j * u j x)) -
      ∑' x, ((v x / (∑' y, v y) : ℝ) : ℂ) * (w x * ∑ j, if keep j then c j * u j x else 0)‖ ≤ C * τ := by
  have hdiscard' (j) (hj : ¬keep j) :
      ‖(finiteSupportProbability v S hv0 hv hZ).complexMean (fun x => w x.val * u j x.val)‖ ≤ τ := by
    rw [finiteSupportProbability_complexMean v S hv0 hv hZ (fun x => w x * u j x)]
    exact hdiscard j hj
  have h := (finiteSupportProbability v S hv0 hv hZ).weighted_expansion_discard_error
    (fun x => w x.val) c (fun j x => u j x.val) keep hc hτ hdiscard'
  rw [finiteSupportProbability_complexMean v S hv0 hv hZ (fun x => w x * ∑ j, c j * u j x),
    finiteSupportProbability_complexMean v S hv0 hv hZ
      (fun x => w x * ∑ j, if keep j then c j * u j x else 0)] at h
  exact h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def finiteDensityMass {X : Type*} (w D : X → ℝ) : ℝ :=
  ∑' x, (w x / ∑' y, w y) * D x

theorem finiteDensityMass_eq_div {X : Type*} (w D : X → ℝ) :
    finiteDensityMass w D = (∑' x, w x * D x) / ∑' x, w x := by
  simp only [finiteDensityMass, div_mul_eq_mul_div, tsum_div_const]

theorem finiteDensityMass_complex {X : Type*} (w D : X → ℝ) :
    (finiteDensityMass w D : ℂ) = ∑' x, ((w x / ∑' y, w y : ℝ) : ℂ) * (D x : ℂ) := by
  simp only [finiteDensityMass, Complex.ofReal_tsum, Complex.ofReal_mul]

theorem finiteDensityMass_raw_pos {X : Type*} (w D : X → ℝ)
    (hw : 0 < ∑' x, w x) (hD : 0 < finiteDensityMass w D) :
    0 < ∑' x, w x * D x := by
  have he := (eq_div_iff hw.ne').mp (finiteDensityMass_eq_div w D)
  rw [← he]
  exact mul_pos hD hw

noncomputable def finiteDensityTiltPMF {X : Type*} (w : X → ℝ) (S : Finset X)
    (hw0 : ∀ x, 0 ≤ w x) (hw : ∀ x ∉ S, w x = 0) (hZ : 0 < ∑' x, w x)
    (D : X → ℝ) (hD0 : ∀ x, 0 ≤ D x) (hD : 0 < finiteDensityMass w D) : PMF X :=
  realWeightPMF (fun x => w x * D x) (fun x => mul_nonneg (hw0 x) (hD0 x))
    (hasSum_sum_of_ne_finset_zero (s := S) (fun x hx => by rw [hw x hx, zero_mul])).summable
    (finiteDensityMass_raw_pos w D hZ hD)

theorem finiteDensityTiltPMF_toReal {X : Type*} (w : X → ℝ) (S : Finset X)
    (hw0 : ∀ x, 0 ≤ w x) (hw : ∀ x ∉ S, w x = 0) (hZ : 0 < ∑' x, w x)
    (D : X → ℝ) (hD0 : ∀ x, 0 ≤ D x) (hD : 0 < finiteDensityMass w D) (x : X) :
    (finiteDensityTiltPMF w S hw0 hw hZ D hD0 hD x).toReal =
      (w x / ∑' y, w y) * D x / finiteDensityMass w D := by
  rw [finiteDensityTiltPMF, realWeightPMF_apply]
  have he := (eq_div_iff hZ.ne').mp (finiteDensityMass_eq_div w D)
  rw [← he]
  field_simp

theorem finiteDensityTiltPMF_complexMean {X : Type*} (w : X → ℝ) (S : Finset X)
    (hw0 : ∀ x, 0 ≤ w x) (hw : ∀ x ∉ S, w x = 0) (hZ : 0 < ∑' x, w x)
    (D : X → ℝ) (hD0 : ∀ x, 0 ≤ D x) (hD : 0 < finiteDensityMass w D) (f : X → ℂ) :
    (∑' x, ((finiteDensityTiltPMF w S hw0 hw hZ D hD0 hD x).toReal : ℂ) * f x) =
      (∑' x, ((w x / ∑' y, w y : ℝ) : ℂ) * ((D x : ℂ) * f x)) /
        (finiteDensityMass w D : ℂ) := by
  simp only [finiteDensityTiltPMF_toReal, Complex.ofReal_div, Complex.ofReal_mul,
    div_mul_eq_mul_div, mul_assoc, tsum_div_const]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem finiteDensityMass_sum_le_of_weight_lower {X : Type*}
    (w D : X → ℝ) (support window : Finset X)
    (hw : ∀ x, 0 ≤ w x) (hoff : ∀ x ∉ support, w x = 0)
    (hD : ∀ x, 0 ≤ D x) (hZ : 0 < ∑' x, w x)
    {b : ℝ} (hb : 0 < b) (hlower : ∀ x ∈ window, b ≤ w x) :
    (∑ x ∈ window, D x) ≤ ((∑' x, w x) / b) * finiteDensityMass w D := by
  classical
  have hsub : window ⊆ support := by
    intro x hx
    by_contra h
    have hh := hlower x hx
    rw [hoff x h] at hh
    exact (not_le_of_gt hb) hh
  have hsum : (∑' x, w x * D x) = ∑ x ∈ support, w x * D x :=
    tsum_eq_sum (fun x hx => by rw [hoff x hx, zero_mul])
  have hbound : b * (∑ x ∈ window, D x) ≤ ∑' x, w x * D x := by
    rw [hsum, Finset.mul_sum]
    apply (Finset.sum_le_sum (fun x hx => mul_le_mul_of_nonneg_right (hlower x hx) (hD x))).trans
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun x _ _ => mul_nonneg (hw x) (hD x))
  have he : finiteDensityMass w D * (∑' x, w x) = ∑' x, w x * D x :=
    (eq_div_iff hZ.ne').mp (finiteDensityMass_eq_div w D)
  rw [← he] at hbound
  calc
    (∑ x ∈ window, D x) ≤ (finiteDensityMass w D * (∑' x, w x)) / b :=
      (le_div_iff₀ hb).mpr (by simpa only [mul_comm b] using hbound)
    _ = ((∑' x, w x) / b) * finiteDensityMass w D := by ring

end Erdos3

end

end OAI
