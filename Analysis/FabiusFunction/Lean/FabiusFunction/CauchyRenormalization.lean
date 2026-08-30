import FabiusFunction.AffineDifferenceOrbit
import FabiusFunction.CauchyTransform
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Renormalization of the Rvachev Cauchy transform

The differential refinement equation for Rvachev's compactly supported
function transfers to its Cauchy transform.  On the complement of `[-1,1]`,

`R'(z) = 2 * (R(2*z+1) - R(2*z-1))`.

Both affine branches preserve this domain.  The generic affine-difference
orbit theorem therefore propagates the equation to every complex derivative,
giving a finite Thue--Morse orbit with the exact chain-rule coefficient.
-/

set_option autoImplicit false

open Finset MeasureTheory Set
open scoped BigOperators Interval

namespace Fabius

private theorem integral_rvachevUp_mul_eq_intervalIntegral
    (F : BoundedFabius) (hF : IsFabius F) (g : ℝ → ℂ) :
    (∫ x : ℝ, (rvachevUp F x : ℂ) * g x) =
      ∫ x in (-1 : ℝ)..1, (rvachevUp F x : ℂ) * g x := by
  apply (intervalIntegral.integral_eq_integral_of_support_subset ?_).symm
  intro x hx
  have hux : rvachevUp F x ≠ 0 := by
    intro hzero
    apply hx
    simp [hzero]
  exact Ioo_subset_Ioc_self (support_rvachev_subset_Ioo F hF hux)

private theorem rvachevCauchyTransform_eq_intervalIntegral
    (F : BoundedFabius) (hF : IsFabius F) (z : ℂ) :
    rvachevCauchyTransform F z =
      ∫ x in (-1 : ℝ)..1,
        (rvachevUp F x : ℂ) * (z - (x : ℂ))⁻¹ := by
  calc
    rvachevCauchyTransform F z =
        ∫ x : ℝ, (rvachevUp F x : ℂ) * (z - (x : ℂ))⁻¹ :=
      rvachevCauchyTransform_eq_integral_rvachevUp F hF z
    _ = ∫ x in (-1 : ℝ)..1,
        (rvachevUp F x : ℂ) * (z - (x : ℂ))⁻¹ :=
      integral_rvachevUp_mul_eq_intervalIntegral F hF _

/-! ## Invariance of the slit domain -/

/-- The positive dyadic branch `z ↦ 2*z+1` preserves the complement of
the complexified interval `[-1,1]`. -/
theorem mapsTo_rvachevCauchyDomain_two_mul_add_one :
    MapsTo (fun z : ℂ => 2 * z + 1)
      rvachevCauchyDomain rvachevCauchyDomain := by
  intro z hz
  have hznot :
      z ∉ algebraMap ℝ ℂ '' Icc (-1 : ℝ) 1 := by
    simpa [rvachevCauchyDomain] using hz
  have hnot :
      2 * z + 1 ∉ algebraMap ℝ ℂ '' Icc (-1 : ℝ) 1 := by
    rintro ⟨x, hx, hxeq⟩
    apply hznot
    refine ⟨(x - 1) / 2, ?_, ?_⟩
    · constructor <;> linarith [hx.1, hx.2]
    · have hxeq' : (x : ℂ) = 2 * z + 1 := by
        simpa only [Complex.coe_algebraMap] using hxeq
      simp only [Complex.coe_algebraMap]
      push_cast
      rw [hxeq']
      ring
  simpa [rvachevCauchyDomain] using hnot

/-- The negative dyadic branch `z ↦ 2*z-1` preserves the complement of
the complexified interval `[-1,1]`. -/
theorem mapsTo_rvachevCauchyDomain_two_mul_sub_one :
    MapsTo (fun z : ℂ => 2 * z - 1)
      rvachevCauchyDomain rvachevCauchyDomain := by
  intro z hz
  have hznot :
      z ∉ algebraMap ℝ ℂ '' Icc (-1 : ℝ) 1 := by
    simpa [rvachevCauchyDomain] using hz
  have hnot :
      2 * z - 1 ∉ algebraMap ℝ ℂ '' Icc (-1 : ℝ) 1 := by
    rintro ⟨x, hx, hxeq⟩
    apply hznot
    refine ⟨(x + 1) / 2, ?_, ?_⟩
    · constructor <;> linarith [hx.1, hx.2]
    · have hxeq' : (x : ℂ) = 2 * z - 1 := by
        simpa only [Complex.coe_algebraMap] using hxeq
      simp only [Complex.coe_algebraMap]
      push_cast
      rw [hxeq']
      ring
  simpa [rvachevCauchyDomain] using hnot

/-! ## First-order renormalization -/

/-- **Rvachev Cauchy-transform differential equation.**  Off the support
interval, differentiating the Cauchy kernel and integrating the differential
refinement equation by parts gives

`R'(z) = 2 * (R(2*z+1) - R(2*z-1))`.
-/
theorem hasDerivAt_rvachevCauchyTransform_affineDifference
    (F : BoundedFabius) (hF : IsFabius F) {z : ℂ}
    (hz : z ∈ rvachevCauchyDomain) :
    HasDerivAt (rvachevCauchyTransform F)
      (2 * (rvachevCauchyTransform F (2 * z + 1) -
        rvachevCauchyTransform F (2 * z - 1))) z := by
  let u : ℝ → ℂ := fun t => (rvachevUp F t : ℂ)
  let u' : ℝ → ℂ := fun t =>
    2 * ((rvachevUp F (2 * t + 1) : ℂ) -
      (rvachevUp F (2 * t - 1) : ℂ))
  let k : ℝ → ℂ := fun t => (z - (t : ℂ))⁻¹
  let k' : ℝ → ℂ := fun t => (z - (t : ℂ))⁻¹ ^ 2
  have hznot : z ∉ algebraMap ℝ ℂ '' Icc (-1 : ℝ) 1 := by
    simpa [rvachevCauchyDomain] using hz
  have hk_ne : ∀ t ∈ Icc (-1 : ℝ) 1, z - (t : ℂ) ≠ 0 := by
    intro t ht hzero
    apply hznot
    refine ⟨t, ht, ?_⟩
    simpa only [Complex.coe_algebraMap] using (sub_eq_zero.mp hzero).symm
  have hu : ∀ t ∈ [[(-1 : ℝ), 1]], HasDerivAt u (u' t) t := by
    intro t _ht
    simpa [u, u'] using (rvachev_hasDerivAt F hF t).ofReal_comp
  have hk : ∀ t ∈ [[(-1 : ℝ), 1]], HasDerivAt k (k' t) t := by
    intro t ht
    have htI : t ∈ Icc (-1 : ℝ) 1 := by
      simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using ht
    have hsub : HasDerivAt (fun w : ℂ => z - w) (-1) (t : ℂ) := by
      simpa only [id_eq] using (hasDerivAt_id (t : ℂ)).const_sub z
    have hinv := hsub.inv (hk_ne t htI)
    simpa [k, k'] using hinv.comp_ofReal
  have hup : Continuous u :=
    Complex.continuous_ofReal.comp (rvachev_contDiff F hF).continuous
  have hu'_continuous : Continuous u' := by
    dsimp only [u']
    exact continuous_const.mul
      ((hup.comp ((continuous_const.mul continuous_id).add continuous_const)).sub
        (hup.comp ((continuous_const.mul continuous_id).sub continuous_const)))
  have hu'_int : IntervalIntegrable u' volume (-1) 1 :=
    hu'_continuous.intervalIntegrable _ _
  have hk_cont : ContinuousOn k (Icc (-1 : ℝ) 1) := by
    dsimp only [k]
    exact
      (by fun_prop : ContinuousOn (fun t : ℝ => z - (t : ℂ))
        (Icc (-1 : ℝ) 1)).inv₀ hk_ne
  have hk'_int : IntervalIntegrable k' volume (-1) 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    change ContinuousOn (fun t => k t ^ 2) (Icc (-1 : ℝ) 1)
    exact hk_cont.pow 2
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hu hk hu'_int hk'_int
  have hparts :
      -(∫ t in (-1 : ℝ)..1, u t * k' t) =
        ∫ t in (-1 : ℝ)..1, u' t * k t := by
    rw [hibp]
    simp [u, rvachevUp_one F hF, rvachevUp_neg_one F hF]
  let p : ℝ → ℂ := fun t =>
    (rvachevUp F (2 * t + 1) : ℂ) * k t
  let m : ℝ → ℂ := fun t =>
    (rvachevUp F (2 * t - 1) : ℂ) * k t
  have hp_cont : ContinuousOn p (Icc (-1 : ℝ) 1) := by
    dsimp only [p]
    exact
      ((hup.comp ((continuous_const.mul continuous_id).add continuous_const)).continuousOn).mul
        hk_cont
  have hm_cont : ContinuousOn m (Icc (-1 : ℝ) 1) := by
    dsimp only [m]
    exact
      ((hup.comp ((continuous_const.mul continuous_id).sub continuous_const)).continuousOn).mul
        hk_cont
  have hp_left : IntervalIntegrable p volume (-1) 0 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    exact hp_cont.mono (by intro t ht; constructor <;> linarith [ht.1, ht.2])
  have hp_right : IntervalIntegrable p volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    exact hp_cont.mono (by intro t ht; constructor <;> linarith [ht.1, ht.2])
  have hm_left : IntervalIntegrable m volume (-1) 0 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    exact hm_cont.mono (by intro t ht; constructor <;> linarith [ht.1, ht.2])
  have hm_right : IntervalIntegrable m volume 0 1 := by
    apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
    exact hm_cont.mono (by intro t ht; constructor <;> linarith [ht.1, ht.2])
  have hp_zero : (∫ t in (0 : ℝ)..1, p t) = 0 := by
    calc
      (∫ t in (0 : ℝ)..1, p t) = ∫ _t in (0 : ℝ)..1, (0 : ℂ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
        dsimp only [p]
        rw [rvachevUp_eq_zero_of_one_le F hF (by linarith [ht.1])]
        simp
      _ = 0 := by simp
  have hm_zero : (∫ t in (-1 : ℝ)..0, m t) = 0 := by
    calc
      (∫ t in (-1 : ℝ)..0, m t) = ∫ _t in (-1 : ℝ)..0, (0 : ℂ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at ht
        dsimp only [m]
        rw [rvachevUp_eq_zero_of_le_neg_one F hF (by linarith [ht.2])]
        simp
      _ = 0 := by simp
  let gp : ℝ → ℂ := fun y =>
    (rvachevUp F y : ℂ) * (2 * z + 1 - (y : ℂ))⁻¹
  let gm : ℝ → ℂ := fun y =>
    (rvachevUp F y : ℂ) * (2 * z - 1 - (y : ℂ))⁻¹
  have hp_sub :
      (∫ t in (-1 : ℝ)..0, p t) =
        ∫ y in (-1 : ℝ)..1, gp y := by
    calc
      (∫ t in (-1 : ℝ)..0, p t) =
          (2 : ℝ) • ∫ t in (-1 : ℝ)..0, gp (2 * t + 1) := by
        rw [← intervalIntegral.integral_smul]
        apply intervalIntegral.integral_congr
        intro t _ht
        dsimp only [p, gp, k]
        have hden :
            2 * z + 1 - ((2 * t + 1 : ℝ) : ℂ) =
              2 * (z - (t : ℂ)) := by
          push_cast
          ring
        rw [hden, mul_inv]
        simp only [Complex.real_smul]
        norm_num
        ring
      _ = ∫ y in (-1 : ℝ)..1, gp y := by
        convert
          (intervalIntegral.smul_integral_comp_mul_add
            (f := gp) (a := (-1 : ℝ)) (b := 0) 2 1) using 1
        all_goals norm_num
  have hm_sub :
      (∫ t in (0 : ℝ)..1, m t) =
        ∫ y in (-1 : ℝ)..1, gm y := by
    calc
      (∫ t in (0 : ℝ)..1, m t) =
          (2 : ℝ) • ∫ t in (0 : ℝ)..1, gm (2 * t - 1) := by
        rw [← intervalIntegral.integral_smul]
        apply intervalIntegral.integral_congr
        intro t _ht
        dsimp only [m, gm, k]
        have hden :
            2 * z - 1 - ((2 * t - 1 : ℝ) : ℂ) =
              2 * (z - (t : ℂ)) := by
          push_cast
          ring
        rw [hden, mul_inv]
        simp only [Complex.real_smul]
        norm_num
        ring
      _ = ∫ y in (-1 : ℝ)..1, gm y := by
        convert
          (intervalIntegral.smul_integral_comp_mul_sub
            (f := gm) (a := (0 : ℝ)) (b := 1) 2 1) using 1
        all_goals norm_num
  have hp_eq :
      (∫ t in (-1 : ℝ)..1, p t) =
        rvachevCauchyTransform F (2 * z + 1) := by
    calc
      (∫ t in (-1 : ℝ)..1, p t) =
          (∫ t in (-1 : ℝ)..0, p t) + ∫ t in (0 : ℝ)..1, p t :=
        (intervalIntegral.integral_add_adjacent_intervals hp_left hp_right).symm
      _ = ∫ t in (-1 : ℝ)..0, p t := by rw [hp_zero, add_zero]
      _ = ∫ y in (-1 : ℝ)..1, gp y := hp_sub
      _ = rvachevCauchyTransform F (2 * z + 1) := by
        simpa only [gp] using
          (rvachevCauchyTransform_eq_intervalIntegral F hF (2 * z + 1)).symm
  have hm_eq :
      (∫ t in (-1 : ℝ)..1, m t) =
        rvachevCauchyTransform F (2 * z - 1) := by
    calc
      (∫ t in (-1 : ℝ)..1, m t) =
          (∫ t in (-1 : ℝ)..0, m t) + ∫ t in (0 : ℝ)..1, m t :=
        (intervalIntegral.integral_add_adjacent_intervals hm_left hm_right).symm
      _ = ∫ t in (0 : ℝ)..1, m t := by rw [hm_zero, zero_add]
      _ = ∫ y in (-1 : ℝ)..1, gm y := hm_sub
      _ = rvachevCauchyTransform F (2 * z - 1) := by
        simpa only [gm] using
          (rvachevCauchyTransform_eq_intervalIntegral F hF (2 * z - 1)).symm
  have horbit :
      (∫ t in (-1 : ℝ)..1, u' t * k t) =
        2 * (rvachevCauchyTransform F (2 * z + 1) -
          rvachevCauchyTransform F (2 * z - 1)) := by
    have hp_int : IntervalIntegrable p volume (-1) 1 :=
      hp_cont.intervalIntegrable_of_Icc (by norm_num)
    have hm_int : IntervalIntegrable m volume (-1) 1 :=
      hm_cont.intervalIntegrable_of_Icc (by norm_num)
    calc
      (∫ t in (-1 : ℝ)..1, u' t * k t) =
          2 * ((∫ t in (-1 : ℝ)..1, p t) -
            ∫ t in (-1 : ℝ)..1, m t) := by
        rw [← intervalIntegral.integral_sub hp_int hm_int,
          ← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro t _ht
        dsimp only [u', p, m]
        ring
      _ = 2 * (rvachevCauchyTransform F (2 * z + 1) -
          rvachevCauchyTransform F (2 * z - 1)) := by rw [hp_eq, hm_eq]
  have hmeasure :
      (∫ x : ℝ, (z - (x : ℂ))⁻¹ ^ 2 ∂rvachevMeasure F) =
        ∫ x : ℝ,
          (rvachevUp F x : ℂ) * (z - (x : ℂ))⁻¹ ^ 2 := by
    rw [rvachevMeasure, integral_withDensity_eq_integral_toReal_smul]
    · apply integral_congr_ae
      filter_upwards with x
      rw [ENNReal.toReal_ofReal (rvachevUp_nonneg F x)]
      simp only [Complex.real_smul]
    · exact ENNReal.measurable_ofReal.comp
        (rvachev_contDiff F hF).continuous.measurable
    · exact Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hderiv := hasDerivAt_rvachevCauchyTransform F hF hz
  rw [hmeasure,
    integral_rvachevUp_mul_eq_intervalIntegral F hF
      (fun x : ℝ => (z - (x : ℂ))⁻¹ ^ 2)] at hderiv
  change HasDerivAt (rvachevCauchyTransform F)
    (-(∫ t in (-1 : ℝ)..1, u t * k' t)) z at hderiv
  rw [hparts, horbit] at hderiv
  exact hderiv

/-- Derivative-value form of the Rvachev Cauchy-transform differential
equation. -/
theorem deriv_rvachevCauchyTransform
    (F : BoundedFabius) (hF : IsFabius F) {z : ℂ}
    (hz : z ∈ rvachevCauchyDomain) :
    deriv (rvachevCauchyTransform F) z =
      2 * (rvachevCauchyTransform F (2 * z + 1) -
        rvachevCauchyTransform F (2 * z - 1)) :=
  (hasDerivAt_rvachevCauchyTransform_affineDifference F hF hz).deriv

/-! ## All-order affine orbit -/

/-- **All complex derivatives of the Rvachev Cauchy transform form a finite
Thue--Morse affine orbit.**  The coefficient contains the `2^n` from the
differential equation and the triangular chain-rule factor
`2^(n.choose 2)`. -/
theorem iteratedDeriv_rvachevCauchyTransform_eq_thueMorse_sum
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) {z : ℂ}
    (hz : z ∈ rvachevCauchyDomain) :
    iteratedDeriv n (rvachevCauchyTransform F) z =
      (2 : ℂ) ^ (n + 1).choose 2 *
        ∑ j ∈ range (2 ^ n), (thueMorseSign j : ℂ) *
          rvachevCauchyTransform F
            ((2 : ℂ) ^ n * z + (2 : ℂ) ^ n - 1 - 2 * (j : ℂ)) := by
  have h := iteratedDeriv_eq_affineDifference_iterate_on
    isOpen_rvachevCauchyDomain
    mapsTo_rvachevCauchyDomain_two_mul_add_one
    mapsTo_rvachevCauchyDomain_two_mul_sub_one
    (rvachevCauchyTransform F)
    (fun w hw => by
      simpa only [affineDifference, smul_eq_mul] using
        hasDerivAt_rvachevCauchyTransform_affineDifference F hF hw)
    n hz
  rw [affineDifference_iterate_two_one_apply] at h
  have hchoose : (n + 1).choose 2 = n.choose 2 + n := by
    rw [Nat.choose_succ_succ]
    simp [add_comm]
  simpa only [smul_eq_mul, zsmul_eq_mul, hchoose, pow_add, mul_comm] using h

end Fabius
