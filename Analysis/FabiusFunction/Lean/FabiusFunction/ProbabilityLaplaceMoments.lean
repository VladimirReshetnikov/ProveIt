import FabiusFunction.LaplaceMoments
import FabiusFunction.ProbabilityRepresentation

/-!
# Probability-law Laplace moments

This module isolates the measure-theoretic bridge between the probabilistic
weighted-sum construction and the real Laplace moments of the Fabius law.  It
provides:

* endpoint and exponentially tilted raw moments on the unit interval;
* almost-sure support and restriction identities for the weighted-sum law;
* its survival function on the full nonnegative ray;
* a compact-support Fubini identity for expectations of differentiable
  functions; and
* the resulting identifications with `fabiusLaplaceMoment` and
  `halfMoment`, including the reflection and degree-zero normalizations.

Keeping this bridge separate lets probabilistic and complex-MGF developments
use it without importing the quantitative endpoint/Laplace comparison.
`EndpointLaplaceComparison` imports this module and therefore continues to
re-export the complete API.
-/

set_option autoImplicit false

open Filter Set MeasureTheory
open scoped Topology

namespace Fabius

/-- The `n`th endpoint moment of a measure, restricted to the unit interval. -/
noncomputable def unitEndpointMoment (μ : Measure ℝ) (n : ℕ) : ℝ :=
  ∫ x in Icc (0 : ℝ) 1, (1 - x) ^ n ∂μ

/-- The `k`th raw moment under the exponentially tilted unit-interval measure. -/
noncomputable def unitLaplaceMoment (μ : Measure ℝ) (s : ℝ) (k : ℕ) : ℝ :=
  ∫ x in Icc (0 : ℝ) 1, Real.exp (-s * x) * x ^ k ∂μ

/-- Unit-interval Laplace moments are nonnegative at every real tilt. -/
lemma unitLaplaceMoment_nonneg (μ : Measure ℝ) (s : ℝ) (k : ℕ) :
    0 ≤ unitLaplaceMoment μ s k := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact mul_nonneg (Real.exp_nonneg _) (pow_nonneg hx.1 k)

namespace ProbabilityRepresentation

/-- The weighted-sum law is almost surely supported on the unit interval. -/
lemma ae_weightedSumDistribution_mem_Icc :
    ∀ᵐ x ∂weightedSumDistribution, x ∈ Icc (0 : ℝ) 1 := by
  unfold weightedSumDistribution
  apply (ae_map_iff measurable_weightedCoordinateSum.aemeasurable
    (show MeasurableSet {x : ℝ | x ∈ Icc (0 : ℝ) 1} by
      exact measurableSet_Icc)).2
  filter_upwards with ω
  exact ⟨weightedCoordinateSum_nonneg ω, weightedCoordinateSum_le_one ω⟩

/-- Restricting the weighted-sum law to its unit-interval support changes no mass. -/
lemma weightedSumDistribution_restrict_Icc :
    weightedSumDistribution.restrict (Icc (0 : ℝ) 1) =
      weightedSumDistribution :=
  Measure.restrict_eq_self_of_ae_mem ae_weightedSumDistribution_mem_Icc

/-- The survival function of the weighted-sum law is Rvachev's bump on the
whole nonnegative ray, including beyond the compact support. -/
lemma weightedSumDistribution_real_Ioi_eq_rvachevUp_of_nonneg
    (F : BoundedFabius) (hF : IsFabius F) {t : ℝ} (ht : 0 ≤ t) :
    weightedSumDistribution.real (Ioi t) = rvachevUp F t := by
  calc
    weightedSumDistribution.real (Ioi t) =
        1 - weightedSumDistribution.real (Iic t) := by
      rw [← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic]
    _ = 1 - weightedSumCDF t := by
      rw [weightedSumCDF, ProbabilityTheory.cdf_eq_real]
    _ = 1 - fabiusReal F t := by
      rw [weightedSumCDF_eq_fabiusReal F hF t]
    _ = rvachevUp F t :=
      (rvachevUp_eq_one_sub_fabiusReal_of_nonneg F hF ht).symm

/-- Unit-interval compatibility form of
`weightedSumDistribution_real_Ioi_eq_rvachevUp_of_nonneg`. -/
lemma weightedSumDistribution_real_Ioi_eq_rvachevUp
    (F : BoundedFabius) (hF : IsFabius F) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) :
    weightedSumDistribution.real (Ioi t) = rvachevUp F t :=
  weightedSumDistribution_real_Ioi_eq_rvachevUp_of_nonneg F hF ht.1

/-- Integration against the weighted-sum law in terms of the survival
function `rvachevUp`.  This is the compact-support expectation identity
`E[g(X)] = g(0) + ∫ g'(t) P(X > t) dt`. -/
theorem integral_unit_eq_zero_add_integral_deriv_mul_rvachevUp
    (F : BoundedFabius) (hF : IsFabius F)
    (g g' : ℝ → ℝ) (hg : Continuous g) (hg' : Continuous g')
    (hderiv : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivAt g (g' x) x) :
    (∫ x in Icc (0 : ℝ) 1, g x ∂weightedSumDistribution) =
      g 0 + ∫ t in (0 : ℝ)..1, g' t * rvachevUp F t := by
  let ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)
  let A : Set (ℝ × ℝ) := {z | z.1 < z.2}
  let H : ℝ × ℝ → ℝ := fun z => A.indicator (fun z => g' z.1) z
  have hA : MeasurableSet A := by
    dsimp [A]
    exact measurableSet_lt measurable_fst measurable_snd
  have hg'ν : Integrable g' ν := by
    dsimp [ν]
    exact hg'.integrableOn_Icc
  have hH : Integrable H (ν.prod weightedSumDistribution) := by
    have hbase : Integrable (fun z : ℝ × ℝ => g' z.1 * (1 : ℝ))
        (ν.prod weightedSumDistribution) :=
      hg'ν.mul_prod (integrable_const (1 : ℝ))
    have hi := hbase.indicator hA
    simpa only [H, one_mul, mul_one] using hi
  have hgμ : Integrable g weightedSumDistribution := by
    rw [← weightedSumDistribution_restrict_Icc]
    exact hg.integrableOn_Icc
  have hinner_t (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      (∫ t : ℝ, H (t, x) ∂ν) = g x - g 0 := by
    have hind : (fun t : ℝ => H (t, x)) = (Iio x).indicator g' := by
      funext t
      simp only [H, A, Set.indicator, mem_setOf_eq, mem_Iio]
    rw [hind, integral_indicator measurableSet_Iio]
    change (∫ t : ℝ, g' t ∂(ν.restrict (Iio x))) = _
    rw [show ν.restrict (Iio x) = volume.restrict (Ico 0 x) by
      dsimp [ν]
      rw [Measure.restrict_restrict measurableSet_Iio]
      congr 1
      ext t
      simp only [mem_inter_iff, mem_Iio, mem_Icc, mem_Ico]
      constructor <;> intro ht
      · exact ⟨ht.2.1, ht.1⟩
      · exact ⟨ht.2, ht.1, (ht.2.trans_le hx.2).le⟩]
    rw [integral_Ico_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hx.1]
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      apply hderiv t
      rw [uIcc_of_le hx.1] at ht
      exact ⟨ht.1, ht.2.trans hx.2⟩
    · exact hg'.intervalIntegrable 0 x
  have hinner_x (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (∫ x : ℝ, H (t, x) ∂weightedSumDistribution) =
        g' t * rvachevUp F t := by
    have hind : (fun x : ℝ => H (t, x)) =
        (Ioi t).indicator (fun _ => g' t) := by
      funext x
      simp only [H, A, Set.indicator, mem_setOf_eq, mem_Ioi]
    rw [hind, integral_indicator_const (g' t) measurableSet_Ioi]
    rw [weightedSumDistribution_real_Ioi_eq_rvachevUp F hF ht]
    simp only [smul_eq_mul]
    ring
  have horder_x :
      (∫ x : ℝ, ∫ t : ℝ, H (t, x) ∂ν ∂weightedSumDistribution) =
        (∫ x : ℝ, g x ∂weightedSumDistribution) - g 0 := by
    calc
      (∫ x : ℝ, ∫ t : ℝ, H (t, x) ∂ν ∂weightedSumDistribution) =
          ∫ x : ℝ, (g x - g 0) ∂weightedSumDistribution := by
            apply integral_congr_ae
            filter_upwards [ae_weightedSumDistribution_mem_Icc] with x hx
            exact hinner_t x hx
      _ = (∫ x : ℝ, g x ∂weightedSumDistribution) - g 0 := by
        rw [integral_sub hgμ (integrable_const _), integral_const,
          probReal_univ, one_smul]
  have horder_t :
      (∫ t : ℝ, ∫ x : ℝ, H (t, x) ∂weightedSumDistribution ∂ν) =
        ∫ t in (0 : ℝ)..1, g' t * rvachevUp F t := by
    calc
      (∫ t : ℝ, ∫ x : ℝ, H (t, x) ∂weightedSumDistribution ∂ν) =
          ∫ t in Icc (0 : ℝ) 1, g' t * rvachevUp F t := by
            apply integral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
            exact hinner_x t ht
      _ = ∫ t in (0 : ℝ)..1, g' t * rvachevUp F t := by
        rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
          integral_Icc_eq_integral_Ioc]
  have hswap :
      (∫ x : ℝ, ∫ t : ℝ, H (t, x) ∂ν ∂weightedSumDistribution) =
        ∫ t : ℝ, ∫ x : ℝ, H (t, x) ∂weightedSumDistribution ∂ν := by
    exact (integral_prod_symm H hH).symm.trans (integral_prod H hH)
  rw [horder_x, horder_t] at hswap
  rw [show (∫ x in Icc (0 : ℝ) 1, g x ∂weightedSumDistribution) =
      ∫ x : ℝ, g x ∂weightedSumDistribution by
    rw [weightedSumDistribution_restrict_Icc]]
  linarith

/-- The raw Laplace moments of the weighted-sum probability law are the
survival-function moments from `LaplaceMoments`. -/
theorem unitLaplaceMoment_weightedSumDistribution_eq_fabiusLaplaceMoment
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ) (s : ℝ) :
    unitLaplaceMoment weightedSumDistribution s k =
      fabiusLaplaceMoment F k s := by
  cases k with
  | zero =>
      let g : ℝ → ℝ := fun x => Real.exp (-s * x)
      let g' : ℝ → ℝ := fun x =>
        Real.exp (-s * x) * (-s * 1)
      have hderiv (x : ℝ) : HasDerivAt g (g' x) x := by
        dsimp [g, g']
        simpa only [id_eq] using ((hasDerivAt_id x).const_mul (-s)).exp
      have h := integral_unit_eq_zero_add_integral_deriv_mul_rvachevUp
        F hF g g' (by fun_prop) (by fun_prop) (fun x _ => hderiv x)
      have htilt :
          (∫ t in (0 : ℝ)..1, g' t * rvachevUp F t) =
            -s * tiltedSurvivalMoment F 0 s := by
        unfold tiltedSurvivalMoment
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro t _ht
        dsimp [g']
        simp only [pow_zero, one_mul]
        ring
      rw [htilt] at h
      simpa [unitLaplaceMoment, g, fabiusLaplaceMoment,
        generatingFunction, tiltedSurvivalMoment] using h
  | succ k =>
      let g : ℝ → ℝ :=
        (fun x => Real.exp (-s * x)) * fun x => x ^ (k + 1)
      let g' : ℝ → ℝ := fun x =>
        Real.exp (-s * x) * (-s * 1) * x ^ (k + 1) +
          Real.exp (-s * x) *
            (((k + 1 : ℕ) : ℝ) * x ^ (k + 1 - 1))
      have hderiv (x : ℝ) : HasDerivAt g (g' x) x := by
        dsimp [g, g']
        simpa only [id_eq, Nat.add_sub_cancel] using
          ((hasDerivAt_id x).const_mul (-s)).exp.mul
            (hasDerivAt_pow (k + 1) x)
      have h := integral_unit_eq_zero_add_integral_deriv_mul_rvachevUp
        F hF g g' (by fun_prop) (by fun_prop) (fun x _ => hderiv x)
      have hIk : IntervalIntegrable
          (fun t : ℝ => t ^ k * rvachevUp F t * Real.exp (-s * t))
          volume 0 1 := by
        apply Continuous.intervalIntegrable
        exact ((continuous_id.pow k).mul
          (rvachev_contDiff F hF).continuous).mul (by fun_prop)
      have hIk1 : IntervalIntegrable
          (fun t : ℝ => t ^ (k + 1) * rvachevUp F t * Real.exp (-s * t))
          volume 0 1 := by
        apply Continuous.intervalIntegrable
        exact ((continuous_id.pow (k + 1)).mul
          (rvachev_contDiff F hF).continuous).mul (by fun_prop)
      have htilt :
          (∫ t in (0 : ℝ)..1, g' t * rvachevUp F t) =
            (k + 1 : ℝ) * tiltedSurvivalMoment F k s -
              s * tiltedSurvivalMoment F (k + 1) s := by
        calc
          (∫ t in (0 : ℝ)..1, g' t * rvachevUp F t) =
              ∫ t in (0 : ℝ)..1,
                ((k + 1 : ℝ) *
                    (t ^ k * rvachevUp F t * Real.exp (-s * t)) -
                  s * (t ^ (k + 1) * rvachevUp F t *
                    Real.exp (-s * t))) := by
                apply intervalIntegral.integral_congr
                intro t _ht
                dsimp [g']
                push_cast
                ring
          _ = (k + 1 : ℝ) *
                (∫ t in (0 : ℝ)..1,
                  t ^ k * rvachevUp F t * Real.exp (-s * t)) -
              s * (∫ t in (0 : ℝ)..1,
                t ^ (k + 1) * rvachevUp F t * Real.exp (-s * t)) := by
                rw [intervalIntegral.integral_sub
                  (hIk.const_mul _) (hIk1.const_mul _),
                  intervalIntegral.integral_const_mul,
                  intervalIntegral.integral_const_mul]
          _ = (k + 1 : ℝ) * tiltedSurvivalMoment F k s -
              s * tiltedSurvivalMoment F (k + 1) s := by
                rfl
      rw [htilt] at h
      simpa [unitLaplaceMoment, g, fabiusLaplaceMoment] using h

/-- Reflection invariance identifies the endpoint power moment with the
ordinary raw moment, represented here as the zero-tilt Laplace moment. -/
theorem unitEndpointMoment_weightedSumDistribution_eq_unitLaplaceMoment_zero
    (n : ℕ) :
    unitEndpointMoment weightedSumDistribution n =
      unitLaplaceMoment weightedSumDistribution 0 n := by
  let r : ℝ → ℝ := fun x => 1 - x
  have hr : Measurable r := by
    dsimp [r]
    fun_prop
  have hmap :
      (∫ y : ℝ, y ^ n ∂weightedSumDistribution.map r) =
        ∫ x : ℝ, (1 - x) ^ n ∂weightedSumDistribution := by
    simpa only [r, Pi.pow_apply, id_eq] using integral_map hr.aemeasurable
      (continuous_id.pow n).aestronglyMeasurable
  have hreflect :
      (∫ x : ℝ, (1 - x) ^ n ∂weightedSumDistribution) =
        ∫ x : ℝ, x ^ n ∂weightedSumDistribution := by
    rw [← hmap, weightedSumDistribution_reflection]
  calc
    unitEndpointMoment weightedSumDistribution n =
        ∫ x : ℝ, (1 - x) ^ n ∂weightedSumDistribution := by
      unfold unitEndpointMoment
      rw [weightedSumDistribution_restrict_Icc]
    _ = ∫ x : ℝ, x ^ n ∂weightedSumDistribution := hreflect
    _ = unitLaplaceMoment weightedSumDistribution 0 n := by
      unfold unitLaplaceMoment
      rw [weightedSumDistribution_restrict_Icc]
      simp

/-- The zero-tilt zeroth moment has total mass one. -/
@[simp] theorem unitLaplaceMoment_weightedSumDistribution_zero_zero :
    unitLaplaceMoment weightedSumDistribution 0 0 = 1 := by
  unfold unitLaplaceMoment
  rw [weightedSumDistribution_restrict_Icc]
  simp

/-- Exact endpoint-moment normalization in degree zero. -/
@[simp] theorem unitEndpointMoment_weightedSumDistribution_zero :
    unitEndpointMoment weightedSumDistribution 0 = 1 := by
  rw [unitEndpointMoment_weightedSumDistribution_eq_unitLaplaceMoment_zero,
    unitLaplaceMoment_weightedSumDistribution_zero_zero]

/-- At zero tilt, the raw moments of the weighted-sum law are exactly the
rational half moments. -/
theorem unitLaplaceMoment_weightedSumDistribution_zero_eq_halfMoment
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    unitLaplaceMoment weightedSumDistribution 0 n = (halfMoment n : ℝ) := by
  calc
    unitLaplaceMoment weightedSumDistribution 0 n =
        fabiusLaplaceMoment F n 0 :=
      unitLaplaceMoment_weightedSumDistribution_eq_fabiusLaplaceMoment
        F hF n 0
    _ = (halfMoment n : ℝ) :=
      fabiusLaplaceMoment_zero_eq_halfMoment F hF n

/-- Reflection invariance identifies the endpoint power moment with the
ordinary power moment, hence with `halfMoment`. -/
theorem unitEndpointMoment_weightedSumDistribution_eq_halfMoment
    (F : BoundedFabius) (hF : IsFabius F) (n : ℕ) :
    unitEndpointMoment weightedSumDistribution n = (halfMoment n : ℝ) := by
  calc
    unitEndpointMoment weightedSumDistribution n =
        unitLaplaceMoment weightedSumDistribution 0 n :=
      unitEndpointMoment_weightedSumDistribution_eq_unitLaplaceMoment_zero n
    _ = (halfMoment n : ℝ) :=
      unitLaplaceMoment_weightedSumDistribution_zero_eq_halfMoment F hF n

end ProbabilityRepresentation

/-- Every real tilted Fabius moment is nonnegative. -/
lemma fabiusLaplaceMoment_nonneg
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ) (s : ℝ) :
    0 ≤ fabiusLaplaceMoment F k s := by
  rw [← ProbabilityRepresentation.unitLaplaceMoment_weightedSumDistribution_eq_fabiusLaplaceMoment
    F hF k s]
  exact unitLaplaceMoment_nonneg _ _ _

end Fabius
