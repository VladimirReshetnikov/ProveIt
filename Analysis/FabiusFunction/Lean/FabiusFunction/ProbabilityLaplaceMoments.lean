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
* a general compact-probability Fubini identity for expectations of
  differentiable functions, expressed through the survival function;
* a reflection principle and exact degree-zero normalizations for arbitrary
  probability laws supported on the unit interval; and
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

/-- Integration by parts for a probability law supported on `[a,b]`, written
in terms of its survival function.  In probabilistic notation this is

`E[g(X)] = g(a) + ∫ₐᵇ g'(t) P(X > t) dt`.

The theorem is independent of the Fabius law; the specialized Rvachev form
below is obtained by setting `a = 0`, `b = 1` and identifying the weighted-sum
survival function.  Both continuity hypotheses are local to `[a,b]`. -/
theorem integral_Icc_eq_left_add_intervalIntegral_deriv_mul_survival
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {a b : ℝ} (hab : a ≤ b) (hμ : ∀ᵐ x ∂μ, x ∈ Icc a b)
    (g g' : ℝ → ℝ) (hg : ContinuousOn g (Icc a b))
    (hg' : ContinuousOn g' (Icc a b))
    (hderiv : ∀ x ∈ Icc a b, HasDerivAt g (g' x) x) :
    (∫ x in Icc a b, g x ∂μ) =
      g a + ∫ t in a..b, g' t * μ.real (Ioi t) := by
  let ν : Measure ℝ := volume.restrict (Icc a b)
  let A : Set (ℝ × ℝ) := {z | z.1 < z.2}
  let H : ℝ × ℝ → ℝ := fun z => A.indicator (fun z => g' z.1) z
  have hA : MeasurableSet A := by
    dsimp [A]
    exact measurableSet_lt measurable_fst measurable_snd
  have hg'ν : Integrable g' ν := by
    dsimp [ν]
    exact hg'.integrableOn_Icc
  have hH : Integrable H (ν.prod μ) := by
    have hbase : Integrable (fun z : ℝ × ℝ => g' z.1 * (1 : ℝ))
        (ν.prod μ) :=
      hg'ν.mul_prod (integrable_const (1 : ℝ))
    have hi := hbase.indicator hA
    simpa only [H, one_mul, mul_one] using hi
  have hrestrict : μ.restrict (Icc a b) = μ :=
    Measure.restrict_eq_self_of_ae_mem hμ
  have hgμ : Integrable g μ := by
    rw [← hrestrict]
    exact hg.integrableOn_Icc
  have hinner_t (x : ℝ) (hx : x ∈ Icc a b) :
      (∫ t : ℝ, H (t, x) ∂ν) = g x - g a := by
    have hind : (fun t : ℝ => H (t, x)) = (Iio x).indicator g' := by
      funext t
      simp only [H, A, Set.indicator, mem_setOf_eq, mem_Iio]
    rw [hind, integral_indicator measurableSet_Iio]
    change (∫ t : ℝ, g' t ∂(ν.restrict (Iio x))) = _
    rw [show ν.restrict (Iio x) = volume.restrict (Ico a x) by
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
    · exact
        (hg'.mono (Icc_subset_Icc_right hx.2)).intervalIntegrable_of_Icc hx.1
  have hinner_x (t : ℝ) :
      (∫ x : ℝ, H (t, x) ∂μ) = g' t * μ.real (Ioi t) := by
    have hind : (fun x : ℝ => H (t, x)) =
        (Ioi t).indicator (fun _ => g' t) := by
      funext x
      simp only [H, A, Set.indicator, mem_setOf_eq, mem_Ioi]
    rw [hind, integral_indicator_const (g' t) measurableSet_Ioi]
    simp only [smul_eq_mul]
    ring
  have horder_x :
      (∫ x : ℝ, ∫ t : ℝ, H (t, x) ∂ν ∂μ) =
        (∫ x : ℝ, g x ∂μ) - g a := by
    calc
      (∫ x : ℝ, ∫ t : ℝ, H (t, x) ∂ν ∂μ) =
          ∫ x : ℝ, (g x - g a) ∂μ := by
            apply integral_congr_ae
            filter_upwards [hμ] with x hx
            exact hinner_t x hx
      _ = (∫ x : ℝ, g x ∂μ) - g a := by
        rw [integral_sub hgμ (integrable_const _), integral_const,
          probReal_univ, one_smul]
  have horder_t :
      (∫ t : ℝ, ∫ x : ℝ, H (t, x) ∂μ ∂ν) =
        ∫ t in a..b, g' t * μ.real (Ioi t) := by
    calc
      (∫ t : ℝ, ∫ x : ℝ, H (t, x) ∂μ ∂ν) =
          ∫ t in Icc a b, g' t * μ.real (Ioi t) := by
            apply integral_congr_ae
            filter_upwards [ae_restrict_mem measurableSet_Icc] with t _ht
            exact hinner_x t
      _ = ∫ t in a..b, g' t * μ.real (Ioi t) := by
        rw [intervalIntegral.integral_of_le hab,
          integral_Icc_eq_integral_Ioc]
  have hswap :
      (∫ x : ℝ, ∫ t : ℝ, H (t, x) ∂ν ∂μ) =
        ∫ t : ℝ, ∫ x : ℝ, H (t, x) ∂μ ∂ν := by
    exact (integral_prod_symm H hH).symm.trans (integral_prod H hH)
  rw [horder_x, horder_t] at hswap
  rw [show (∫ x in Icc a b, g x ∂μ) = ∫ x : ℝ, g x ∂μ by
    rw [hrestrict]]
  linarith

/-- Unit-interval form of
`integral_Icc_eq_left_add_intervalIntegral_deriv_mul_survival`. -/
theorem integral_unit_eq_zero_add_integral_deriv_mul_survival
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc (0 : ℝ) 1)
    (g g' : ℝ → ℝ)
    (hg : ContinuousOn g (Icc (0 : ℝ) 1))
    (hg' : ContinuousOn g' (Icc (0 : ℝ) 1))
    (hderiv : ∀ x ∈ Icc (0 : ℝ) 1, HasDerivAt g (g' x) x) :
    (∫ x in Icc (0 : ℝ) 1, g x ∂μ) =
      g 0 + ∫ t in (0 : ℝ)..1, g' t * μ.real (Ioi t) :=
  integral_Icc_eq_left_add_intervalIntegral_deriv_mul_survival
    μ (by norm_num) hμ g g' hg hg' hderiv

/-- A measure supported on `[0,1]` and invariant under reflection about
`1/2` has equal endpoint and ordinary moments. -/
theorem unitEndpointMoment_eq_unitLaplaceMoment_zero_of_reflection
    (μ : Measure ℝ) (hμ : ∀ᵐ x ∂μ, x ∈ Icc (0 : ℝ) 1)
    (hreflect : μ.map (fun x : ℝ => 1 - x) = μ) (n : ℕ) :
    unitEndpointMoment μ n = unitLaplaceMoment μ 0 n := by
  let r : ℝ → ℝ := fun x => 1 - x
  have hr : Measurable r := by
    dsimp [r]
    fun_prop
  have hmap :
      (∫ y : ℝ, y ^ n ∂μ.map r) = ∫ x : ℝ, (1 - x) ^ n ∂μ := by
    simpa only [r, Pi.pow_apply, id_eq] using integral_map hr.aemeasurable
      (continuous_id.pow n).aestronglyMeasurable
  have hreflect' :
      (∫ x : ℝ, (1 - x) ^ n ∂μ) = ∫ x : ℝ, x ^ n ∂μ := by
    rw [← hmap, hreflect]
  have hrestrict : μ.restrict (Icc (0 : ℝ) 1) = μ :=
    Measure.restrict_eq_self_of_ae_mem hμ
  calc
    unitEndpointMoment μ n = ∫ x : ℝ, (1 - x) ^ n ∂μ := by
      unfold unitEndpointMoment
      rw [hrestrict]
    _ = ∫ x : ℝ, x ^ n ∂μ := hreflect'
    _ = unitLaplaceMoment μ 0 n := by
      unfold unitLaplaceMoment
      rw [hrestrict]
      simp

/-- The zero-tilt zeroth moment of a unit-interval probability law is one. -/
theorem unitLaplaceMoment_zero_zero_of_ae_mem_Icc
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc (0 : ℝ) 1) :
    unitLaplaceMoment μ 0 0 = 1 := by
  unfold unitLaplaceMoment
  rw [Measure.restrict_eq_self_of_ae_mem hμ]
  simp

/-- The zeroth endpoint moment of a unit-interval probability law is one. -/
theorem unitEndpointMoment_zero_of_ae_mem_Icc
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, x ∈ Icc (0 : ℝ) 1) :
    unitEndpointMoment μ 0 = 1 := by
  unfold unitEndpointMoment
  rw [Measure.restrict_eq_self_of_ae_mem hμ]
  simp

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
  calc
    (∫ x in Icc (0 : ℝ) 1, g x ∂weightedSumDistribution) =
        g 0 + ∫ t in (0 : ℝ)..1,
          g' t * weightedSumDistribution.real (Ioi t) :=
      integral_unit_eq_zero_add_integral_deriv_mul_survival
        weightedSumDistribution ae_weightedSumDistribution_mem_Icc
        g g' hg.continuousOn hg'.continuousOn hderiv
    _ = g 0 + ∫ t in (0 : ℝ)..1, g' t * rvachevUp F t := by
      apply congrArg (fun y : ℝ => g 0 + y)
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      change g' t * weightedSumDistribution.real (Ioi t) =
        g' t * rvachevUp F t
      rw [weightedSumDistribution_real_Ioi_eq_rvachevUp F hF ht]

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
  exact unitEndpointMoment_eq_unitLaplaceMoment_zero_of_reflection
    weightedSumDistribution ae_weightedSumDistribution_mem_Icc
    weightedSumDistribution_reflection n

/-- The zero-tilt zeroth moment has total mass one. -/
@[simp] theorem unitLaplaceMoment_weightedSumDistribution_zero_zero :
    unitLaplaceMoment weightedSumDistribution 0 0 = 1 := by
  exact unitLaplaceMoment_zero_zero_of_ae_mem_Icc
    weightedSumDistribution ae_weightedSumDistribution_mem_Icc

/-- Exact endpoint-moment normalization in degree zero. -/
@[simp] theorem unitEndpointMoment_weightedSumDistribution_zero :
    unitEndpointMoment weightedSumDistribution 0 = 1 := by
  exact unitEndpointMoment_zero_of_ae_mem_Icc
    weightedSumDistribution ae_weightedSumDistribution_mem_Icc

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
