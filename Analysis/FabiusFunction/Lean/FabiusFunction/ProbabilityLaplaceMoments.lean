import FabiusFunction.NegativeLaplaceDerivatives
import FabiusFunction.ProbabilityRepresentation
import FabiusFunction.SurvivalLayerCake
import Mathlib.Data.Nat.Choose.Sum

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
* reflection principles for unrestricted and unit-restricted integrals, and
  the resulting signed binomial transforms of the complete raw and normalized
  tilted-moment hierarchies;
* complementarity and centered oddness of opposite tilted means, together with
  evenness of the tilted variance;
* centered Laplace functional equations and exact degree-zero normalizations
  for arbitrary probability laws supported on the unit interval; and
* the resulting identifications with `fabiusLaplaceMoment` and
  `halfMoment`, including the reflection and degree-zero normalizations.

Keeping this bridge separate lets probabilistic and complex-MGF developments
use it without importing the quantitative endpoint/Laplace comparison.
`EndpointLaplaceComparison` imports this module and therefore continues to
re-export the complete API.
-/

set_option autoImplicit false

open Filter Set MeasureTheory
open scoped BigOperators Topology

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
  have hrestrict : μ.restrict (Icc a b) = μ :=
    Measure.restrict_eq_self_of_ae_mem hμ
  have hgμ : Integrable g μ := by
    rw [← hrestrict]
    exact hg.integrableOn_Icc
  have hg'int : IntervalIntegrable g' volume a b :=
    hg'.intervalIntegrable_of_Icc hab
  have hsurvival :=
    intervalIntegral_survival_smul_eq_integral_of_ae_mem_Icc
      μ hab hμ g' hg'int
  have hprimitive :
      ∀ᵐ x ∂μ, (∫ t in a..x, g' t) = g x - g a := by
    filter_upwards [hμ] with x hx
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro t ht
      rw [uIcc_of_le hx.1] at ht
      exact hderiv t ⟨ht.1, ht.2.trans hx.2⟩
    · exact
        (hg'.mono (Icc_subset_Icc_right hx.2)).intervalIntegrable_of_Icc hx.1
  have hstopped :
      (∫ x : ℝ, (∫ t in a..x, g' t) ∂μ) =
        (∫ x : ℝ, g x ∂μ) - g a := by
    calc
      (∫ x : ℝ, (∫ t in a..x, g' t) ∂μ) =
          ∫ x : ℝ, (g x - g a) ∂μ := integral_congr_ae hprimitive
      _ = (∫ x : ℝ, g x ∂μ) - g a := by
        rw [integral_sub hgμ (integrable_const _), integral_const,
          probReal_univ, one_smul]
  have hsurvival' :
      (∫ t in a..b, g' t * μ.real (Ioi t)) =
        ∫ x : ℝ, (∫ t in a..x, g' t) ∂μ := by
    calc
      (∫ t in a..b, g' t * μ.real (Ioi t)) =
          ∫ t in a..b, μ.real (Ioi t) • g' t := by
        apply intervalIntegral.integral_congr
        intro t _ht
        simp only [smul_eq_mul]
        ring
      _ = ∫ x : ℝ, (∫ t in a..x, g' t) ∂μ := hsurvival
  rw [show (∫ x in Icc a b, g x ∂μ) = ∫ x : ℝ, g x ∂μ by
    rw [hrestrict]]
  rw [hsurvival', hstopped]
  ring

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

/-- A reflection-invariant measure gives the same integral after replacing
`x` by `1 - x`.  This expectation-level statement is independent of support
and probability normalization; the endpoint- and Laplace-moment identities
below are its unit-interval specializations. -/
theorem integral_eq_integral_one_sub_of_reflection
    (μ : Measure ℝ) (hreflect : μ.map (fun x : ℝ => 1 - x) = μ)
    (g : ℝ → ℝ) (hg : Continuous g) :
    (∫ x : ℝ, g x ∂μ) = ∫ x : ℝ, g (1 - x) ∂μ := by
  let r : ℝ → ℝ := fun x => 1 - x
  have hr : Measurable r := by
    dsimp [r]
    fun_prop
  calc
    (∫ x : ℝ, g x ∂μ) = ∫ x : ℝ, g x ∂μ.map r := by rw [hreflect]
    _ = ∫ x : ℝ, g (1 - x) ∂μ := by
      simpa only [r] using
        integral_map hr.aemeasurable hg.aestronglyMeasurable

/-- Reflection invariance passes to the restriction of a measure to `[0,1]`,
because `x ↦ 1 - x` preserves that interval.  Thus every continuous
unit-interval observable has the same integral after reflection, without any
support, finiteness, or probability-normalization hypothesis on the ambient
measure. -/
theorem integral_unit_eq_integral_one_sub_of_reflection
    (μ : Measure ℝ) (hreflect : μ.map (fun x : ℝ => 1 - x) = μ)
    (g : ℝ → ℝ) (hg : Continuous g) :
    (∫ x in Icc (0 : ℝ) 1, g x ∂μ) =
      ∫ x in Icc (0 : ℝ) 1, g (1 - x) ∂μ := by
  let ν : Measure ℝ := μ.restrict (Icc (0 : ℝ) 1)
  have hpreimage :
      (fun x : ℝ => 1 - x) ⁻¹' Icc (0 : ℝ) 1 =
        Icc (0 : ℝ) 1 := by
    ext x
    simp only [mem_preimage, mem_Icc]
    constructor <;> rintro ⟨h0, h1⟩ <;> constructor <;> linarith
  have hνreflect : ν.map (fun x : ℝ => 1 - x) = ν := by
    dsimp only [ν]
    calc
      (μ.restrict (Icc (0 : ℝ) 1)).map (fun x : ℝ => 1 - x) =
          (μ.restrict
            ((fun x : ℝ => 1 - x) ⁻¹' Icc (0 : ℝ) 1)).map
              (fun x : ℝ => 1 - x) := by
            rw [hpreimage]
      _ = (μ.map (fun x : ℝ => 1 - x)).restrict
            (Icc (0 : ℝ) 1) :=
        (Measure.restrict_map
          (μ := μ) (f := fun x : ℝ => 1 - x)
          (by fun_prop) measurableSet_Icc).symm
      _ = μ.restrict (Icc (0 : ℝ) 1) := by
        rw [hreflect]
  change (∫ x : ℝ, g x ∂ν) = ∫ x : ℝ, g (1 - x) ∂ν
  exact integral_eq_integral_one_sub_of_reflection ν hνreflect g hg

/-- For a reflection-invariant measure finite on compact sets, reflection of
`X` to `1 - X` carries the complete tilted raw-moment hierarchy by the signed
binomial transform

`Mₖ(s) = exp(-s) * ∑ j ≤ k, (-1)^j * choose k j * Mⱼ(-s)`.

Only the restriction to `[0,1]` enters the moments, so no global support
hypothesis is needed. -/
theorem unitLaplaceMoment_reflection
    (μ : Measure ℝ) [IsFiniteMeasureOnCompacts μ]
    (hreflect : μ.map (fun x : ℝ => 1 - x) = μ)
    (k : ℕ) (s : ℝ) :
    unitLaplaceMoment μ s k =
      Real.exp (-s) *
        ∑ j ∈ Finset.range (k + 1),
          (-1 : ℝ) ^ j * (k.choose j : ℝ) *
            unitLaplaceMoment μ (-s) j := by
  have hmoment (j : ℕ) :
      Integrable
        (fun x : ℝ => Real.exp (-(-s) * x) * x ^ j)
        (μ.restrict (Icc (0 : ℝ) 1)) := by
    exact
      (by
        fun_prop :
        Continuous (fun x : ℝ => Real.exp (-(-s) * x) * x ^ j)).integrableOn_Icc
  have hpow (x : ℝ) :
      (1 - x) ^ k =
        ∑ j ∈ Finset.range (k + 1),
          (-1 : ℝ) ^ j * (k.choose j : ℝ) * x ^ j := by
    rw [show 1 - x = -x + 1 by ring, add_pow]
    apply Finset.sum_congr rfl
    intro j _hj
    have hneg : (-x) ^ j = (-1 : ℝ) ^ j * x ^ j := neg_pow x j
    rw [hneg, one_pow, mul_one]
    ring
  unfold unitLaplaceMoment
  calc
    (∫ x in Icc (0 : ℝ) 1,
        Real.exp (-s * x) * x ^ k ∂μ) =
        ∫ x in Icc (0 : ℝ) 1,
          Real.exp (-s * (1 - x)) * (1 - x) ^ k ∂μ :=
      integral_unit_eq_integral_one_sub_of_reflection
        μ hreflect
        (fun x : ℝ => Real.exp (-s * x) * x ^ k)
        (by fun_prop)
    _ = Real.exp (-s) *
        ∫ x in Icc (0 : ℝ) 1,
          Real.exp (-(-s) * x) * (1 - x) ^ k ∂μ := by
      rw [← MeasureTheory.integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      rw [show -s * (1 - x) = -s + -(-s) * x by ring,
        Real.exp_add]
      ring
    _ = Real.exp (-s) *
        ∫ x in Icc (0 : ℝ) 1,
          ∑ j ∈ Finset.range (k + 1),
            (-1 : ℝ) ^ j * (k.choose j : ℝ) *
              (Real.exp (-(-s) * x) * x ^ j) ∂μ := by
      congr 1
      apply integral_congr_ae
      filter_upwards with x
      rw [hpow x, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ = Real.exp (-s) *
        ∑ j ∈ Finset.range (k + 1),
          (-1 : ℝ) ^ j * (k.choose j : ℝ) *
            (∫ x in Icc (0 : ℝ) 1,
              Real.exp (-(-s) * x) * x ^ j ∂μ) := by
      congr 1
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro j _hj
        rw [MeasureTheory.integral_const_mul]
      · intro j _hj
        exact (hmoment j).const_mul _

/-- A measure supported on `[0,1]` and invariant under reflection about
`1/2` has equal endpoint and ordinary moments. -/
theorem unitEndpointMoment_eq_unitLaplaceMoment_zero_of_reflection
    (μ : Measure ℝ) (hμ : ∀ᵐ x ∂μ, x ∈ Icc (0 : ℝ) 1)
    (hreflect : μ.map (fun x : ℝ => 1 - x) = μ) (n : ℕ) :
    unitEndpointMoment μ n = unitLaplaceMoment μ 0 n := by
  have hreflect' :
      (∫ x : ℝ, (1 - x) ^ n ∂μ) = ∫ x : ℝ, x ^ n ∂μ := by
    exact (integral_eq_integral_one_sub_of_reflection μ hreflect
      (fun x : ℝ => x ^ n) (continuous_id.pow n)).symm
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

/-- The zeroth unit-interval Laplace transform of a reflection-invariant law
satisfies `L(s) = exp(-s) * L(-s)`.  Equivalently, multiplying by
`exp(s / 2)` centers the transform and makes it even. -/
theorem unitLaplaceMoment_zero_reflection
    (μ : Measure ℝ) (hμ : ∀ᵐ x ∂μ, x ∈ Icc (0 : ℝ) 1)
    (hreflect : μ.map (fun x : ℝ => 1 - x) = μ) (s : ℝ) :
    unitLaplaceMoment μ s 0 =
      Real.exp (-s) * unitLaplaceMoment μ (-s) 0 := by
  have hrestrict : μ.restrict (Icc (0 : ℝ) 1) = μ :=
    Measure.restrict_eq_self_of_ae_mem hμ
  have hreflect' := integral_eq_integral_one_sub_of_reflection μ hreflect
    (fun x : ℝ => Real.exp (-s * x)) (by fun_prop)
  unfold unitLaplaceMoment
  rw [hrestrict]
  simp only [pow_zero, mul_one]
  calc
    (∫ x : ℝ, Real.exp (-s * x) ∂μ) =
        ∫ x : ℝ, Real.exp (-s * (1 - x)) ∂μ := hreflect'
    _ = Real.exp (-s) * ∫ x : ℝ, Real.exp (-(-s) * x) ∂μ := by
      rw [← MeasureTheory.integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      rw [← Real.exp_add]
      congr 1
      ring

/-- Centered form of `unitLaplaceMoment_zero_reflection`: the function
`s ↦ exp(s / 2) * L(s)` is even for every reflection-invariant law
supported on the unit interval. -/
theorem unitLaplaceMoment_zero_centered_even
    (μ : Measure ℝ) (hμ : ∀ᵐ x ∂μ, x ∈ Icc (0 : ℝ) 1)
    (hreflect : μ.map (fun x : ℝ => 1 - x) = μ) (s : ℝ) :
    Real.exp (s / 2) * unitLaplaceMoment μ s 0 =
      Real.exp (-s / 2) * unitLaplaceMoment μ (-s) 0 := by
  rw [unitLaplaceMoment_zero_reflection μ hμ hreflect s]
  calc
    Real.exp (s / 2) *
          (Real.exp (-s) * unitLaplaceMoment μ (-s) 0) =
        (Real.exp (s / 2) * Real.exp (-s)) *
          unitLaplaceMoment μ (-s) 0 := by ring
    _ = Real.exp (-s / 2) * unitLaplaceMoment μ (-s) 0 := by
      congr 1
      rw [← Real.exp_add]
      congr 1
      ring

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
  rw [weightedSumDistribution_eq_geometricUniformDistribution_one_half]
  unfold geometricUniformDistribution
  have hq : |(1 / 2 : ℝ)| < 1 := by norm_num
  simpa only [(hasSum_geometricUniformWeight hq).tsum_eq] using
    (ae_weightedUniformDistribution_mem_Icc
      (summable_norm_geometricUniformWeight hq)
      (geometricUniformWeight_nonneg (by norm_num) (by norm_num)))

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

/-- **Partial Rvachev survival layer cake.**  For `c ∈ [0,1]` and every
Banach-valued interval-integrable kernel `k`,

`∫₀ᶜ rvachevUp(t) • k(t) dt
  = E[∫₀^{min(X,c)} k(t) dt]`,

where `X` has the weighted-sum distribution.  The kernel need not be
nonnegative. -/
theorem intervalIntegral_rvachevUp_smul_eq_integral_min
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : BoundedFabius) (hF : IsFabius F)
    {c : ℝ} (hc : c ∈ Icc (0 : ℝ) 1)
    (k : ℝ → E) (hk : IntervalIntegrable k volume 0 c) :
    (∫ t in (0 : ℝ)..c, rvachevUp F t • k t) =
      ∫ z : ℝ, (∫ t in (0 : ℝ)..min z c, k t)
        ∂weightedSumDistribution := by
  calc
    (∫ t in (0 : ℝ)..c, rvachevUp F t • k t) =
        ∫ t in (0 : ℝ)..c,
          weightedSumDistribution.real (Ioi t) • k t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hc.1] at ht
      exact congrArg (fun a : ℝ => a • k t)
        (weightedSumDistribution_real_Ioi_eq_rvachevUp F hF
          ⟨ht.1, ht.2.trans hc.2⟩).symm
    _ = ∫ z : ℝ, (∫ t in (0 : ℝ)..min z c, k t)
          ∂weightedSumDistribution :=
      intervalIntegral_survival_smul_eq_integral_min_of_ae_mem_Icc
        weightedSumDistribution hc ae_weightedSumDistribution_mem_Icc k hk

/-- **Full Rvachev survival layer cake.**  Every Banach-valued
interval-integrable kernel `k` satisfies

`∫₀¹ rvachevUp(t) • k(t) dt = E[∫₀ˣ k(t) dt]`

for the weighted-sum random variable `X`.  Taking `E = ℂ` gives the complex
kernel identity used by transform arguments. -/
theorem intervalIntegral_rvachevUp_smul_eq_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : BoundedFabius) (hF : IsFabius F)
    (k : ℝ → E) (hk : IntervalIntegrable k volume 0 1) :
    (∫ t in (0 : ℝ)..1, rvachevUp F t • k t) =
      ∫ z : ℝ, (∫ t in (0 : ℝ)..z, k t) ∂weightedSumDistribution := by
  calc
    (∫ t in (0 : ℝ)..1, rvachevUp F t • k t) =
        ∫ t in (0 : ℝ)..1,
          weightedSumDistribution.real (Ioi t) • k t := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      exact congrArg (fun a : ℝ => a • k t)
        (weightedSumDistribution_real_Ioi_eq_rvachevUp F hF ht).symm
    _ = ∫ z : ℝ, (∫ t in (0 : ℝ)..z, k t)
          ∂weightedSumDistribution :=
      intervalIntegral_survival_smul_eq_integral_of_ae_mem_Icc
        weightedSumDistribution (by norm_num)
          ae_weightedSumDistribution_mem_Icc k hk

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

/-- Reflection symmetry of the Fabius probability law carries every tilted
raw moment by the signed binomial transform

`Mₖ(s) = exp(-s) * ∑ j ≤ k, (-1)^j * choose k j * Mⱼ(-s)`. -/
theorem fabiusLaplaceMoment_reflection
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ) (s : ℝ) :
    fabiusLaplaceMoment F k s =
      Real.exp (-s) *
        ∑ j ∈ Finset.range (k + 1),
          (-1 : ℝ) ^ j * (k.choose j : ℝ) *
            fabiusLaplaceMoment F j (-s) := by
  simpa only [
    ProbabilityRepresentation.unitLaplaceMoment_weightedSumDistribution_eq_fabiusLaplaceMoment
      F hF] using
    unitLaplaceMoment_reflection
      ProbabilityRepresentation.weightedSumDistribution
      ProbabilityRepresentation.weightedSumDistribution_reflection k s

/-- Reflection symmetry of the Fabius law gives the exact functional equation
`M₀(s) = exp(-s) M₀(-s)` for its bilateral zeroth Laplace moment. -/
theorem fabiusLaplaceMoment_zero_reflection
    (F : BoundedFabius) (hF : IsFabius F) (s : ℝ) :
    fabiusLaplaceMoment F 0 s =
      Real.exp (-s) * fabiusLaplaceMoment F 0 (-s) := by
  simpa using fabiusLaplaceMoment_reflection F hF 0 s

/-- After centering at the mean `1/2`, the zeroth Fabius Laplace moment is an
even function of the tilt. -/
theorem fabiusLaplaceMoment_zero_centered_even
    (F : BoundedFabius) (hF : IsFabius F) (s : ℝ) :
    Real.exp (s / 2) * fabiusLaplaceMoment F 0 s =
      Real.exp (-s / 2) * fabiusLaplaceMoment F 0 (-s) := by
  simpa only [
    ProbabilityRepresentation.unitLaplaceMoment_weightedSumDistribution_eq_fabiusLaplaceMoment
      F hF] using
    unitLaplaceMoment_zero_centered_even
      ProbabilityRepresentation.weightedSumDistribution
      ProbabilityRepresentation.ae_weightedSumDistribution_mem_Icc
      ProbabilityRepresentation.weightedSumDistribution_reflection s

/-- After normalization by the zeroth tilted moment, reflection reverses the
tilt and applies the signed binomial transform

`Rₖ(s) = ∑ j ≤ k, (-1)^j * choose k j * Rⱼ(-s)`.

The exponential factor in the raw reflection law disappears because the
normalizing zeroth moment carries exactly the same factor. -/
theorem normalizedLaplaceMoment_reflection
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ) (s : ℝ) :
    normalizedLaplaceMoment F k s =
      ∑ j ∈ Finset.range (k + 1),
        (-1 : ℝ) ^ j * (k.choose j : ℝ) *
          normalizedLaplaceMoment F j (-s) := by
  unfold normalizedLaplaceMoment
  rw [fabiusLaplaceMoment_reflection F hF k s,
    fabiusLaplaceMoment_zero_reflection F hF s,
    mul_div_mul_left _ _ (Real.exp_ne_zero (-s)),
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [mul_div_assoc]

/-- The normalized means under opposite exponential tilts are complementary:
`R₁(s) + R₁(-s) = 1`. -/
theorem normalizedLaplaceMoment_one_complement
    (F : BoundedFabius) (hF : IsFabius F) (s : ℝ) :
    normalizedLaplaceMoment F 1 s +
        normalizedLaplaceMoment F 1 (-s) =
      1 := by
  have hreflect := normalizedLaplaceMoment_reflection F hF 1 s
  norm_num [Finset.sum_range_succ,
    normalizedLaplaceMoment_zero_all F hF] at hreflect
  linarith

/-- Centering the normalized first tilted moment at the reflection center
`1 / 2` produces an odd function of the tilt. -/
theorem normalizedLaplaceMoment_one_sub_half_odd
    (F : BoundedFabius) (hF : IsFabius F) :
    Function.Odd
      (fun s : ℝ => normalizedLaplaceMoment F 1 s - (1 / 2 : ℝ)) := by
  intro s
  dsimp
  linarith [normalizedLaplaceMoment_one_complement F hF s]

/-- The second normalized logarithmic cumulant—the variance of the
exponentially tilted law—is even under reversal of the tilt. -/
theorem negativeLaplaceLogSecond_even
    (F : BoundedFabius) (hF : IsFabius F) :
    Function.Even (negativeLaplaceLogSecond F) := by
  intro s
  have hone :
      normalizedLaplaceMoment F 1 s =
        1 - normalizedLaplaceMoment F 1 (-s) := by
    linarith [normalizedLaplaceMoment_one_complement F hF s]
  have htwo := normalizedLaplaceMoment_reflection F hF 2 s
  norm_num [Finset.sum_range_succ,
    normalizedLaplaceMoment_zero_all F hF] at htwo
  unfold negativeLaplaceLogSecond
  rw [hone, htwo]
  ring

/-- Every real tilted Fabius moment is nonnegative. -/
lemma fabiusLaplaceMoment_nonneg
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ) (s : ℝ) :
    0 ≤ fabiusLaplaceMoment F k s := by
  rw [← ProbabilityRepresentation.unitLaplaceMoment_weightedSumDistribution_eq_fabiusLaplaceMoment
    F hF k s]
  exact unitLaplaceMoment_nonneg _ _ _

end Fabius
