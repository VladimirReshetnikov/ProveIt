import FabiusFunction.GeometricUniformDictionary
import FabiusFunction.RandomSeriesLaw

/-!
# The finite sinc factorization at every ratio

The closed characteristic function of the scaled digit and the finite
master factorization of the normalized geometric-uniform law: for
every ratio `|q| < 1` and every depth `m`,

`φ_q(t) = e^{i(1-qᵐ)t/2} · ∏_{k<m} sinc((1-q)qᵏt/2) · φ_q(qᵐ t)`,

the finite half of the corpus's sinc-product factorizations — at
`q = 1/2` the dyadic `F̂ₙ = Φ·A(2⁻ⁿt)` master factorization of the
repeated-integration approximants, at `q = 1/a` the atomic-function
family `ĥ_a`.  The phase collapses along the geometric sum
`(1-q)∑_{k<m}qᵏ = 1-qᵐ`; the modulus factor is the finite sinc
product itself.
-/

set_option autoImplicit false

open MeasureTheory Complex Real Set

namespace Fabius

open ProbabilityRepresentation

private lemma map_subtype_val_volume_Icc :
    (volume : Measure (Set.Icc (0 : ℝ) 1)).map
      (fun u : Set.Icc (0 : ℝ) 1 => (u : ℝ)) =
      (volume : Measure ℝ).restrict (Icc (0 : ℝ) 1) := by
  rw [show (volume : Measure (Set.Icc (0 : ℝ) 1)) =
      (volume : Measure ℝ).comap Subtype.val from rfl]
  exact map_comap_subtype_coe measurableSet_Icc _

/-- **The closed digit characteristic function**: the scaled uniform
digit `(1-q)·U` has `φ(t) = e^{i(1-q)t/2}·sinc((1-q)t/2)`. -/
theorem charFun_geometricUniformDigit (q t : ℝ) :
    charFun (geometricUniformDigit q) t =
      cexp (((2⁻¹ * ((1 - q) * t) : ℝ) : ℂ) * I) *
        complexSinc ((2⁻¹ * ((1 - q) * t) : ℝ) : ℂ) := by
  rw [geometricUniformDigit,
    charFun_map_mul_comp measurable_subtype_coe.aemeasurable
      (1 - q) t,
    map_subtype_val_volume_Icc, charFun_volume_restrict_unit]

/-- **The finite factorization with closed factors**: the dictionary's
characteristic-product face with every digit factor evaluated. -/
theorem charFun_geometricUniformDistribution_prefix {q : ℝ}
    (hq : |q| < 1) (m : ℕ) (t : ℝ) :
    charFun (geometricUniformDistribution q) t =
      (∏ k ∈ Finset.range m,
        (cexp (((2⁻¹ * ((1 - q) * (q ^ k * t)) : ℝ) : ℂ) * I) *
          complexSinc
            ((2⁻¹ * ((1 - q) * (q ^ k * t)) : ℝ) : ℂ))) *
        charFun (geometricUniformDistribution q) (q ^ m * t) := by
  have h := ((geometric_tail_dictionary_geometricUniform hq m).2.1) t
  rw [h]
  congr 1
  exact Finset.prod_congr rfl fun k _ =>
    charFun_geometricUniformDigit q (q ^ k * t)

/-- **The finite sinc factorization at every ratio**: the phase
collapses along the geometric sum, leaving the finite sinc product —
`φ_q(t) = e^{i(1-qᵐ)t/2}·∏_{k<m} sinc((1-q)qᵏt/2)·φ_q(qᵐt)`. -/
theorem charFun_geometricUniformDistribution_prefix_sinc {q : ℝ}
    (hq : |q| < 1) (m : ℕ) (t : ℝ) :
    charFun (geometricUniformDistribution q) t =
      cexp (((2⁻¹ * ((1 - q ^ m) * t) : ℝ) : ℂ) * I) *
        (∏ k ∈ Finset.range m,
          complexSinc ((2⁻¹ * ((1 - q) * (q ^ k * t)) : ℝ) : ℂ)) *
        charFun (geometricUniformDistribution q) (q ^ m * t) := by
  have hgeo : (∑ k ∈ Finset.range m,
      2⁻¹ * ((1 - q) * (q ^ k * t))) =
      2⁻¹ * ((1 - q ^ m) * t) := by
    have h := geom_sum_mul q m
    have hsum : (∑ k ∈ Finset.range m, q ^ k) * (1 - q) =
        1 - q ^ m := by
      linear_combination -h
    calc ∑ k ∈ Finset.range m, 2⁻¹ * ((1 - q) * (q ^ k * t))
        = (∑ k ∈ Finset.range m, q ^ k) * ((1 - q) * (2⁻¹ * t)) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun k _ => by ring
      _ = 2⁻¹ * ((1 - q ^ m) * t) := by
          rw [show (∑ k ∈ Finset.range m, q ^ k) *
              ((1 - q) * (2⁻¹ * t)) =
              ((∑ k ∈ Finset.range m, q ^ k) * (1 - q)) *
                (2⁻¹ * t) from by ring, hsum]
          ring
  have hphase : (∏ k ∈ Finset.range m,
      cexp (((2⁻¹ * ((1 - q) * (q ^ k * t)) : ℝ) : ℂ) * I)) =
      cexp (((2⁻¹ * ((1 - q ^ m) * t) : ℝ) : ℂ) * I) := by
    calc ∏ k ∈ Finset.range m,
        cexp (((2⁻¹ * ((1 - q) * (q ^ k * t)) : ℝ) : ℂ) * I)
        = cexp (∑ k ∈ Finset.range m,
            ((2⁻¹ * ((1 - q) * (q ^ k * t)) : ℝ) : ℂ) * I) :=
          (Complex.exp_sum _ _).symm
      _ = cexp (((2⁻¹ * ((1 - q ^ m) * t) : ℝ) : ℂ) * I) := by
          congr 1
          rw [← Finset.sum_mul]
          congr 1
          rw [← hgeo]
          push_cast
          rfl
  rw [charFun_geometricUniformDistribution_prefix hq m t,
    Finset.prod_mul_distrib, hphase]

/-- **The infinite master factorization at every ratio**: the finite
phase-collapsed sinc products converge to the characteristic
function, `e^{i(1-qᵐ)t/2}·∏_{k<m} sinc((1-q)qᵏt/2) → φ_q(t)` —
the full sinc-product formula as the limit of its finite halves. -/
theorem tendsto_prefix_sinc_charFun {q : ℝ} (hq : |q| < 1) (t : ℝ) :
    Filter.Tendsto (fun m : ℕ =>
      cexp (((2⁻¹ * ((1 - q ^ m) * t) : ℝ) : ℂ) * I) *
        ∏ k ∈ Finset.range m,
          complexSinc ((2⁻¹ * ((1 - q) * (q ^ k * t)) : ℝ) : ℂ))
      Filter.atTop
      (nhds (charFun (geometricUniformDistribution q) t)) := by
  haveI := geometricUniformDistribution_isProbabilityMeasure hq
  have htail : Filter.Tendsto
      (fun m : ℕ =>
        charFun (geometricUniformDistribution q) (q ^ m * t))
      Filter.atTop (nhds 1) := by
    have hq0 : Filter.Tendsto (fun m : ℕ => q ^ m * t)
        Filter.atTop (nhds 0) := by
      have h := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hq
      simpa using h.mul_const t
    have h := ((continuous_charFun
      (μ := geometricUniformDistribution q)).tendsto 0).comp hq0
    simpa [charFun_zero, Function.comp_def] using h
  have hfin : ∀ m : ℕ,
      (cexp (((2⁻¹ * ((1 - q ^ m) * t) : ℝ) : ℂ) * I) *
        ∏ k ∈ Finset.range m,
          complexSinc ((2⁻¹ * ((1 - q) * (q ^ k * t)) : ℝ) : ℂ)) *
        charFun (geometricUniformDistribution q) (q ^ m * t) =
        charFun (geometricUniformDistribution q) t := fun m =>
    (charFun_geometricUniformDistribution_prefix_sinc hq m t).symm
  have hne : ∀ᶠ m : ℕ in Filter.atTop,
      charFun (geometricUniformDistribution q) (q ^ m * t) ≠ 0 :=
    htail.eventually_ne one_ne_zero
  have hlim : Filter.Tendsto (fun m : ℕ =>
      charFun (geometricUniformDistribution q) t *
        (charFun (geometricUniformDistribution q) (q ^ m * t))⁻¹)
      Filter.atTop
      (nhds (charFun (geometricUniformDistribution q) t)) := by
    have h := (htail.inv₀ one_ne_zero).const_mul
      (charFun (geometricUniformDistribution q) t)
    simpa using h
  refine Filter.Tendsto.congr' ?_ hlim
  filter_upwards [hne] with m hm
  rw [← hfin m, mul_assoc, mul_inv_cancel₀ hm, mul_one]

/-! ## The dyadic instance -/

private lemma abs_one_half_lt_one : |(1 / 2 : ℝ)| < 1 := by
  rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  norm_num

/-- **The dyadic master factorization**: the Fabius random-series law
is the corpus's `q = 1/2` instance, so at every depth `m`

`E[e^{itX}] = e^{i(1-2⁻ᵐ)t/2}·∏_{k<m} sinc(t/2^{k+2})·E[e^{i2⁻ᵐtX}]`

— the finite half of `F̂ₙ = Φ·A(2⁻ⁿt)`, with the phase collapsed
along the dyadic geometric sum. -/
theorem charFun_weightedSumDistribution_prefix_sinc (m : ℕ) (t : ℝ) :
    charFun weightedSumDistribution t =
      cexp (((2⁻¹ * ((1 - (1 / 2 : ℝ) ^ m) * t) : ℝ) : ℂ) * I) *
        (∏ k ∈ Finset.range m,
          complexSinc (((((2 : ℝ) ^ (k + 2))⁻¹ * t : ℝ)) : ℂ)) *
        charFun weightedSumDistribution ((1 / 2 : ℝ) ^ m * t) := by
  rw [weightedSumDistribution_eq_geometricUniformDistribution_one_half,
    charFun_geometricUniformDistribution_prefix_sinc
      abs_one_half_lt_one m t]
  congr 2
  refine Finset.prod_congr rfl fun k _ => ?_
  congr 2
  push_cast [one_div]
  ring

/-- The dyadic finite products converge to the random-series
characteristic function. -/
theorem tendsto_prefix_sinc_charFun_weightedSumDistribution (t : ℝ) :
    Filter.Tendsto (fun m : ℕ =>
      cexp (((2⁻¹ * ((1 - (1 / 2 : ℝ) ^ m) * t) : ℝ) : ℂ) * I) *
        ∏ k ∈ Finset.range m,
          complexSinc (((((2 : ℝ) ^ (k + 2))⁻¹ * t : ℝ)) : ℂ))
      Filter.atTop (nhds (charFun weightedSumDistribution t)) := by
  rw [weightedSumDistribution_eq_geometricUniformDistribution_one_half]
  refine (tendsto_prefix_sinc_charFun abs_one_half_lt_one t).congr
    fun m => ?_
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  congr 2
  push_cast [one_div]
  ring

end Fabius
