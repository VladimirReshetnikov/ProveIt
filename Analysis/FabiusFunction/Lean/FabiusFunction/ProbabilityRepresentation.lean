import FabiusFunction.Existence
import FabiusFunction.GeometricUniformLaw
import Mathlib.Probability.CDF

/-!
# The product-probability representation of Rvachev's function

This file formalizes Theorem 3 (and the equivalent probabilistic proposition)
of Juan Arias de Reyna, *An infinitely differentiable function with compact
support: Definition and properties*, arXiv:1702.05442.

The paper indexes the coordinates by positive integers and writes
`∑ k ≥ 1, x k / 2^k`.  We use Lean's natural-number indexing, so the same
random variable is `∑' n, x n / 2 / 2^n`.

The construction records both pointwise and measure-theoretic support on
`[0,1]`, as well as the self-similarity and reflection identities used to
identify its continuous CDF with the bounded Fabius function.

The theorem stated in the paper is recovered on its source-facing domain
`x ∈ [-1,0]`.  The construction yields stronger identities with no restriction
on the real argument:

* `weightedSumCDF x = fabiusReal F x`, equivalently
  `fabiusReal F x = P[X ≤ x]`;
* `rvachevUp F x = weightedSumCDF (1 - |x|)`, equivalently
  `rvachevUp F x = P[X ≤ 1 - |x|]`.

Both identities have real-valued and native `ℝ≥0∞` measure forms.  In theorem
names below, `_global` means that the input `x` ranges over all of `ℝ`; it
does **not** refer to the signed extension `extendedFabius` or its canonical
specialization `globalFabius`.
-/

open Filter Set MeasureTheory ProbabilityTheory Topology
open scoped BigOperators unitInterval

namespace Fabius
namespace ProbabilityRepresentation

set_option autoImplicit false
noncomputable section

/-- The random series `X₁/2 + X₂/4 + ⋯`, with zero-based Lean indexing. -/
noncomputable def weightedCoordinateSum (ω : SampleSpace) : ℝ :=
  ∑' n : ℕ, (ω n : ℝ) / 2 / (2 : ℝ) ^ n

/-- The dyadic random series is the specialization of the general
uniform-coordinate series to the weights `1 / 2 / 2 ^ n`. -/
theorem weightedCoordinateSum_eq_weightedUniformSeries (ω : SampleSpace) :
    weightedCoordinateSum ω =
      weightedUniformSeries (fun n : ℕ => (1 : ℝ) / 2 / (2 : ℝ) ^ n) ω := by
  unfold weightedCoordinateSum weightedUniformSeries
  apply tsum_congr
  intro n
  simp only [smul_eq_mul]
  ring

/-- At `q = 1 / 2`, the geometric uniform series is exactly the dyadic
random series used in the Fabius probability representation. -/
theorem weightedCoordinateSum_eq_geometricUniformSeries_one_half
    (ω : SampleSpace) :
    weightedCoordinateSum ω = geometricUniformSeries (1 / 2) ω := by
  rw [weightedCoordinateSum_eq_weightedUniformSeries]
  unfold geometricUniformSeries weightedUniformSeries
  apply tsum_congr
  intro n
  simp only [geometricUniformWeight, smul_eq_mul, div_pow, one_pow]
  ring

private abbrev dyadicWeight (n : ℕ) : ℝ :=
  (1 : ℝ) / 2 / (2 : ℝ) ^ n

private lemma dyadicWeight_nonneg (n : ℕ) : 0 ≤ dyadicWeight n := by
  positivity

private lemma summable_norm_dyadicWeight :
    Summable (fun n : ℕ => ‖dyadicWeight n‖) := by
  have hnorm : (fun n : ℕ => ‖dyadicWeight n‖) = dyadicWeight := by
    funext n
    rw [Real.norm_eq_abs, abs_of_nonneg (dyadicWeight_nonneg n)]
  rw [hnorm]
  exact summable_geometric_two' 1

private lemma tsum_dyadicWeight : ∑' n : ℕ, dyadicWeight n = 1 :=
  tsum_geometric_two' 1

private lemma dyadicWeight_shift (n : ℕ) :
    dyadicWeight (Nat.succ n) = (1 / 2 : ℝ) • dyadicWeight n := by
  simp only [dyadicWeight, Nat.succ_eq_add_one, pow_succ, smul_eq_mul]
  field_simp

private lemma weightedCoordinateSum_eq_weightedUniformSeries_fun :
    weightedCoordinateSum = weightedUniformSeries dyadicWeight := by
  funext ω
  exact weightedCoordinateSum_eq_weightedUniformSeries ω

/-- The random series is continuous on the sample space, because it
converges uniformly against the summable geometric majorant
`n ↦ 1 / 2 / 2 ^ n`. -/
lemma continuous_weightedCoordinateSum : Continuous weightedCoordinateSum := by
  rw [weightedCoordinateSum_eq_weightedUniformSeries_fun]
  exact continuous_weightedUniformSeries summable_norm_dyadicWeight

/-- Measurability of the random series, read off from its continuity.
This is the hypothesis that lets `uniformProduct` be pushed forward to
`weightedSumDistribution`. -/
lemma measurable_weightedCoordinateSum : Measurable weightedCoordinateSum :=
  continuous_weightedCoordinateSum.measurable

/-- The random series is nonnegative, since every summand is. -/
lemma weightedCoordinateSum_nonneg (ω : SampleSpace) :
    0 ≤ weightedCoordinateSum ω := by
  rw [weightedCoordinateSum_eq_weightedUniformSeries]
  exact weightedUniformSeries_nonneg dyadicWeight_nonneg ω

/-- The random series is at most `1`, by comparison with
`∑' n, 1 / 2 / 2 ^ n = 1`.  With `weightedCoordinateSum_nonneg` this
gives `weightedCoordinateSum_mem_Icc`. -/
lemma weightedCoordinateSum_le_one (ω : SampleSpace) :
    weightedCoordinateSum ω ≤ 1 := by
  rw [weightedCoordinateSum_eq_weightedUniformSeries]
  simpa only [tsum_dyadicWeight] using
    weightedUniformSeries_le_tsum summable_norm_dyadicWeight
      dyadicWeight_nonneg ω

/-- The random series takes values in the closed unit interval pointwise. -/
lemma weightedCoordinateSum_mem_Icc (ω : SampleSpace) :
    weightedCoordinateSum ω ∈ Icc (0 : ℝ) 1 := by
  rw [weightedCoordinateSum_eq_weightedUniformSeries]
  simpa only [tsum_dyadicWeight] using
    weightedUniformSeries_mem_Icc summable_norm_dyadicWeight
      dyadicWeight_nonneg ω

/-- One step of the recurrence: the random series at `ω` equals
`(ω 0 + X (tail ω)) / 2`.  This pointwise identity is what
`weightedSumDistribution_selfSimilar` transports to the level of laws. -/
lemma weightedCoordinateSum_split (ω : SampleSpace) :
    weightedCoordinateSum ω = ((ω 0 : ℝ) + weightedCoordinateSum (tail ω)) / 2 := by
  rw [weightedCoordinateSum_eq_weightedUniformSeries ω,
    weightedCoordinateSum_eq_weightedUniformSeries (tail ω),
    weightedUniformSeries_geometric_split (c := (1 / 2 : ℝ))
      summable_norm_dyadicWeight dyadicWeight_shift]
  simp only [dyadicWeight, pow_zero, div_one, smul_eq_mul]
  ring

/-- The distribution of the random series. -/
noncomputable def weightedSumDistribution : Measure ℝ :=
  uniformProduct.map weightedCoordinateSum

/-- The dyadic random-series law is the specialization of the general
uniform-coordinate law to the weights `1 / 2 / 2 ^ n`. -/
theorem weightedSumDistribution_eq_weightedUniformDistribution :
    weightedSumDistribution =
      weightedUniformDistribution
        (fun n : ℕ => (1 : ℝ) / 2 / (2 : ℝ) ^ n) := by
  unfold weightedSumDistribution weightedUniformDistribution
  rw [weightedCoordinateSum_eq_weightedUniformSeries_fun]

/-- The classical dyadic law is the half-base member of the geometric
uniform family. -/
theorem weightedSumDistribution_eq_geometricUniformDistribution_one_half :
    weightedSumDistribution = geometricUniformDistribution (1 / 2) := by
  rw [weightedSumDistribution, geometricUniformDistribution,
    weightedUniformDistribution]
  apply Measure.map_congr
  filter_upwards with ω
  exact weightedCoordinateSum_eq_geometricUniformSeries_one_half ω

/-- The classical dyadic weighted-sum law has topological support exactly
the closed unit interval. -/
theorem weightedSumDistribution_support_eq_Icc :
    weightedSumDistribution.support = Icc (0 : ℝ) 1 := by
  rw [weightedSumDistribution_eq_geometricUniformDistribution_one_half]
  exact geometricUniformDistribution_support_eq_Icc (by norm_num) (by norm_num)

/-- The law of the random series is a probability measure, being the
pushforward of one along a measurable map. -/
instance : IsProbabilityMeasure weightedSumDistribution := by
  rw [weightedSumDistribution_eq_weightedUniformDistribution]
  exact isProbabilityMeasure_weightedUniformDistribution
    summable_norm_dyadicWeight

/-- The law of the random series is supported on the closed unit interval. -/
lemma weightedSumDistribution_Icc :
    weightedSumDistribution (Icc (0 : ℝ) 1) = 1 := by
  rw [weightedSumDistribution_eq_weightedUniformDistribution]
  simpa only [tsum_dyadicWeight] using
    weightedUniformDistribution_Icc summable_norm_dyadicWeight
      dyadicWeight_nonneg

/-- The weighted-sum law assigns no mass outside its natural support. -/
@[simp]
lemma weightedSumDistribution_compl_Icc :
    weightedSumDistribution ((Icc (0 : ℝ) 1)ᶜ) = 0 := by
  rw [weightedSumDistribution_eq_weightedUniformDistribution]
  simpa only [tsum_dyadicWeight] using
    weightedUniformDistribution_compl_Icc summable_norm_dyadicWeight
      dyadicWeight_nonneg

/-- The weighted-sum law is almost surely carried by the unit interval. -/
lemma ae_weightedSumDistribution_mem_Icc :
    ∀ᵐ x ∂weightedSumDistribution, x ∈ Icc (0 : ℝ) 1 := by
  change Icc (0 : ℝ) 1 ∈ ae weightedSumDistribution
  rw [mem_ae_iff]
  exact weightedSumDistribution_compl_Icc

/-- Restricting the weighted-sum law to the unit interval leaves it
unchanged. -/
lemma weightedSumDistribution_restrict_Icc :
    weightedSumDistribution.restrict (Icc (0 : ℝ) 1) =
      weightedSumDistribution :=
  Measure.restrict_eq_self_of_ae_mem ae_weightedSumDistribution_mem_Icc

/-- The pair (first coordinate, series of the remaining coordinates) has
law `volume` times `weightedSumDistribution`: the head is uniform on
`[0,1]` and independent of the tail series. -/
lemma uniformProduct_map_head_tailSum :
    uniformProduct.map
        (fun ω : SampleSpace => (ω 0, weightedCoordinateSum (tail ω))) =
      (volume : Measure (Set.Icc (0 : ℝ) 1)).prod weightedSumDistribution := by
  simpa only [← weightedCoordinateSum_eq_weightedUniformSeries,
    ← weightedSumDistribution_eq_weightedUniformDistribution] using
      (uniformProduct_map_head_tailWeightedUniformSeries
        (v := dyadicWeight) summable_norm_dyadicWeight)

/-- Self-similarity of the law: `weightedSumDistribution` is the image of
`volume` times `weightedSumDistribution` under `p ↦ (p.1 + p.2) / 2`.
This is the measure-level form of `weightedCoordinateSum_split` and the
input to the smoothing equation `weightedSumCDF_eq_integral`. -/
lemma weightedSumDistribution_selfSimilar :
    weightedSumDistribution =
      ((volume : Measure (Set.Icc (0 : ℝ) 1)).prod weightedSumDistribution).map
        (fun p => ((p.1 : ℝ) + p.2) / 2) := by
  simp only [weightedSumDistribution_eq_weightedUniformDistribution]
  calc
    weightedUniformDistribution dyadicWeight =
        ((volume : Measure (Set.Icc (0 : ℝ) 1)).prod
          (weightedUniformDistribution dyadicWeight)).map
            (fun p => (p.1 : ℝ) • dyadicWeight 0 + (1 / 2 : ℝ) • p.2) :=
      weightedUniformDistribution_geometric_split
        (c := (1 / 2 : ℝ)) summable_norm_dyadicWeight dyadicWeight_shift
    _ = ((volume : Measure (Set.Icc (0 : ℝ) 1)).prod
          (weightedUniformDistribution dyadicWeight)).map
            (fun p => ((p.1 : ℝ) + p.2) / 2) := by
      apply Measure.map_congr
      filter_upwards with p
      simp only [dyadicWeight, pow_zero, div_one, smul_eq_mul]
      ring

/-- Reflecting every coordinate sends the random series `X` to `1 - X`;
the constant comes from `∑' n, 1 / 2 / 2 ^ n = 1`. -/
lemma weightedCoordinateSum_reflect (ω : SampleSpace) :
    weightedCoordinateSum (reflectCoordinates ω) = 1 - weightedCoordinateSum ω := by
  rw [weightedCoordinateSum_eq_weightedUniformSeries (reflectCoordinates ω),
    weightedCoordinateSum_eq_weightedUniformSeries ω]
  simpa only [tsum_dyadicWeight] using
    weightedUniformSeries_reflect summable_norm_dyadicWeight ω

/-- The law of the random series is invariant under `x ↦ 1 - x`, i.e. it
is symmetric about `1/2`.  It gives `weightedSumCDF_symmetry` here, and
is reused in `ProbabilityLaplaceMoments` to relate the endpoint moments
of the law at `0` and at `1`. -/
lemma weightedSumDistribution_reflection :
    weightedSumDistribution.map (fun x : ℝ => 1 - x) = weightedSumDistribution := by
  simp only [weightedSumDistribution_eq_weightedUniformDistribution]
  simpa only [tsum_dyadicWeight] using
    weightedUniformDistribution_reflection
      (w := dyadicWeight) summable_norm_dyadicWeight


/-- Its cumulative distribution function. -/
noncomputable def weightedSumCDF (x : ℝ) : ℝ :=
  ProbabilityTheory.cdf weightedSumDistribution x

/-- The CDF as an explicit real-valued probability on the sample space:
`weightedSumCDF x = P[X ≤ x]`.  This is the bridge between Mathlib's
`cdf` API and the event `{ω | weightedCoordinateSum ω ≤ x}` appearing in
the representation theorems at the end of the file. -/
lemma weightedSumCDF_eq_measureReal (x : ℝ) :
    weightedSumCDF x = uniformProduct.real {ω | weightedCoordinateSum ω ≤ x} := by
  rw [weightedSumCDF, ProbabilityTheory.cdf_eq_real, weightedSumDistribution,
    map_measureReal_apply measurable_weightedCoordinateSum measurableSet_Iic]
  rfl

/-- The CDF is measurable, being monotone. -/
lemma measurable_weightedSumCDF : Measurable weightedSumCDF := by
  exact (ProbabilityTheory.monotone_cdf weightedSumDistribution).measurable

/-- The CDF is nonnegative.  Half of the range bound required by
`cdfContinuousMap_admissible`. -/
lemma weightedSumCDF_nonneg (x : ℝ) : 0 ≤ weightedSumCDF x :=
  ProbabilityTheory.cdf_nonneg weightedSumDistribution x

/-- The CDF is at most `1`.  The other half of the range bound required
by `cdfContinuousMap_admissible`. -/
lemma weightedSumCDF_le_one (x : ℝ) : weightedSumCDF x ≤ 1 :=
  ProbabilityTheory.cdf_le_one weightedSumDistribution x

/-- Conditioning on the first uniform coordinate gives the smoothing equation
`H(y) = ∫₀¹ H(2y-u) du` for the CDF `H` of the random series. -/
lemma weightedSumCDF_eq_integral (y : ℝ) :
    weightedSumCDF y =
      ∫ u : Set.Icc (0 : ℝ) 1, weightedSumCDF (2 * y - (u : ℝ)) := by
  let A : Set (Set.Icc (0 : ℝ) 1 × ℝ) :=
    {p | ((p.1 : ℝ) + p.2) / 2 ≤ y}
  have hA : MeasurableSet A := by
    apply measurableSet_le
    · fun_prop
    · fun_prop
  have hcombine : Measurable
      (fun p : Set.Icc (0 : ℝ) 1 × ℝ => ((p.1 : ℝ) + p.2) / 2) := by
    fun_prop
  rw [weightedSumCDF, ProbabilityTheory.cdf_eq_real,
    weightedSumDistribution_selfSimilar,
    map_measureReal_apply hcombine measurableSet_Iic]
  change ((volume : Measure (Set.Icc (0 : ℝ) 1)).prod weightedSumDistribution).real A = _
  calc
    ((volume : Measure (Set.Icc (0 : ℝ) 1)).prod weightedSumDistribution).real A =
        ∫ p, A.indicator (fun _ => (1 : ℝ)) p
          ∂((volume : Measure (Set.Icc (0 : ℝ) 1)).prod weightedSumDistribution) := by
      symm
      exact integral_indicator_one hA
    _ = ∫ u : Set.Icc (0 : ℝ) 1,
        ∫ v : ℝ, A.indicator (fun _ => (1 : ℝ)) (u, v) ∂weightedSumDistribution := by
      apply integral_prod
      exact (integrable_const (1 : ℝ)).indicator hA
    _ = ∫ u : Set.Icc (0 : ℝ) 1, weightedSumCDF (2 * y - (u : ℝ)) := by
      apply integral_congr_ae
      filter_upwards with u
      let Au : Set ℝ := {v | (((u : ℝ) + v) / 2 : ℝ) ≤ y}
      have hAu : MeasurableSet Au := by
        apply measurableSet_le <;> fun_prop
      calc
        (∫ v : ℝ, A.indicator (fun _ => (1 : ℝ)) (u, v)
            ∂weightedSumDistribution) =
            ∫ v : ℝ, Au.indicator (fun _ => (1 : ℝ)) v
              ∂weightedSumDistribution := by
          apply integral_congr_ae
          filter_upwards with v
          rfl
        _ = weightedSumDistribution.real Au := integral_indicator_one hAu
        _ = weightedSumCDF (2 * y - (u : ℝ)) := by
          rw [weightedSumCDF, ProbabilityTheory.cdf_eq_real]
          congr 2
          ext v
          simp only [Au, mem_setOf_eq, mem_Iic]
          constructor <;> intro hv <;> linarith

/-- The same smoothing equation written as an ordinary interval integral. -/
lemma weightedSumCDF_eq_intervalIntegral (y : ℝ) :
    weightedSumCDF y =
      ∫ t in (2 * y - 1)..(2 * y), weightedSumCDF t := by
  rw [weightedSumCDF_eq_integral]
  calc
    (∫ u : Set.Icc (0 : ℝ) 1, weightedSumCDF (2 * y - (u : ℝ))) =
        ∫ u in Set.Icc (0 : ℝ) 1, weightedSumCDF (2 * y - u) := by
      simpa using (integral_subtype (G := ℝ) measurableSet_Icc
        (fun u : ℝ => weightedSumCDF (2 * y - u)))
    _ = ∫ u in (0 : ℝ)..1, weightedSumCDF (2 * y - u) := by
      rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by norm_num)]
    _ = ∫ t in (2 * y - 1)..(2 * y - 0), weightedSumCDF t :=
      intervalIntegral.integral_comp_sub_left weightedSumCDF (2 * y)
    _ = ∫ t in (2 * y - 1)..(2 * y), weightedSumCDF t := by ring_nf

/-- The CDF is continuous on all of `ℝ`.  Using
`weightedSumCDF_eq_intervalIntegral` it is rewritten as a difference of
two primitives of itself, and interval primitives are continuous.
`weightedSumDistribution_singleton` deduces from this that the law has
no atoms. -/
lemma continuous_weightedSumCDF : Continuous weightedSumCDF := by
  have hint : ∀ a b : ℝ, IntervalIntegrable weightedSumCDF volume a b :=
    fun _ _ => (ProbabilityTheory.monotone_cdf weightedSumDistribution).intervalIntegrable
  have hp : Continuous (fun z : ℝ => ∫ t in (0 : ℝ)..z, weightedSumCDF t) :=
    intervalIntegral.continuous_primitive hint 0
  have hrepr : weightedSumCDF = fun y : ℝ =>
      (∫ t in (0 : ℝ)..(2 * y), weightedSumCDF t) -
        ∫ t in (0 : ℝ)..(2 * y - 1), weightedSumCDF t := by
    funext y
    rw [weightedSumCDF_eq_intervalIntegral]
    exact (intervalIntegral.integral_interval_sub_left (hint 0 (2 * y))
      (hint 0 (2 * y - 1))).symm
  rw [hrepr]
  exact (hp.comp (by fun_prop)).sub (hp.comp (by fun_prop))

/-- For arguments `x ≤ 0` the CDF vanishes: the event `X ≤ x` forces
`X = 0`, which forces the first coordinate to be `0`, a null event. -/
lemma weightedSumCDF_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    weightedSumCDF x = 0 := by
  rw [weightedSumCDF_eq_measureReal]
  have hsubset : {ω : SampleSpace | weightedCoordinateSum ω ≤ x} ⊆
      {ω : SampleSpace | weightedCoordinateSum ω = 0} := by
    intro ω hω
    exact le_antisymm (hω.trans hx) (weightedCoordinateSum_nonneg ω)
  have hzero : uniformProduct {ω : SampleSpace | weightedCoordinateSum ω = 0} = 0 := by
    have hcoord : {ω : SampleSpace | weightedCoordinateSum ω = 0} ⊆
        {ω : SampleSpace | ω 0 = 0} := by
      intro ω hω
      change weightedCoordinateSum ω = 0 at hω
      by_contra hn
      change ω 0 ≠ 0 at hn
      have hne : (ω 0 : ℝ) ≠ 0 := fun h => hn (Subtype.ext h)
      have hpos : 0 < (ω 0 : ℝ) := lt_of_le_of_ne (ω 0).property.1 (Ne.symm hne)
      have hle : (ω 0 : ℝ) / 2 ≤ weightedCoordinateSum ω := by
        rw [weightedCoordinateSum_split]
        have htail := weightedCoordinateSum_nonneg (tail ω)
        linarith
      linarith
    apply measure_mono_null hcoord
    calc
      uniformProduct {ω : SampleSpace | ω 0 = 0} =
          (uniformProduct.map fun ω => ω 0) {(0 : Set.Icc (0 : ℝ) 1)} := by
        rw [Measure.map_apply (μ := uniformProduct) (measurable_pi_apply 0)
          (measurableSet_singleton (0 : Set.Icc (0 : ℝ) 1))]
        rfl
      _ = (volume : Measure (Set.Icc (0 : ℝ) 1)) {0} := by
        rw [coordinate_has_uniform_law]
      _ = 0 := measure_singleton _
  apply measureReal_mono_null hsubset
  rw [measureReal_def, hzero]
  simp

/-- For arguments `1 ≤ x` the CDF equals `1`, since `X ≤ 1` holds
pointwise on the sample space. -/
lemma weightedSumCDF_one_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    weightedSumCDF x = 1 := by
  rw [weightedSumCDF_eq_measureReal]
  have hall : {ω : SampleSpace | weightedCoordinateSum ω ≤ x} = Set.univ := by
    ext ω
    simp only [mem_setOf_eq, mem_univ, iff_true]
    exact (weightedCoordinateSum_le_one ω).trans hx
  rw [hall, probReal_univ]

/-- The law of the random series has no atoms: every singleton is null.
This follows from continuity of the CDF, and supplies the
`NullSingletonClass` instance used by `weightedSumCDF_symmetry`. -/
lemma weightedSumDistribution_singleton (x : ℝ) :
    weightedSumDistribution {x} = 0 := by
  rw [← ProbabilityTheory.measure_cdf weightedSumDistribution,
    StieltjesFunction.measure_singleton]
  have hleft : Function.leftLim weightedSumCDF x = weightedSumCDF x :=
    continuous_weightedSumCDF.continuousAt.continuousWithinAt.leftLim_eq
  change ENNReal.ofReal (weightedSumCDF x - Function.leftLim weightedSumCDF x) = 0
  rw [hleft, sub_self, ENNReal.ofReal_zero]

/-- The law of the random series is symmetric about `1/2`. -/
lemma weightedSumCDF_symmetry (x : ℝ) :
    weightedSumCDF (1 - x) = 1 - weightedSumCDF x := by
  letI : NullSingletonClass weightedSumDistribution :=
    ⟨weightedSumDistribution_singleton⟩
  calc
    weightedSumCDF (1 - x) = weightedSumDistribution.real (Iic (1 - x)) := by
      rw [weightedSumCDF, ProbabilityTheory.cdf_eq_real]
    _ = (weightedSumDistribution.map (fun z : ℝ => 1 - z)).real (Iic (1 - x)) := by
      rw [weightedSumDistribution_reflection]
    _ = weightedSumDistribution.real ((fun z : ℝ => 1 - z) ⁻¹' Iic (1 - x)) := by
      rw [map_measureReal_apply (by fun_prop) measurableSet_Iic]
    _ = weightedSumDistribution.real (Ici x) := by
      have hset : ((fun z : ℝ => 1 - z) ⁻¹' Iic (1 - x)) = Ici x := by
        ext z
        change (1 - z ≤ 1 - x) ↔ x ≤ z
        constructor <;> intro hz <;> linarith
      rw [hset]
    _ = weightedSumDistribution.real (Iio x)ᶜ := by rw [compl_Iio]
    _ = 1 - weightedSumDistribution.real (Iio x) :=
      probReal_compl_eq_one_sub measurableSet_Iio
    _ = 1 - weightedSumDistribution.real (Iic x) := by
      rw [measureReal_congr Iio_ae_eq_Iic]
    _ = 1 - weightedSumCDF x := by
      rw [weightedSumCDF, ProbabilityTheory.cdf_eq_real]

/-- Symmetry fixes the value of the CDF at the midpoint. -/
@[simp] lemma weightedSumCDF_one_half : weightedSumCDF (1 / 2) = 1 / 2 := by
  have h := weightedSumCDF_symmetry (1 / 2)
  norm_num at h ⊢
  linarith

/-- Whenever `x ≤ 1/2`, the smoothing equation collapses to
`H x = ∫ t in 0..2 * x, H t`.  No lower bound on `x` is needed: the CDF
vanishes on the nonpositive axis, including in the reversed-orientation
integral when `x < 0`. -/
lemma weightedSumCDF_eq_intervalIntegral_of_le_half {x : ℝ}
    (hx : x ≤ 1 / 2) :
    weightedSumCDF x = ∫ t in (0 : ℝ)..(2 * x), weightedSumCDF t := by
  have hint : ∀ a b : ℝ, IntervalIntegrable weightedSumCDF volume a b :=
    fun _ _ => (ProbabilityTheory.monotone_cdf weightedSumDistribution).intervalIntegrable
  have hlower : 2 * x - 1 ≤ 0 := by linarith
  have hzero : (∫ t in (2 * x - 1)..(0 : ℝ), weightedSumCDF t) = 0 := by
    calc
      (∫ t in (2 * x - 1)..(0 : ℝ), weightedSumCDF t) =
          ∫ _t in (2 * x - 1)..(0 : ℝ), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_le hlower] at ht
        exact weightedSumCDF_zero_of_nonpos ht.2
      _ = 0 := intervalIntegral.integral_zero
  rw [weightedSumCDF_eq_intervalIntegral,
    ← intervalIntegral.integral_add_adjacent_intervals
      (hint (2 * x - 1) 0) (hint 0 (2 * x)), hzero, zero_add]

/-- Compatibility wrapper for the left-half interval formulation. -/
lemma weightedSumCDF_left_formula {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) (1 / 2)) :
    weightedSumCDF x = ∫ t in (0 : ℝ)..(2 * x), weightedSumCDF t :=
  weightedSumCDF_eq_intervalIntegral_of_le_half hx.2

/-- The CDF restricted to the unit interval, as an element of the function
space used in the existence proof. -/
noncomputable def cdfContinuousMap : Existence.C :=
  ⟨fun x => weightedSumCDF x, continuous_weightedSumCDF.comp continuous_subtype_val⟩

@[simp] lemma cdfContinuousMap_apply (x : Existence.I) :
    cdfContinuousMap x = weightedSumCDF x := rfl

/-- The restricted CDF is admissible in the sense of `Existence`: it
takes values in `[0,1]` and satisfies `f (1 - x) = 1 - f x`. -/
lemma cdfContinuousMap_admissible : Existence.admissible cdfContinuousMap := by
  constructor
  · intro x
    exact ⟨weightedSumCDF_nonneg x, weightedSumCDF_le_one x⟩
  · intro x
    change weightedSumCDF (1 - (x : ℝ)) = 1 - weightedSumCDF x
    exact weightedSumCDF_symmetry x

/-- The restricted CDF packaged as a point of `Existence.admissibleSet`,
the complete metric space on which `Existence.transformSelf` is a
contraction. -/
noncomputable def cdfAdmissible : Existence.admissibleSet :=
  ⟨cdfContinuousMap, cdfContinuousMap_admissible⟩

private lemma cumulative_cdfContinuousMap {y : ℝ} (hy : y ∈ Icc (0 : ℝ) 1) :
    Existence.cumulative cdfContinuousMap y =
      ∫ t in (0 : ℝ)..y, weightedSumCDF t := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hy.1] at ht
  rw [Existence.extend_eq cdfContinuousMap ⟨ht.1, ht.2.trans hy.2⟩]
  rfl

/-- The restricted CDF is a fixed point of `Existence.transformSelf`.
The `x ≤ 1/2` branch is
`weightedSumCDF_eq_intervalIntegral_of_le_half`; the other branch combines
that formula with `weightedSumCDF_symmetry`. -/
lemma cdfAdmissible_fixed :
    Existence.transformSelf cdfAdmissible = cdfAdmissible := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  change Existence.transformValue cdfContinuousMap x = weightedSumCDF x
  by_cases hx : (x : ℝ) ≤ 1 / 2
  · rw [Existence.transformValue, if_pos hx]
    have h2x : 2 * (x : ℝ) ∈ Icc (0 : ℝ) 1 := by
      constructor <;> linarith [x.property.1]
    rw [cumulative_cdfContinuousMap h2x]
    exact (weightedSumCDF_eq_intervalIntegral_of_le_half hx).symm
  · rw [Existence.transformValue, if_neg hx]
    have hxhalf : 1 / 2 < (x : ℝ) := lt_of_not_ge hx
    have honeSub : 1 - (x : ℝ) ≤ 1 / 2 := by linarith
    have harg : 2 - 2 * (x : ℝ) ∈ Icc (0 : ℝ) 1 := by
      constructor <;> linarith [x.property.2]
    rw [cumulative_cdfContinuousMap harg]
    have hleft := weightedSumCDF_eq_intervalIntegral_of_le_half honeSub
    have hsymm := weightedSumCDF_symmetry (x : ℝ)
    have heq : 2 * (1 - (x : ℝ)) = 2 - 2 * (x : ℝ) := by ring
    rw [heq] at hleft
    linarith

/-- By uniqueness of the fixed point of the contraction
`Existence.transformSelf`, the restricted CDF is exactly
`Existence.fixedCandidate`. -/
lemma cdfAdmissible_eq_fixedCandidate :
    cdfAdmissible = Existence.fixedCandidate :=
  Existence.transformSelf_contracting.fixedPoint_unique cdfAdmissible_fixed

/-- On `[0,1]` the CDF agrees with `Existence.boundedCandidate`.  This is
the step from the fixed-point identification to
`weightedSumCDF_eq_fabiusReal`, which drops the restriction on `x`. -/
lemma weightedSumCDF_eq_boundedCandidate {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    weightedSumCDF x = fabiusReal Existence.boundedCandidate x := by
  change weightedSumCDF x = Existence.extend Existence.fixedCandidate.1 x
  rw [Existence.extend_eq Existence.fixedCandidate.1 hx]
  have h := congrArg (fun f : Existence.admissibleSet => f.1 ⟨x, hx⟩)
    cdfAdmissible_eq_fixedCandidate
  exact h

/-- The random-series CDF is the unique bounded Fabius function, globally on
`ℝ`.  Quantifying over `F` makes this immediately applicable to the canonical
choice `fabius` as well as to any locally bundled construction. -/
theorem weightedSumCDF_eq_fabiusReal
    (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    weightedSumCDF x = fabiusReal F x := by
  by_cases hx0 : x ≤ 0
  · rw [weightedSumCDF_zero_of_nonpos hx0, hF.zero_of_nonpos x hx0]
  by_cases hx1 : 1 ≤ x
  · rw [weightedSumCDF_one_of_one_le hx1, hF.one_of_one_le x hx1]
  have hx : x ∈ Icc (0 : ℝ) 1 :=
    ⟨(lt_of_not_ge hx0).le, (lt_of_not_ge hx1).le⟩
  rw [weightedSumCDF_eq_boundedCandidate hx]
  have hF_eq := Existence.isFabius_eq F Existence.boundedCandidate hF
    Existence.boundedCandidate_isFabius
  rw [hF_eq]

/-- The Rvachev bump is the random-series CDF evaluated at its distance from
the boundary of the support.  Unlike the paper's left-half formulation below,
this identity holds for every real argument; outside `[-1, 1]`, both sides
vanish automatically. -/
theorem rvachevUp_eq_weightedSumCDF
    (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    rvachevUp F x = weightedSumCDF (1 - |x|) := by
  rw [weightedSumCDF_eq_fabiusReal F hF, rvachevUp]
  split_ifs with hx
  · rw [abs_of_nonpos hx]
    congr 1
    ring
  · rw [abs_of_pos (lt_of_not_ge hx)]

/-- All-real probability representation of Rvachev's function:
`up(x) = P[X ≤ 1 - |x|]` for the weighted sum of independent uniforms.
Here “global” refers to the unrestricted real input, not to `globalFabius`. -/
theorem rvachevUp_eq_weightedSum_probability_global
    (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    rvachevUp F x = uniformProduct.real
      {ω : SampleSpace | weightedCoordinateSum ω ≤ 1 - |x|} := by
  rw [rvachevUp_eq_weightedSumCDF F hF x,
    weightedSumCDF_eq_measureReal]

/-- The all-real representation of `rvachevUp` in the probability measure's
native `ℝ≥0∞` codomain.  This is unrelated to the signed `globalFabius`. -/
theorem ofReal_rvachevUp_eq_weightedSum_probability_global
    (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    ENNReal.ofReal (rvachevUp F x) = uniformProduct
      {ω : SampleSpace | weightedCoordinateSum ω ≤ 1 - |x|} := by
  rw [rvachevUp_eq_weightedSum_probability_global F hF x,
    ofReal_measureReal]

/-- The bounded Fabius function is the distribution function of the random
series, with no restriction on the real argument. -/
theorem fabiusReal_eq_weightedSum_probability
    (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    fabiusReal F x =
      uniformProduct.real {ω : SampleSpace | weightedCoordinateSum ω ≤ x} := by
  rw [← weightedSumCDF_eq_measureReal,
    weightedSumCDF_eq_fabiusReal F hF]

/-- The all-real bounded-CDF representation in the probability measure's native
`ℝ≥0∞` codomain. -/
theorem ofReal_fabiusReal_eq_weightedSum_probability
    (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    ENNReal.ofReal (fabiusReal F x) =
      uniformProduct {ω : SampleSpace | weightedCoordinateSum ω ≤ x} := by
  rw [fabiusReal_eq_weightedSum_probability F hF, ofReal_measureReal]

/-- Theorem 3 of arXiv:1702.05442, in its source-facing real-probability form
on `[-1,0]`.  The unrestricted strengthening is
`rvachevUp_eq_weightedSum_probability_global`. -/
theorem rvachevUp_eq_weightedSum_probability
    (F : BoundedFabius) (hF : IsFabius F) {x : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 0) :
    rvachevUp F x = uniformProduct.real
      {ω : SampleSpace |
        0 ≤ weightedCoordinateSum ω ∧ weightedCoordinateSum ω ≤ x + 1} := by
  have hset : {ω : SampleSpace | weightedCoordinateSum ω ≤ 1 - |x|} =
      {ω : SampleSpace |
        0 ≤ weightedCoordinateSum ω ∧ weightedCoordinateSum ω ≤ x + 1} := by
    ext ω
    simp only [mem_setOf_eq]
    rw [abs_of_nonpos hx.2]
    constructor
    · intro hω
      exact ⟨weightedCoordinateSum_nonneg ω, by linarith⟩
    · intro hω
      linarith [hω.2]
  rw [rvachevUp_eq_weightedSum_probability_global F hF x, hset]

/-- The same source-facing theorem with the probability left in its native
`ℝ≥0∞` codomain.  See `ofReal_rvachevUp_eq_weightedSum_probability_global`
for the unrestricted real-domain strengthening. -/
theorem ofReal_rvachevUp_eq_weightedSum_probability
    (F : BoundedFabius) (hF : IsFabius F) {x : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 0) :
    ENNReal.ofReal (rvachevUp F x) = uniformProduct
      {ω : SampleSpace |
        0 ≤ weightedCoordinateSum ω ∧ weightedCoordinateSum ω ≤ x + 1} := by
  rw [rvachevUp_eq_weightedSum_probability F hF hx,
    ofReal_measureReal]

end
end ProbabilityRepresentation
end Fabius
