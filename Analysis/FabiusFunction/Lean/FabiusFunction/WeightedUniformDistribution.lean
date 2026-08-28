import FabiusFunction.WeightedUniformSeries

/-!
# Laws of absolutely summable uniform-coordinate series

This file passes the general weighted series from
`WeightedUniformSeries.lean` to the level of probability laws.  For an
absolutely summable vector-weight sequence `w`, it records:

* the pushforward probability measure of the weighted series;
* the joint law of the first coordinate and the shifted tail series;
* the resulting affine head--tail decomposition of the law;
* reflection about half of the total vector weight;
* concentration on the natural interval for nonnegative real weights.

No relation between consecutive weights is assumed.  Geometric
self-similarity is therefore a specialization of the affine decomposition,
not a separate measure-theoretic argument.
-/

open Filter Set MeasureTheory ProbabilityTheory Topology
open scoped BigOperators unitInterval

namespace Fabius
namespace ProbabilityRepresentation

set_option autoImplicit false
noncomputable section

/-! ## A generic head--tail pushforward -/

/-- Applying an arbitrary measurable observable to the shifted tail keeps
it independent of the first uniform coordinate. -/
theorem uniformProduct_map_head_tail_function
    {E : Type*} [MeasurableSpace E]
    (f : SampleSpace → E) (hf : Measurable f) :
    uniformProduct.map (fun ω : SampleSpace => (ω 0, f (tail ω))) =
      (volume : Measure (Set.Icc (0 : ℝ) 1)).prod
        (uniformProduct.map f) := by
  have hind := independent_head_tail.comp measurable_id hf
  have h := hind.map_prod_eq_prod_map_map
    (measurable_pi_apply 0).aemeasurable
    (hf.comp measurable_tail).aemeasurable
  have hhead := coordinate_has_uniform_law 0
  have htail : uniformProduct.map (f ∘ tail) = uniformProduct.map f := by
    rw [← Measure.map_map hf measurable_tail, uniformProduct_map_tail]
  rwa [hhead, htail] at h

/-! ## Vector-valued laws -/

/-- The pushforward measure of an arbitrary uniform-coordinate series.
The definition is total; the probability-law interpretation is certified
below under norm summability. -/
noncomputable def weightedUniformDistribution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] (w : ℕ → E) : Measure E :=
  uniformProduct.map (weightedUniformSeries w)

/-- A norm-summable weight sequence gives a probability law. -/
theorem weightedUniformDistribution_isProbabilityMeasure
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {w : ℕ → E} (hw : Summable fun n => ‖w n‖) :
    IsProbabilityMeasure (weightedUniformDistribution w) :=
  Measure.isProbabilityMeasure_map
    (measurable_weightedUniformSeries hw).aemeasurable

/-- Scaling all weights pushes the law forward by the same scalar map. -/
theorem weightedUniformDistribution_smul_weights
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    (a : ℝ) {w : ℕ → E} (hw : Summable fun n => ‖w n‖) :
    weightedUniformDistribution (fun n => a • w n) =
      (weightedUniformDistribution w).map (fun x => a • x) := by
  rw [weightedUniformDistribution, weightedUniformDistribution,
    Measure.map_map (by fun_prop) (measurable_weightedUniformSeries hw)]
  apply Measure.map_congr
  filter_upwards with ω
  exact weightedUniformSeries_smul_weights a w ω

private theorem summable_norm_weight_tail
    {E : Type*} [NormedAddCommGroup E]
    {w : ℕ → E} (hw : Summable fun n => ‖w n‖) :
    Summable fun n => ‖w (Nat.succ n)‖ := by
  simpa only [Nat.succ_eq_add_one, Nat.add_comm] using
    (summable_nat_add_iff 1).mpr hw

/-- The first uniform coordinate and the shifted weighted tail have the
product of their marginal laws. -/
theorem uniformProduct_map_head_tail_weightedUniformSeries
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {w : ℕ → E} (hw : Summable fun n => ‖w n‖) :
    uniformProduct.map
        (fun ω : SampleSpace =>
          (ω 0, weightedUniformSeries (fun n => w (Nat.succ n)) (tail ω))) =
      (volume : Measure (Set.Icc (0 : ℝ) 1)).prod
        (weightedUniformDistribution fun n => w (Nat.succ n)) := by
  have hwtail := summable_norm_weight_tail hw
  simpa only [weightedUniformDistribution] using
    uniformProduct_map_head_tail_function
      (weightedUniformSeries fun n => w (Nat.succ n))
      (measurable_weightedUniformSeries hwtail)

/-- The law of an arbitrary weighted series is the affine image of one
uniform coordinate and the law of its shifted weighted tail. -/
theorem weightedUniformDistribution_split
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {w : ℕ → E} (hw : Summable fun n => ‖w n‖) :
    weightedUniformDistribution w =
      ((volume : Measure (Set.Icc (0 : ℝ) 1)).prod
        (weightedUniformDistribution fun n => w (Nat.succ n))).map
          (fun p => (p.1 : ℝ) • w 0 + p.2) := by
  change uniformProduct.map (weightedUniformSeries w) =
    ((volume : Measure (Set.Icc (0 : ℝ) 1)).prod
      (uniformProduct.map
        (weightedUniformSeries fun n => w (Nat.succ n)))).map
          (fun p => (p.1 : ℝ) • w 0 + p.2)
  have hjoint :
      uniformProduct.map
          (fun ω : SampleSpace =>
            (ω 0, weightedUniformSeries (fun n => w (Nat.succ n)) (tail ω))) =
        (volume : Measure (Set.Icc (0 : ℝ) 1)).prod
          (uniformProduct.map
            (weightedUniformSeries fun n => w (Nat.succ n))) := by
    simpa only [weightedUniformDistribution] using
      uniformProduct_map_head_tail_weightedUniformSeries hw
  rw [← hjoint]
  rw [Measure.map_map (μ := uniformProduct)
    (f := fun ω : SampleSpace =>
      (ω 0, weightedUniformSeries (fun n => w (Nat.succ n)) (tail ω)))
    (g := fun p : Set.Icc (0 : ℝ) 1 × E => (p.1 : ℝ) • w 0 + p.2)
    ((((continuous_subtype_val.comp continuous_fst).smul continuous_const).add
      continuous_snd).measurable)
    ((measurable_pi_apply 0).prodMk
      ((measurable_weightedUniformSeries (summable_norm_weight_tail hw)).comp
        measurable_tail))]
  apply Measure.map_congr
  filter_upwards with ω
  exact weightedUniformSeries_split hw ω

/-- Reflecting all coordinates reflects the law about half of the total
vector weight. -/
theorem weightedUniformDistribution_reflection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {w : ℕ → E} (hw : Summable fun n => ‖w n‖) :
    (weightedUniformDistribution w).map
        (fun x => (∑' n : ℕ, w n) - x) =
      weightedUniformDistribution w := by
  rw [weightedUniformDistribution,
    Measure.map_map (by fun_prop) (measurable_weightedUniformSeries hw)]
  calc
    uniformProduct.map
          ((fun x => (∑' n : ℕ, w n) - x) ∘ weightedUniformSeries w) =
        uniformProduct.map
          (weightedUniformSeries w ∘ reflectCoordinates) := by
      apply Measure.map_congr
      filter_upwards with ω
      exact (weightedUniformSeries_reflect hw ω).symm
    _ = (uniformProduct.map reflectCoordinates).map
        (weightedUniformSeries w) := by
      rw [Measure.map_map (measurable_weightedUniformSeries hw)
        measurable_reflectCoordinates]
    _ = uniformProduct.map (weightedUniformSeries w) := by
      rw [uniformProduct_map_reflectCoordinates]

/-! ## Ordered real laws -/

/-- The law of nonnegative real weights is concentrated on the interval
from zero to their total mass. -/
theorem weightedUniformDistribution_Icc
    {w : ℕ → ℝ} (hw : Summable fun n => ‖w n‖)
    (hwnonneg : ∀ n, 0 ≤ w n) :
    weightedUniformDistribution w (Icc 0 (∑' n : ℕ, w n)) = 1 := by
  rw [weightedUniformDistribution,
    Measure.map_apply (measurable_weightedUniformSeries hw) measurableSet_Icc]
  have hpreimage :
      weightedUniformSeries w ⁻¹' Icc 0 (∑' n : ℕ, w n) = Set.univ :=
    Set.eq_univ_of_forall (weightedUniformSeries_mem_Icc hw hwnonneg)
  rw [hpreimage, measure_univ]

/-- A nonnegative weighted law gives no mass to the complement of its
natural interval. -/
theorem weightedUniformDistribution_compl_Icc
    {w : ℕ → ℝ} (hw : Summable fun n => ‖w n‖)
    (hwnonneg : ∀ n, 0 ≤ w n) :
    weightedUniformDistribution w
        ((Icc 0 (∑' n : ℕ, w n))ᶜ) = 0 := by
  letI : IsProbabilityMeasure (weightedUniformDistribution w) :=
    weightedUniformDistribution_isProbabilityMeasure hw
  rw [measure_compl measurableSet_Icc (by simp),
    weightedUniformDistribution_Icc hw hwnonneg,
    measure_univ, tsub_self]

/-- The law of unit-mass nonnegative real weights is concentrated on the
unit interval. -/
theorem weightedUniformDistribution_unitInterval
    {w : ℕ → ℝ} (hw : Summable fun n => ‖w n‖)
    (hwnonneg : ∀ n, 0 ≤ w n) (hmass : ∑' n : ℕ, w n = 1) :
    weightedUniformDistribution w (Icc (0 : ℝ) 1) = 1 := by
  simpa only [hmass] using weightedUniformDistribution_Icc hw hwnonneg

/-- A unit-mass nonnegative weighted law gives no mass to the complement
of the unit interval. -/
theorem weightedUniformDistribution_compl_unitInterval
    {w : ℕ → ℝ} (hw : Summable fun n => ‖w n‖)
    (hwnonneg : ∀ n, 0 ≤ w n) (hmass : ∑' n : ℕ, w n = 1) :
    weightedUniformDistribution w ((Icc (0 : ℝ) 1)ᶜ) = 0 := by
  simpa only [hmass] using weightedUniformDistribution_compl_Icc hw hwnonneg

end

end ProbabilityRepresentation
end Fabius
