import FabiusFunction.WeightedUniformSeries

/-!
# Compatibility refinements for weighted uniform laws

`WeightedUniformSeries.lean` owns the general series and its canonical
pushforward-law API.  This module preserves the alternative public naming
introduced with the geometric-law layer and adds the refinements not needed
by the core file:

* scalar naturality of the pushforward law;
* a shifted-tail joint-law wrapper;
* unit-mass interval and complement corollaries.

The compatibility declarations below are thin consequences of the canonical
foundation, so no probability or head--tail argument is duplicated.
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
        (uniformProduct.map f) :=
  uniformProduct_map_head_tail_comp hf

/-! ## Vector-valued law refinements -/

/-- A norm-summable weight sequence gives a probability law. -/
theorem weightedUniformDistribution_isProbabilityMeasure
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {w : ℕ → E} (hw : Summable fun n => ‖w n‖) :
    IsProbabilityMeasure (weightedUniformDistribution w) :=
  isProbabilityMeasure_weightedUniformDistribution hw

/-- Scaling all weights pushes the law forward by the same scalar map. -/
theorem weightedUniformDistribution_smul_weights
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    (a : ℝ) {w : ℕ → E} (hw : Summable fun n => ‖w n‖) :
    weightedUniformDistribution (fun n => a • w n) =
      (weightedUniformDistribution w).map (fun x => a • x) :=
  (weightedUniformDistribution_smul a hw).symm

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

/-! ## Unit-mass real corollaries -/

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
