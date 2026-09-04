import FabiusFunction.WeightedUniformSeries

/-!
# Compatibility refinements for weighted uniform laws

`WeightedUniformSeries.lean` owns the general series and its canonical
pushforward-law API.  This module preserves the alternative public naming
introduced with the geometric-law layer and adds the refinements not needed
by the core file:

* scalar naturality of the pushforward law;
* a shifted-tail joint-law wrapper;
* the exact barycenter from reflection and bounded-series integrability;
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

/-! ## Smoothing by one uniform coordinate -/

/-- Adding a nontrivially scaled uniform coordinate to an independent
real-valued random variable produces a law absolutely continuous with
respect to Lebesgue measure.

The second marginal is allowed to be any s-finite measure; in particular,
it need not itself be absolutely continuous.  The map is written in the
coordinate-first orientation `(u, x) ↦ (u : ℝ) * a + x`, matching the scalar
action used by `weightedUniformDistribution_split`. -/
theorem uniformScaledAdd_absolutelyContinuous
    (μ : Measure ℝ) [SFinite μ] {a : ℝ} (ha : a ≠ 0) :
    (((volume : Measure (Set.Icc (0 : ℝ) 1)).prod μ).map
        (fun p => (p.1 : ℝ) * a + p.2)) ≪
      (volume : Measure ℝ) := by
  have hcombine : Measurable
      (fun p : Set.Icc (0 : ℝ) 1 × ℝ => (p.1 : ℝ) * a + p.2) := by
    fun_prop
  refine Measure.AbsolutelyContinuous.mk fun s hs hvolume => ?_
  rw [Measure.map_apply hcombine hs,
    Measure.prod_apply_symm (hs.preimage hcombine)]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards with y
  let t : Set ℝ := (fun x : ℝ => x * a + y) ⁻¹' s
  have ht : MeasurableSet t := hs.preimage (by fun_prop)
  have ht_eq :
      t = (fun x : ℝ => x * a) ⁻¹' ((fun x : ℝ => y + x) ⁻¹' s) := by
    ext x
    simp only [t, Set.mem_preimage]
    rw [add_comm]
  have ht_volume : (volume : Measure ℝ) t = 0 := by
    rw [ht_eq, Real.volume_preimage_mul_right ha,
      measure_preimage_add, hvolume, mul_zero]
  have hsubtype :
      (volume : Measure (Set.Icc (0 : ℝ) 1))
          (((↑) : Set.Icc (0 : ℝ) 1 → ℝ) ⁻¹' t) = 0 := by
    rw [volume_preimage_coe
      measurableSet_Icc.nullMeasurableSet ht]
    exact measure_mono_null inter_subset_left ht_volume
  change (volume : Measure (Set.Icc (0 : ℝ) 1))
      (((↑) : Set.Icc (0 : ℝ) 1 → ℝ) ⁻¹' t) = 0
  exact hsubtype

/-! ## Vector-valued law refinements -/

/-- A norm-summable weight sequence gives a probability law. -/
theorem weightedUniformDistribution_isProbabilityMeasure
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {w : ℕ → E} (hw : Summable fun n => ‖w n‖) :
    IsProbabilityMeasure (weightedUniformDistribution w) :=
  isProbabilityMeasure_weightedUniformDistribution hw

/-- The identity is Bochner integrable against every norm-summable
weighted-uniform law.

The proof does not exchange an integral with the infinite series.  Instead,
the series map is strongly measurable and is pointwise bounded in norm by
the summable total norm of the weights; integrability is then transported
through the defining pushforward. -/
private theorem integrable_id_weightedUniformDistribution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {w : ℕ → E} (hw : Summable fun n => ‖w n‖) :
    Integrable (fun x : E => x) (weightedUniformDistribution w) := by
  have hseriesStrong :
      StronglyMeasurable (weightedUniformSeries w) :=
    (continuous_weightedUniformSeries hw).stronglyMeasurable
  have hseriesIntegrable :
      Integrable (weightedUniformSeries w) uniformProduct := by
    refine Integrable.mono'
      (integrable_const (∑' n : ℕ, ‖w n‖))
      hseriesStrong.aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall
      (norm_weightedUniformSeries_le hw)
  rw [weightedUniformDistribution]
  have hid :
      AEStronglyMeasurable (id : E → E)
        (uniformProduct.map (weightedUniformSeries w)) :=
    hseriesStrong.aestronglyMeasurable.aestronglyMeasurable_id_map
  exact
    (integrable_map_measure hid
      (measurable_weightedUniformSeries hw).aemeasurable).2
      (by simpa only [Function.id_comp] using hseriesIntegrable)

/-- The barycenter of a norm-summable weighted uniform-coordinate law is
half the total vector weight:

`∫ x, x ∂weightedUniformDistribution w = (1 / 2) • ∑' n, w n`.

This holds in every complete real normed space with its Borel measurable
structure.  No sign, order, independence expansion, or termwise
integration is needed.  Bounded-series integrability makes the identity
integrable, and central reflection of the law gives
`totalWeight - mean = mean`. -/
theorem integral_id_weightedUniformDistribution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
    {w : ℕ → E} (hw : Summable fun n => ‖w n‖) :
    (∫ x : E, x ∂weightedUniformDistribution w) =
      (1 / 2 : ℝ) • ∑' n : ℕ, w n := by
  letI : IsProbabilityMeasure (weightedUniformDistribution w) :=
    weightedUniformDistribution_isProbabilityMeasure hw
  have hid :
      Integrable (fun x : E => x) (weightedUniformDistribution w) :=
    integrable_id_weightedUniformDistribution hw
  have hidMap :
      AEStronglyMeasurable (fun x : E => x)
        ((weightedUniformDistribution w).map
          (fun x => (∑' n : ℕ, w n) - x)) := by
    rw [weightedUniformDistribution_reflection hw]
    exact hid.aestronglyMeasurable
  have hreflected :
      (∫ x : E, (∑' n : ℕ, w n) - x
          ∂weightedUniformDistribution w) =
        ∫ x : E, x ∂weightedUniformDistribution w := by
    calc
      (∫ x : E, (∑' n : ℕ, w n) - x
          ∂weightedUniformDistribution w) =
          ∫ x : E, (fun y : E => y) ((∑' n : ℕ, w n) - x)
            ∂weightedUniformDistribution w := rfl
      _ = ∫ y : E, (fun x : E => x) y
          ∂(weightedUniformDistribution w).map
            (fun x => (∑' n : ℕ, w n) - x) :=
        (MeasureTheory.integral_map
          (by fun_prop :
            AEMeasurable (fun x : E => (∑' n : ℕ, w n) - x)
              (weightedUniformDistribution w))
          hidMap).symm
      _ = ∫ x : E, x ∂weightedUniformDistribution w := by
        rw [weightedUniformDistribution_reflection hw]
  have hconst :
      Integrable (fun _ : E => ∑' n : ℕ, w n)
        (weightedUniformDistribution w) :=
    integrable_const _
  rw [MeasureTheory.integral_sub hconst hid] at hreflected
  simp only [MeasureTheory.integral_const, probReal_univ, one_smul] at hreflected
  have htotal :
      (∑' n : ℕ, w n) =
        (∫ x : E, x ∂weightedUniformDistribution w) +
          ∫ x : E, x ∂weightedUniformDistribution w :=
    (sub_eq_iff_eq_add).mp hreflected
  rw [htotal, ← two_smul ℝ, ← mul_smul]
  norm_num

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

/-! ## Absolute continuity of nontrivial real weighted laws -/

/-- A real weighted-uniform law is absolutely continuous as soon as its
first weight is nonzero.

This is the one-step workhorse: split off the first coordinate, regard the
shifted series as an arbitrary independent s-finite tail law, and apply
`uniformScaledAdd_absolutelyContinuous`.  The theorem below removes the
head-position restriction. -/
theorem weightedUniformDistribution_absolutelyContinuous_of_head_ne_zero
    {w : ℕ → ℝ} (hw : Summable fun n => ‖w n‖)
    (hhead : w 0 ≠ 0) :
    weightedUniformDistribution w ≪ (volume : Measure ℝ) := by
  have hwtail := summable_norm_weight_tail hw
  letI : IsProbabilityMeasure
      (weightedUniformDistribution fun n => w (Nat.succ n)) :=
    weightedUniformDistribution_isProbabilityMeasure hwtail
  rw [weightedUniformDistribution_split hw]
  simpa only [smul_eq_mul] using
    (uniformScaledAdd_absolutelyContinuous
      (weightedUniformDistribution fun n => w (Nat.succ n)) hhead)

/-- Every nontrivial norm-summable real weighted-uniform law is absolutely
continuous with respect to Lebesgue measure.

The nontriviality hypothesis is sharp: it asks for a nonzero weight at an
arbitrary index, not necessarily at the head.  The proof discards any zero
prefix using the head--tail law splitting until the first exhibited nonzero
coordinate becomes available to the uniform smoothing theorem. -/
theorem weightedUniformDistribution_absolutelyContinuous
    {w : ℕ → ℝ} (hw : Summable fun n => ‖w n‖)
    (hwne : ∃ n, w n ≠ 0) :
    weightedUniformDistribution w ≪ (volume : Measure ℝ) := by
  rcases hwne with ⟨k, hk⟩
  induction k generalizing w with
  | zero =>
      exact weightedUniformDistribution_absolutelyContinuous_of_head_ne_zero hw hk
  | succ k ih =>
      by_cases hzero : w 0 = 0
      · have hwtail := summable_norm_weight_tail hw
        letI : IsProbabilityMeasure
            (weightedUniformDistribution fun n => w (Nat.succ n)) :=
          weightedUniformDistribution_isProbabilityMeasure hwtail
        have htail_ac :
            weightedUniformDistribution (fun n => w (Nat.succ n)) ≪
              (volume : Measure ℝ) :=
          ih hwtail hk
        calc
          weightedUniformDistribution w =
              weightedUniformDistribution (fun n => w (Nat.succ n)) := by
            calc
              weightedUniformDistribution w =
                  ((volume : Measure (Set.Icc (0 : ℝ) 1)).prod
                    (weightedUniformDistribution fun n => w (Nat.succ n))).map
                      (fun p => (p.1 : ℝ) • w 0 + p.2) :=
                weightedUniformDistribution_split hw
              _ = ((volume : Measure (Set.Icc (0 : ℝ) 1)).prod
                    (weightedUniformDistribution fun n => w (Nat.succ n))).map
                      Prod.snd := by
                apply Measure.map_congr
                filter_upwards with p
                simp only [hzero, smul_zero, zero_add]
              _ = weightedUniformDistribution (fun n => w (Nat.succ n)) := by
                simp only [Measure.map_snd_prod, measure_univ, one_smul]
          _ ≪ (volume : Measure ℝ) := htail_ac
      · exact
          weightedUniformDistribution_absolutelyContinuous_of_head_ne_zero hw hzero

/-- A nontrivial norm-summable real weighted-uniform law has no atoms.

This theorem returns the typeclass explicitly, allowing callers to install
it locally only after supplying the analytic summability and nontriviality
hypotheses. -/
theorem weightedUniformDistribution_nullSingletonClass
    {w : ℕ → ℝ} (hw : Summable fun n => ‖w n‖)
    (hwne : ∃ n, w n ≠ 0) :
    NullSingletonClass (weightedUniformDistribution w) := by
  refine ⟨fun x => ?_⟩
  exact weightedUniformDistribution_absolutelyContinuous hw hwne
    (measure_singleton x : (volume : Measure ℝ) {x} = 0)

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
