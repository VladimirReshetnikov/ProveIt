import FabiusFunction.WeightedUniformSeries
import Mathlib.MeasureTheory.Measure.Support

/-!
# Exact support of weighted uniform-coordinate laws

This file upgrades carried-set statements to exact topological-support
identities.  The proof is deliberately split into two reusable facts:

* a continuous image of a measure positive on nonempty open sets has support
  equal to the closure of its range;
* the range of a real weighted uniform-coordinate series is exactly the
  interval from the sum of its negative parts to the sum of its positive
  parts.

The first statement is independent of weighted series.  For signed weights,
connectedness of the coordinate cube fills the interval between the two
extremal coordinate choices.  The nonnegative specialization also has a
direct constant-coordinate proof, including the degenerate zero-mass case.
-/

open Filter Set MeasureTheory ProbabilityTheory Topology
open scoped BigOperators unitInterval

namespace Fabius
namespace ProbabilityRepresentation

set_option autoImplicit false
noncomputable section

/-! ## Open positivity and continuous pushforwards -/

private lemma unitInterval_volume_isOpenPosMeasure :
    (volume : Measure (Set.Icc (0 : ℝ) 1)).IsOpenPosMeasure := by
  constructor
  intro U hU hUne
  obtain ⟨a, b, hab, hsub⟩ := hU.exists_Ioo_subset hUne
  apply ne_of_gt
  apply lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [unitInterval.volume_Ioo]
  exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)

/-- An arbitrary product of open-positive probability measures is itself
positive on every nonempty open set.

This is the infinite-product analogue of Mathlib's finite-product instance
for `Measure.pi`.  The proof reduces a nonempty open set to a finite open
cylinder and evaluates that cylinder by `Measure.infinitePi_pi`. -/
theorem isOpenPosMeasure_infinitePi
    {ι : Type*} {X : ι → Type*}
    [∀ i, TopologicalSpace (X i)] [∀ i, MeasurableSpace (X i)]
    [∀ i, OpensMeasurableSpace (X i)]
    (mu : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (mu i)]
    [∀ i, (mu i).IsOpenPosMeasure] :
    (Measure.infinitePi mu).IsOpenPosMeasure := by
  constructor
  rintro U hU ⟨x, hx⟩
  obtain ⟨indices, u, hu, hsub⟩ := (isOpen_pi_iff.mp hU) x hx
  apply ne_of_gt
  apply lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Measure.infinitePi_pi]
  · rw [CanonicallyOrderedAdd.prod_pos]
    intro i hi
    exact (hu i hi).1.measure_pos _ ⟨x i, (hu i hi).2⟩
  · intro i hi
    exact (hu i hi).1.measurableSet

/-- The countable product of uniform unit-interval laws gives positive mass
to every nonempty open subset of the full sample space. -/
instance uniformProduct_isOpenPosMeasure :
    uniformProduct.IsOpenPosMeasure := by
  letI : (volume : Measure (Set.Icc (0 : ℝ) 1)).IsOpenPosMeasure :=
    unitInterval_volume_isOpenPosMeasure
  unfold uniformProduct
  exact isOpenPosMeasure_infinitePi
    (fun _ : ℕ => (volume : Measure (Set.Icc (0 : ℝ) 1)))

/-- The support of the pushforward of an open-positive measure through a
continuous map is the closure of the map's range.

No compactness, injectivity, surjectivity, or finiteness hypothesis is
required. -/
theorem support_map_eq_closure_range_of_continuous
    {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [TopologicalSpace Y] [MeasurableSpace Y]
    [BorelSpace Y] (mu : Measure X) [mu.IsOpenPosMeasure]
    {f : X → Y} (hf : Continuous f) :
    (mu.map f).support = closure (Set.range f) := by
  apply Set.Subset.antisymm
  · apply Measure.support_subset_of_isClosed isClosed_closure
    rw [mem_ae_iff, Measure.map_apply hf.measurable
      isClosed_closure.isOpen_compl.measurableSet]
    have hpreimage : f ⁻¹' (closure (Set.range f))ᶜ = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hx (subset_closure ⟨x, rfl⟩)
    rw [hpreimage, measure_empty]
  · apply closure_minimal _ Measure.isClosed_support
    rintro y ⟨x, rfl⟩
    rw [Measure.support_eq_forall_isOpen]
    intro U hfx hU
    rw [Measure.map_apply hf.measurable hU.measurableSet]
    exact (hU.preimage hf).measure_pos mu ⟨x, hfx⟩

/-! ## Exact range and support -/

/-- On a constant coordinate path, the weighted series is the same scalar
multiple of the total weight.  This identity is total and does not require
summability. -/
theorem weightedUniformSeries_constCoordinates
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : ℕ → E) (u : Set.Icc (0 : ℝ) 1) :
    weightedUniformSeries w (fun _ => u) =
      (u : ℝ) • ∑' n : ℕ, w n := by
  unfold weightedUniformSeries
  rw [tsum_const_smul'']

/-- In a complete Borel real normed space, the topological support of an
absolutely summable weighted-uniform law is exactly the range of its series
map.  The range is already closed because it is the continuous image of the
compact coordinate cube. -/
theorem weightedUniformDistribution_support_eq_range
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    {w : ℕ → E} (hw : Summable fun n => ‖w n‖) :
    (weightedUniformDistribution w).support =
      Set.range (weightedUniformSeries w) := by
  rw [weightedUniformDistribution,
    support_map_eq_closure_range_of_continuous uniformProduct
      (continuous_weightedUniformSeries hw),
    (isCompact_range (continuous_weightedUniformSeries hw)).isClosed.closure_eq]

/-- For arbitrary summable real weights, the range is the closed interval
whose endpoints are obtained by selecting every negative, respectively every
positive, weight.  Thus cancellation and sign changes do not create gaps in
the attainable set. -/
theorem range_weightedUniformSeries_eq_Icc_min_max
    {w : ℕ → ℝ} (hw : Summable fun n => ‖w n‖) :
    Set.range (weightedUniformSeries w) =
      Icc (∑' n : ℕ, min (w n) 0) (∑' n : ℕ, max (w n) 0) := by
  have hminNorm : Summable fun n : ℕ => ‖min (w n) 0‖ := by
    apply hw.of_nonneg_of_le
    · intro n
      exact norm_nonneg _
    · intro n
      by_cases hn : w n ≤ 0
      · simpa only [min_eq_left hn] using (le_refl ‖w n‖)
      · simp only [min_eq_right (le_of_not_ge hn), norm_zero, norm_nonneg]
  have hmaxNorm : Summable fun n : ℕ => ‖max (w n) 0‖ := by
    apply hw.of_nonneg_of_le
    · intro n
      exact norm_nonneg _
    · intro n
      by_cases hn : 0 ≤ w n
      · simpa only [max_eq_left hn] using (le_refl ‖w n‖)
      · simp only [max_eq_right (le_of_not_ge hn), norm_zero, norm_nonneg]
  have hmin : Summable fun n : ℕ => min (w n) 0 := hminNorm.of_norm
  have hmax : Summable fun n : ℕ => max (w n) 0 := hmaxNorm.of_norm
  let lowerCoordinates : SampleSpace := fun n =>
    if w n < 0 then ⟨1, zero_le_one, le_rfl⟩ else ⟨0, le_rfl, zero_le_one⟩
  let upperCoordinates : SampleSpace := fun n =>
    if 0 < w n then ⟨1, zero_le_one, le_rfl⟩ else ⟨0, le_rfl, zero_le_one⟩
  have hlower : weightedUniformSeries w lowerCoordinates =
      ∑' n : ℕ, min (w n) 0 := by
    unfold weightedUniformSeries
    apply tsum_congr
    intro n
    by_cases hn : w n < 0
    · simp [lowerCoordinates, hn, min_eq_left hn.le]
    · simp [lowerCoordinates, hn, min_eq_right (le_of_not_gt hn)]
  have hupper : weightedUniformSeries w upperCoordinates =
      ∑' n : ℕ, max (w n) 0 := by
    unfold weightedUniformSeries
    apply tsum_congr
    intro n
    by_cases hn : 0 < w n
    · simp [upperCoordinates, hn, max_eq_left hn.le]
    · simp [upperCoordinates, hn, max_eq_right (le_of_not_gt hn)]
  apply Set.Subset.antisymm
  · rintro _ ⟨ω, rfl⟩
    have hterms := summable_weightedUniformSeries_terms hw ω
    constructor
    · unfold weightedUniformSeries
      apply hmin.tsum_le_tsum _ hterms
      intro n
      simp only [smul_eq_mul]
      by_cases hn : w n < 0
      · simpa only [min_eq_left hn.le, one_mul] using
          mul_le_mul_of_nonpos_right (ω n).property.2 hn.le
      · simpa only [min_eq_right (le_of_not_gt hn)] using
          mul_nonneg (ω n).property.1 (le_of_not_gt hn)
    · unfold weightedUniformSeries
      apply hterms.tsum_le_tsum _ hmax
      intro n
      simp only [smul_eq_mul]
      by_cases hn : 0 < w n
      · simpa only [max_eq_left hn.le, one_mul] using
          mul_le_mul_of_nonneg_right (ω n).property.2 hn.le
      · simpa only [max_eq_right (le_of_not_gt hn)] using
          mul_nonpos_of_nonneg_of_nonpos (ω n).property.1 (le_of_not_gt hn)
  · exact (isPreconnected_range (continuous_weightedUniformSeries hw)).Icc_subset
      ⟨lowerCoordinates, hlower⟩ ⟨upperCoordinates, hupper⟩

/-- The support of a summable real weighted-uniform law is the exact interval
between the sums of its negative and positive parts. -/
theorem weightedUniformDistribution_support_eq_Icc_min_max
    {w : ℕ → ℝ} (hw : Summable fun n => ‖w n‖) :
    (weightedUniformDistribution w).support =
      Icc (∑' n : ℕ, min (w n) 0) (∑' n : ℕ, max (w n) 0) := by
  rw [weightedUniformDistribution_support_eq_range hw,
    range_weightedUniformSeries_eq_Icc_min_max hw]

/-- The range of a summable nonnegative real weighted series is exactly its
natural closed interval. -/
theorem range_weightedUniformSeries_eq_Icc
    {w : ℕ → ℝ} (hw : Summable fun n => ‖w n‖)
    (hwnonneg : ∀ n, 0 ≤ w n) :
    Set.range (weightedUniformSeries w) =
      Icc 0 (∑' n : ℕ, w n) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨ω, rfl⟩
    exact weightedUniformSeries_mem_Icc hw hwnonneg ω
  · intro x hx
    let W : ℝ := ∑' n : ℕ, w n
    have hWnonneg : 0 ≤ W := tsum_nonneg hwnonneg
    by_cases hW : W = 0
    · have hWsum : (∑' n : ℕ, w n) = 0 := by simpa only [W] using hW
      have hx0 : x = 0 := le_antisymm (by simpa only [hWsum] using hx.2) hx.1
      subst x
      let u : Set.Icc (0 : ℝ) 1 := ⟨0, le_rfl, zero_le_one⟩
      refine ⟨fun _ => u, ?_⟩
      rw [weightedUniformSeries_constCoordinates, hWsum, smul_zero]
    · have hWpos : 0 < W := lt_of_le_of_ne hWnonneg (Ne.symm hW)
      let u : Set.Icc (0 : ℝ) 1 :=
        ⟨x / W, div_nonneg hx.1 hWpos.le, (div_le_one hWpos).2 hx.2⟩
      refine ⟨fun _ => u, ?_⟩
      rw [weightedUniformSeries_constCoordinates]
      change (x / W) * W = x
      exact div_mul_cancel₀ x hW

/-- The topological support of a summable nonnegative real weighted-uniform
law is exactly the interval from zero to the total weight. -/
theorem weightedUniformDistribution_support_eq_Icc
    {w : ℕ → ℝ} (hw : Summable fun n => ‖w n‖)
    (hwnonneg : ∀ n, 0 ≤ w n) :
    (weightedUniformDistribution w).support =
      Icc 0 (∑' n : ℕ, w n) := by
  rw [weightedUniformDistribution_support_eq_range hw,
    range_weightedUniformSeries_eq_Icc hw hwnonneg]

/-- Unit-mass nonnegative weights have topological support exactly the unit
interval. -/
theorem weightedUniformDistribution_support_eq_unitInterval
    {w : ℕ → ℝ} (hw : Summable fun n => ‖w n‖)
    (hwnonneg : ∀ n, 0 ≤ w n) (hmass : ∑' n : ℕ, w n = 1) :
    (weightedUniformDistribution w).support = Icc (0 : ℝ) 1 := by
  simpa only [hmass] using
    weightedUniformDistribution_support_eq_Icc hw hwnonneg

end

end ProbabilityRepresentation
end Fabius
