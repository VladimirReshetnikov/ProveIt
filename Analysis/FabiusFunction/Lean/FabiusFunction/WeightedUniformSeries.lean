import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Constructions.UnitInterval
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.Process.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Absolutely summable uniform-coordinate series

This file isolates the probability space of independent uniform coordinates
and the general series

`sum' n, (omega n : ℝ) • w n`

attached to an absolutely summable sequence of vectors.  The construction is
independent of the dyadic Fabius equation.  It applies to every complete
real normed space and records the reusable pointwise foundations needed by
geometric Fabius families:

* absolute summability and continuity of the coordinate series;
* splitting off the head coordinate with an arbitrary shifted weight tail;
* reflection about half of the total weight;
* the corresponding probability law, product splitting, and central symmetry;
* measure-theoretic support bounds for nonnegative real weights.

The public sample-space, shift, independence, and reflection declarations
formerly lived in `ProbabilityRepresentation`.  They retain exactly the same
names and types here, so the dyadic probability API and all of its downstream
users are unchanged.  The useful head--tail independence lemma, formerly
private, is now exposed as part of this foundational API.
-/

open Filter Set MeasureTheory ProbabilityTheory Topology
open scoped BigOperators unitInterval

namespace Fabius
namespace ProbabilityRepresentation

set_option autoImplicit false
noncomputable section

/-! ## Independent uniform coordinates -/

/-- The sample space of countably many points of the closed unit interval. -/
abbrev SampleSpace := ℕ → Set.Icc (0 : ℝ) 1

/-- Product Lebesgue probability measure on `[0,1]^ℕ`. -/
noncomputable def uniformProduct : Measure SampleSpace :=
  Measure.infinitePi (fun _ : ℕ => (volume : Measure (Set.Icc (0 : ℝ) 1)))

/-- The product of the uniform coordinate laws is a probability measure. -/
instance : IsProbabilityMeasure uniformProduct := by
  unfold uniformProduct
  infer_instance

/-- The coordinate projections are mutually independent uniform random
variables. -/
lemma independent_uniform_coordinates :
    iIndepFun (fun n : ℕ => fun ω : SampleSpace => ω n) uniformProduct := by
  unfold uniformProduct
  exact iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id)

/-- Each coordinate projection has the uniform probability law on `[0,1]`. -/
lemma coordinate_has_uniform_law (n : ℕ) :
    uniformProduct.map (fun ω : SampleSpace => ω n) =
      (volume : Measure (Set.Icc (0 : ℝ) 1)) := by
  unfold uniformProduct
  rw [Measure.infinitePi_map_eval]

/-- Delete the first coordinate. -/
def tail (ω : SampleSpace) : SampleSpace := fun n => ω (Nat.succ n)

/-- The shift `tail` is measurable, being a reindexing of the coordinate
projections. -/
lemma measurable_tail : Measurable tail := by
  exact measurable_pi_lambda _ fun n => measurable_pi_apply (Nat.succ n)

/-- The product measure is invariant under deleting the first coordinate. -/
lemma uniformProduct_map_tail : uniformProduct.map tail = uniformProduct := by
  change (Measure.infinitePi fun _ : ℕ => (volume : Measure (Set.Icc (0 : ℝ) 1))).map
      (fun ω n => ω (Nat.succ n)) =
    Measure.infinitePi fun _ : ℕ => (volume : Measure (Set.Icc (0 : ℝ) 1))
  rw [Measure.map_infinitePi_infinitePi_of_inj Nat.succ_injective]

/-- The head coordinate is independent of the complete tail process. -/
lemma independent_head_tail :
    IndepFun (fun ω : SampleSpace => ω 0) tail uniformProduct := by
  have hi := independent_uniform_coordinates
  apply IndepFun.indepFun_process (measurable_pi_apply 0)
    (fun n => measurable_pi_apply (Nat.succ n))
  intro s
  let t : Finset ℕ := s.image Nat.succ
  have hdisj : Disjoint ({0} : Finset ℕ) t := by
    rw [Finset.disjoint_left]
    intro n hn0 hnt
    simp only [Finset.mem_singleton] at hn0
    subst n
    rcases Finset.mem_image.mp hnt with ⟨n, _hn, hn⟩
    omega
  have hfin := iIndepFun.indepFun_finset ({0} : Finset ℕ) t hdisj hi
    (fun n => measurable_pi_apply n)
  let takeHead : ((i : ({0} : Finset ℕ)) → Set.Icc (0 : ℝ) 1) →
      Set.Icc (0 : ℝ) 1 := fun z => z ⟨0, by simp⟩
  let reindex : ((i : t) → Set.Icc (0 : ℝ) 1) →
      ((i : s) → Set.Icc (0 : ℝ) 1) :=
    fun z i => z ⟨Nat.succ i, Finset.mem_image.mpr ⟨i, i.property, rfl⟩⟩
  have hcomp := hfin.comp (by fun_prop : Measurable takeHead)
    (by fun_prop : Measurable reindex)
  simpa only [Function.comp_def, takeHead, reindex, t] using hcomp

/-- The head and tail are jointly distributed as the product of one uniform
coordinate with an independent copy of the full coordinate process. -/
lemma uniformProduct_map_head_tail :
    uniformProduct.map (fun ω : SampleSpace => (ω 0, tail ω)) =
      (volume : Measure (Set.Icc (0 : ℝ) 1)).prod uniformProduct := by
  have h := independent_head_tail.map_prod_eq_prod_map_map
    (measurable_pi_apply 0).aemeasurable measurable_tail.aemeasurable
  rw [uniformProduct_map_tail] at h
  have hhead := coordinate_has_uniform_law 0
  rwa [hhead] at h

/-- A measurable statistic of the tail is jointly distributed with the head
as one uniform coordinate times the statistic's law on a fresh copy of the
full coordinate process.

This formulation is independent of weighted series: it is the reusable
head--tail product-map principle behind every first-coordinate decomposition
below. -/
theorem uniformProduct_map_head_tail_comp
    {E : Type*} [MeasurableSpace E] {g : SampleSpace → E}
    (hg : Measurable g) :
    uniformProduct.map (fun ω : SampleSpace => (ω 0, g (tail ω))) =
      (volume : Measure (Set.Icc (0 : ℝ) 1)).prod (uniformProduct.map g) := by
  have hind := independent_head_tail.comp measurable_id hg
  have hjoint := hind.map_prod_eq_prod_map_map
    (measurable_pi_apply 0).aemeasurable
    (hg.comp measurable_tail).aemeasurable
  have hhead := coordinate_has_uniform_law 0
  have htail : uniformProduct.map (g ∘ tail) = uniformProduct.map g := by
    rw [← Measure.map_map hg measurable_tail, uniformProduct_map_tail]
  rwa [hhead, htail] at hjoint

/-- Reflect every coordinate in the midpoint of the unit interval. -/
def reflectCoordinates (ω : SampleSpace) : SampleSpace :=
  fun n => unitInterval.symm (ω n)

/-- Coordinatewise reflection is measurable on the sample space. -/
lemma measurable_reflectCoordinates : Measurable reflectCoordinates := by
  exact measurable_pi_lambda _ fun n =>
    unitInterval.measurable_symm.comp (measurable_pi_apply n)

/-- Lebesgue measure on `[0,1]` and hence its countable product are invariant
under coordinatewise reflection. -/
lemma uniformProduct_map_reflectCoordinates :
    uniformProduct.map reflectCoordinates = uniformProduct := by
  change (Measure.infinitePi fun _ : ℕ => (volume : Measure (Set.Icc (0 : ℝ) 1))).map
      (fun ω n => unitInterval.symm (ω n)) =
    Measure.infinitePi fun _ : ℕ => (volume : Measure (Set.Icc (0 : ℝ) 1))
  rw [Measure.infinitePi_map_pi
    (fun _ : ℕ => (volume : Measure (Set.Icc (0 : ℝ) 1)))
    (fun _ => unitInterval.measurable_symm)]
  congr 1
  funext n
  exact unitInterval.measurePreserving_symm.map_eq

/-! ## Vector-valued weighted series -/

/-- The uniform-coordinate series with vector weights `w`.

The definition is total, as every `tsum` in Lean is.  The useful continuity,
splitting, and reflection theorems assume absolute summability of `w`. -/
noncomputable def weightedUniformSeries
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (w : ℕ → E) (ω : SampleSpace) : E :=
  ∑' n : ℕ, (ω n : ℝ) • w n

private lemma norm_coordinate_smul_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : Set.Icc (0 : ℝ) 1) (x : E) :
    ‖(u : ℝ) • x‖ ≤ ‖x‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg u.property.1]
  calc
    (u : ℝ) * ‖x‖ ≤ 1 * ‖x‖ :=
      mul_le_mul_of_nonneg_right u.property.2 (norm_nonneg x)
    _ = ‖x‖ := one_mul _

/-- Absolute summability of the weights uniformly controls every coordinate
series. -/
theorem summable_weightedUniformSeries_terms
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {w : ℕ → E} (hw : Summable fun n => ‖w n‖) (ω : SampleSpace) :
    Summable fun n : ℕ => (ω n : ℝ) • w n := by
  exact hw.of_norm_bounded fun n => norm_coordinate_smul_le (ω n) (w n)

/-- An absolutely summable vector-weight sequence defines a continuous map
on the full product of unit intervals. -/
theorem continuous_weightedUniformSeries
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {w : ℕ → E} (hw : Summable fun n => ‖w n‖) :
    Continuous (weightedUniformSeries w) := by
  unfold weightedUniformSeries
  apply continuous_tsum
  · intro n
    fun_prop
  · exact hw
  · intro n ω
    exact norm_coordinate_smul_le (ω n) (w n)

/-- The weighted series is measurable whenever its complete normed codomain
carries the Borel measurable structure. -/
theorem measurable_weightedUniformSeries
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    {w : ℕ → E} (hw : Summable fun n => ‖w n‖) :
    Measurable (weightedUniformSeries w) :=
  (continuous_weightedUniformSeries hw).measurable

/-! ## Laws of weighted series -/

/-- The distribution of an arbitrary weighted uniform-coordinate series.

As with `Measure.map` itself, this definition is total even when the series
map is not measurable; in that case Mathlib's totalized map is the zero
measure.  Absolute summability and completeness enter the theorems below,
where they provide measurability and hence a genuine probability law. -/
noncomputable def weightedUniformDistribution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    (w : ℕ → E) : Measure E :=
  uniformProduct.map (weightedUniformSeries w)

/-- The law of an absolutely summable weighted series is a probability
measure.  This is stated as a theorem, rather than a global instance, because
measurability genuinely depends on the summability hypothesis. -/
theorem isProbabilityMeasure_weightedUniformDistribution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    {w : ℕ → E} (hw : Summable fun n => ‖w n‖) :
    IsProbabilityMeasure (weightedUniformDistribution w) :=
  Measure.isProbabilityMeasure_map
    (measurable_weightedUniformSeries hw).aemeasurable

/-- The head coordinate and the weighted series formed from the shifted
weights and tail coordinates have the product of their marginal laws. -/
theorem uniformProduct_map_head_tailWeightedUniformSeries
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    {v : ℕ → E} (hv : Summable fun n => ‖v n‖) :
    uniformProduct.map
        (fun ω : SampleSpace =>
          (ω 0, weightedUniformSeries v (tail ω))) =
      (volume : Measure (Set.Icc (0 : ℝ) 1)).prod
        (weightedUniformDistribution v) := by
  exact uniformProduct_map_head_tail_comp
    (measurable_weightedUniformSeries hv)

/-- Splitting off the first coordinate shifts an arbitrary weight sequence.
No geometric relation between consecutive weights is assumed. -/
theorem weightedUniformSeries_split
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {w : ℕ → E} (hw : Summable fun n => ‖w n‖) (ω : SampleSpace) :
    weightedUniformSeries w ω =
      (ω 0 : ℝ) • w 0 +
        weightedUniformSeries (fun n => w (Nat.succ n)) (tail ω) := by
  simpa only [weightedUniformSeries, tail] using
    (summable_weightedUniformSeries_terms hw ω).tsum_eq_zero_add

/-- Reflection replaces every coordinate `u` by `1-u`, so the reflected
series is the total vector weight minus the original series. -/
theorem weightedUniformSeries_reflect
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {w : ℕ → E} (hw : Summable fun n => ‖w n‖) (ω : SampleSpace) :
    weightedUniformSeries w (reflectCoordinates ω) =
      (∑' n : ℕ, w n) - weightedUniformSeries w ω := by
  rw [weightedUniformSeries, weightedUniformSeries]
  have hterm (n : ℕ) :
      ((reflectCoordinates ω n : Set.Icc (0 : ℝ) 1) : ℝ) • w n =
        w n - (ω n : ℝ) • w n := by
    simp only [reflectCoordinates, unitInterval.symm, Subtype.coe_mk]
    rw [sub_smul, one_smul]
  simp_rw [hterm]
  rw [(hw.of_norm).tsum_sub (summable_weightedUniformSeries_terms hw ω)]

/-- The law of a weighted series is obtained by adding the uniformly scaled
head weight to an independent copy of the shifted-tail series.  No geometric
relation between consecutive weights is required. -/
theorem weightedUniformDistribution_split
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    {w : ℕ → E} (hw : Summable fun n => ‖w n‖) :
    weightedUniformDistribution w =
      ((volume : Measure (Set.Icc (0 : ℝ) 1)).prod
        (weightedUniformDistribution (fun n => w (Nat.succ n)))).map
          (fun p => (p.1 : ℝ) • w 0 + p.2) := by
  have hwtail : Summable fun n => ‖w (Nat.succ n)‖ := by
    simpa only [Nat.succ_eq_add_one] using
      (summable_nat_add_iff (f := fun n => ‖w n‖) 1).mpr hw
  rw [← uniformProduct_map_head_tailWeightedUniformSeries hwtail]
  rw [weightedUniformDistribution]
  have hf : Measurable (fun ω : SampleSpace =>
      (ω 0, weightedUniformSeries (fun n => w (Nat.succ n)) (tail ω))) :=
    (measurable_pi_apply 0).prodMk
      ((measurable_weightedUniformSeries hwtail).comp measurable_tail)
  have hg : Measurable
      (fun p : Set.Icc (0 : ℝ) 1 × E => (p.1 : ℝ) • w 0 + p.2) :=
    (((continuous_subtype_val.comp continuous_fst).smul continuous_const).add
      continuous_snd).measurable
  rw [Measure.map_map
    (μ := uniformProduct)
    (f := fun ω : SampleSpace =>
      (ω 0, weightedUniformSeries (fun n => w (Nat.succ n)) (tail ω)))
    (g := fun p : Set.Icc (0 : ℝ) 1 × E => (p.1 : ℝ) • w 0 + p.2)
    hg hf]
  apply Measure.map_congr
  filter_upwards with ω
  exact weightedUniformSeries_split hw ω

/-- The law of an absolutely summable vector-weighted series is centrally
symmetric: reflection through half the total weight preserves the law. -/
theorem weightedUniformDistribution_reflection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    {w : ℕ → E} (hw : Summable fun n => ‖w n‖) :
    (weightedUniformDistribution w).map
        (fun x => (∑' n : ℕ, w n) - x) =
      weightedUniformDistribution w := by
  rw [weightedUniformDistribution,
    Measure.map_map (by fun_prop : Measurable fun x : E => (∑' n : ℕ, w n) - x)
      (measurable_weightedUniformSeries hw)]
  calc
    uniformProduct.map
        ((fun x : E => (∑' n : ℕ, w n) - x) ∘ weightedUniformSeries w) =
        uniformProduct.map (weightedUniformSeries w ∘ reflectCoordinates) := by
      apply Measure.map_congr
      filter_upwards with ω
      exact (weightedUniformSeries_reflect hw ω).symm
    _ = (uniformProduct.map reflectCoordinates).map
        (weightedUniformSeries w) := by
      rw [Measure.map_map (measurable_weightedUniformSeries hw)
        measurable_reflectCoordinates]
    _ = uniformProduct.map (weightedUniformSeries w) := by
      rw [uniformProduct_map_reflectCoordinates]

/-- The norm of a weighted coordinate series is at most the total norm of
its weights. -/
theorem norm_weightedUniformSeries_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {w : ℕ → E} (hw : Summable fun n => ‖w n‖) (ω : SampleSpace) :
    ‖weightedUniformSeries w ω‖ ≤ ∑' n : ℕ, ‖w n‖ := by
  unfold weightedUniformSeries
  exact tsum_of_norm_bounded hw.hasSum fun n =>
    norm_coordinate_smul_le (ω n) (w n)

/-! ## Ordered real weights -/

/-- Nonnegative real weights give a pointwise nonnegative series. -/
theorem weightedUniformSeries_nonneg
    {w : ℕ → ℝ} (hwnonneg : ∀ n, 0 ≤ w n) (ω : SampleSpace) :
    0 ≤ weightedUniformSeries w ω := by
  unfold weightedUniformSeries
  apply tsum_nonneg
  intro n
  simpa only [smul_eq_mul] using
    mul_nonneg (ω n).property.1 (hwnonneg n)

/-- A nonnegative weighted series is bounded above by the sum of its
weights. -/
theorem weightedUniformSeries_le_tsum
    {w : ℕ → ℝ} (hw : Summable fun n => ‖w n‖)
    (hwnonneg : ∀ n, 0 ≤ w n) (ω : SampleSpace) :
    weightedUniformSeries w ω ≤ ∑' n : ℕ, w n := by
  unfold weightedUniformSeries
  apply (summable_weightedUniformSeries_terms hw ω).tsum_le_tsum _ (hw.of_norm)
  intro n
  simp only [smul_eq_mul]
  calc
    (ω n : ℝ) * w n ≤ 1 * w n :=
      mul_le_mul_of_nonneg_right (ω n).property.2 (hwnonneg n)
    _ = w n := one_mul _

/-- Pointwise support interval for a series with nonnegative real weights. -/
theorem weightedUniformSeries_mem_Icc
    {w : ℕ → ℝ} (hw : Summable fun n => ‖w n‖)
    (hwnonneg : ∀ n, 0 ≤ w n) (ω : SampleSpace) :
    weightedUniformSeries w ω ∈ Icc 0 (∑' n : ℕ, w n) :=
  ⟨weightedUniformSeries_nonneg hwnonneg ω,
    weightedUniformSeries_le_tsum hw hwnonneg ω⟩

/-- The law of a nonnegative real weighted series is carried by its natural
pointwise interval from zero to the total weight. -/
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

/-- A nonnegative real weighted series assigns no mass outside its natural
support interval. -/
@[simp]
theorem weightedUniformDistribution_compl_Icc
    {w : ℕ → ℝ} (hw : Summable fun n => ‖w n‖)
    (hwnonneg : ∀ n, 0 ≤ w n) :
    weightedUniformDistribution w ((Icc 0 (∑' n : ℕ, w n))ᶜ) = 0 := by
  letI : IsProbabilityMeasure (weightedUniformDistribution w) :=
    isProbabilityMeasure_weightedUniformDistribution hw
  rw [measure_compl measurableSet_Icc (by simp),
    weightedUniformDistribution_Icc hw hwnonneg, measure_univ, tsub_self]

/-- Unit-mass nonnegative weights produce a point of the unit interval. -/
theorem weightedUniformSeries_mem_unitInterval
    {w : ℕ → ℝ} (hw : Summable fun n => ‖w n‖)
    (hwnonneg : ∀ n, 0 ≤ w n) (hmass : ∑' n : ℕ, w n = 1)
    (ω : SampleSpace) :
    weightedUniformSeries w ω ∈ Set.Icc (0 : ℝ) 1 := by
  simpa only [hmass] using weightedUniformSeries_mem_Icc hw hwnonneg ω

end

end ProbabilityRepresentation
end Fabius
