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
* ordered support bounds for nonnegative real weights.

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
