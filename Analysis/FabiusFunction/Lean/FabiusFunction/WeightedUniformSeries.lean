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
* a generic head--tail recursion principle for pushforward laws;
* naturality under continuous linear maps;
* operator and scalar geometric self-similarity;
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

/-- An almost-everywhere head--tail recursion induces the corresponding
product-law recursion.

This statement is independent of linear structure and weighted series.  It
packages the common measure-theoretic argument behind affine fixed-point laws:
the head is one fresh uniform coordinate, while the tail statistic has the
same law on a fresh copy and is independent of that head. -/
theorem uniformProduct_map_of_ae_head_tail_recursion
    {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    {f : SampleSpace → F} {g : SampleSpace → E}
    (hg : Measurable g) (combine : Set.Icc (0 : ℝ) 1 × E → F)
    (hcombine : Measurable combine)
    (hrec : f =ᵐ[uniformProduct] fun ω => combine (ω 0, g (tail ω))) :
    uniformProduct.map f =
      ((volume : Measure (Set.Icc (0 : ℝ) 1)).prod
        (uniformProduct.map g)).map combine := by
  rw [← uniformProduct_map_head_tail_comp hg]
  rw [Measure.map_map
    (f := fun ω : SampleSpace => (ω 0, g (tail ω)))
    (g := combine) hcombine
    ((measurable_pi_apply 0).prodMk (hg.comp measurable_tail))]
  exact Measure.map_congr hrec

/-- A pointwise measurable head--tail recursion induces the corresponding
product-law recursion.  This convenient form specializes
`uniformProduct_map_of_ae_head_tail_recursion`. -/
theorem uniformProduct_map_of_head_tail_recursion
    {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    {f : SampleSpace → F} {g : SampleSpace → E}
    (hg : Measurable g) (combine : Set.Icc (0 : ℝ) 1 × E → F)
    (hcombine : Measurable combine)
    (hrec : ∀ ω, f ω = combine (ω 0, g (tail ω))) :
    uniformProduct.map f =
      ((volume : Measure (Set.Icc (0 : ℝ) 1)).prod
        (uniformProduct.map g)).map combine :=
  uniformProduct_map_of_ae_head_tail_recursion hg combine hcombine
    (ae_of_all _ hrec)

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

/-- Scaling every weight scales the corresponding uniform-coordinate
series.  The identity is total and does not require a summability
hypothesis. -/
theorem weightedUniformSeries_smul_weights
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (w : ℕ → E) (ω : SampleSpace) :
    weightedUniformSeries (fun n => a • w n) ω =
      a • weightedUniformSeries w ω := by
  unfold weightedUniformSeries
  rw [← tsum_const_smul'' a]
  apply tsum_congr
  intro n
  rw [smul_smul, smul_smul, mul_comm]

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

/-- Continuous linear maps commute with absolutely summable uniform-coordinate
series.  Completeness is needed only in the source space, where it turns the
norm-summable weight majorant into convergence of the original series; the
target need not be complete. -/
theorem weightedUniformSeries_map
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) {w : ℕ → E} (hw : Summable fun n => ‖w n‖)
    (ω : SampleSpace) :
    L (weightedUniformSeries w ω) =
      weightedUniformSeries (fun n => L (w n)) ω := by
  rw [weightedUniformSeries, weightedUniformSeries,
    L.map_tsum (summable_weightedUniformSeries_terms hw ω)]
  apply tsum_congr
  intro n
  exact L.map_smul (ω n : ℝ) (w n)

/-- Scalar multiplication commutes with a uniform-coordinate series without
any summability or completeness hypothesis.  This uses the total infinite-sum
identity for scalar multiplication over a division ring, so it remains valid
even when the underlying series is not summable. -/
theorem weightedUniformSeries_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c : ℝ) (w : ℕ → E) (ω : SampleSpace) :
    weightedUniformSeries (fun n => c • w n) ω =
      c • weightedUniformSeries w ω := by
  unfold weightedUniformSeries
  simpa only [smul_smul, mul_comm] using
    (tsum_const_smul'' (f := fun n => (ω n : ℝ) • w n) c)

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

/-- Pushforward of a weighted-uniform law by a continuous linear map is the
law obtained by mapping every weight.  As for the series-level theorem, the
target normed space need not be complete. -/
theorem weightedUniformDistribution_map
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (L : E →L[ℝ] F) {w : ℕ → E} (hw : Summable fun n => ‖w n‖) :
    (weightedUniformDistribution w).map L =
      weightedUniformDistribution (fun n => L (w n)) := by
  rw [weightedUniformDistribution,
    Measure.map_map L.continuous.measurable
      (measurable_weightedUniformSeries hw)]
  exact Measure.map_congr
    (ae_of_all _ (weightedUniformSeries_map L hw))

/-- Scalar pushforward is the law obtained by multiplying every weight by the
same scalar.  Unlike the pointwise theorem, this law-level statement records
summability so that both totalized measure maps are genuine pushforwards. -/
theorem weightedUniformDistribution_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (c : ℝ) {w : ℕ → E} (hw : Summable fun n => ‖w n‖) :
    (weightedUniformDistribution w).map (fun x => c • x) =
      weightedUniformDistribution (fun n => c • w n) := by
  rw [weightedUniformDistribution, weightedUniformDistribution,
    Measure.map_map (by fun_prop : Measurable fun x : E => c • x)
      (measurable_weightedUniformSeries hw)]
  apply Measure.map_congr
  filter_upwards with ω
  exact (weightedUniformSeries_smul c w ω).symm

/-- When the shifted weights are the image under one fixed operator, pushing
the parent law through that operator is exactly the shifted-tail law. -/
theorem weightedUniformDistribution_map_eq_shift
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (A : E →L[ℝ] E) {w : ℕ → E} (hw : Summable fun n => ‖w n‖)
    (hshift : ∀ n, w (Nat.succ n) = A (w n)) :
    (weightedUniformDistribution w).map A =
      weightedUniformDistribution (fun n => w (Nat.succ n)) := by
  rw [weightedUniformDistribution_map A hw]
  congr 1
  funext n
  exact (hshift n).symm

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

/-- The head coordinate and the weighted series formed from any independently chosen
tail-weight sequence have the product of their marginal laws. -/
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
  exact uniformProduct_map_of_head_tail_recursion
    (measurable_weightedUniformSeries hwtail)
    (fun p : Set.Icc (0 : ℝ) 1 × E => (p.1 : ℝ) • w 0 + p.2)
    ((((continuous_subtype_val.comp continuous_fst).smul continuous_const).add
      continuous_snd).measurable)
    (weightedUniformSeries_split hw)

/-- If shifting the weights applies one fixed continuous linear operator, then
splitting off the first coordinate gives an operator-affine pointwise
recursion. -/
theorem weightedUniformSeries_split_of_shift_eq_map
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A : E →L[ℝ] E) {w : ℕ → E} (hw : Summable fun n => ‖w n‖)
    (hshift : ∀ n, w (Nat.succ n) = A (w n)) (ω : SampleSpace) :
    weightedUniformSeries w ω =
      (ω 0 : ℝ) • w 0 + A (weightedUniformSeries w (tail ω)) := by
  have hwfun : (fun n => w (Nat.succ n)) = fun n => A (w n) :=
    funext hshift
  rw [weightedUniformSeries_split hw, hwfun,
    ← weightedUniformSeries_map A hw]

/-- An operator-geometric weight recursion produces the exact affine
fixed-point law driven by one fresh uniform coordinate. -/
theorem weightedUniformDistribution_split_of_shift_eq_map
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (A : E →L[ℝ] E) {w : ℕ → E} (hw : Summable fun n => ‖w n‖)
    (hshift : ∀ n, w (Nat.succ n) = A (w n)) :
    weightedUniformDistribution w =
      ((volume : Measure (Set.Icc (0 : ℝ) 1)).prod
        (weightedUniformDistribution w)).map
          (fun p => (p.1 : ℝ) • w 0 + A p.2) := by
  exact uniformProduct_map_of_head_tail_recursion
    (measurable_weightedUniformSeries hw)
    (fun p : Set.Icc (0 : ℝ) 1 × E => (p.1 : ℝ) • w 0 + A p.2)
    ((((continuous_subtype_val.comp continuous_fst).smul continuous_const).add
      (A.continuous.comp continuous_snd)).measurable)
    (weightedUniformSeries_split_of_shift_eq_map A hw hshift)

/-- Scalar-geometric weights satisfy the familiar affine pointwise recursion.
No sign or size condition on the scalar is required beyond the explicit
summability hypothesis on the weights. -/
theorem weightedUniformSeries_geometric_split
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (c : ℝ) {w : ℕ → E} (hw : Summable fun n => ‖w n‖)
    (hshift : ∀ n, w (Nat.succ n) = c • w n) (ω : SampleSpace) :
    weightedUniformSeries w ω =
      (ω 0 : ℝ) • w 0 + c • weightedUniformSeries w (tail ω) := by
  simpa using weightedUniformSeries_split_of_shift_eq_map
    (c • ContinuousLinearMap.id ℝ E) hw hshift ω

/-- Scalar-geometric weights satisfy the exact affine fixed-point law.  The
only analytic premise is norm summability of the displayed weight sequence;
in particular no positivity or contraction hypothesis is built into the
theorem. -/
theorem weightedUniformDistribution_geometric_split
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (c : ℝ) {w : ℕ → E} (hw : Summable fun n => ‖w n‖)
    (hshift : ∀ n, w (Nat.succ n) = c • w n) :
    weightedUniformDistribution w =
      ((volume : Measure (Set.Icc (0 : ℝ) 1)).prod
        (weightedUniformDistribution w)).map
          (fun p => (p.1 : ℝ) • w 0 + c • p.2) := by
  simpa using weightedUniformDistribution_split_of_shift_eq_map
    (c • ContinuousLinearMap.id ℝ E) hw hshift

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
