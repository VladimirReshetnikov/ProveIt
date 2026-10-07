/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Compat.Measurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod
import OAI.Combinatorics.Progressions.Geometry.SupportedFiniteComparison
import OAI.Combinatorics.Progressions.Lattices.PrincipalResidueMixture
import OAI.Combinatorics.Progressions.Probability.RetainedWeightedDensityTest
import OAI.Combinatorics.Progressions.Probability.ScalarCubeHistogramMeasure

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem finiteSource_comparison_on_set {Ω X : Type*} [Fintype Ω] [PseudoMetricSpace X]
    [MeasurableSpace X] (p : FiniteProbabilityWeights Ω) (F : Ω → X) (μ : Measure X)
    (S : Set X) (hF : ∀ x, F x ∈ S) (hμ : ∀ᵐ x ∂μ, x ∈ S)
    {K : ℝ≥0} {B ε : ℝ} (hB : 0 ≤ B)
    (hglobal : ∀ g : X → ℝ, LipschitzWith K g → (∀ x, ‖g x‖ ≤ B) →
      |p.mean (g ∘ F) - ∫ x, g x ∂μ| ≤ ε)
    (φ : X → ℝ) (hφ : LipschitzOnWith K φ S) (hb : ∀ x ∈ S, ‖φ x‖ ≤ B) :
    |p.mean (φ ∘ F) - ∫ x, φ x ∂μ| ≤ ε := by
  obtain ⟨g,hg,heq,hgb⟩ := exists_real_lipschitz_extension_interval φ S K hφ (-B) B
    (neg_le_self hB) (fun x hx => abs_le.mp (by simpa only [Real.norm_eq_abs] using hb x hx))
  have hmean : p.mean (φ ∘ F) = p.mean (g ∘ F) := by
    congr 1
    funext x
    exact heq (hF x)
  have hint : (∫ x, φ x ∂μ) = ∫ x, g x ∂μ :=
    integral_congr_ae (hμ.mono (fun x hx => heq hx))
  rw [hmean, hint]
  exact hglobal g hg (fun x => by simpa only [Real.norm_eq_abs] using abs_le.mpr (hgb x))

theorem finiteSource_comparison_on_support {Ω X : Type*} [Fintype Ω] [PseudoMetricSpace X]
    [MeasurableSpace X] (p : FiniteProbabilityWeights Ω) (F : Ω → X) (μ : Measure X)
    (S : Set X) (hF : ∀ x, 0 < p.weight x → F x ∈ S) (hμ : ∀ᵐ x ∂μ, x ∈ S)
    {K : ℝ≥0} {B ε : ℝ} (hB : 0 ≤ B)
    (hglobal : ∀ g : X → ℝ, LipschitzWith K g → (∀ x, ‖g x‖ ≤ B) →
      |p.mean (g ∘ F) - ∫ x, g x ∂μ| ≤ ε)
    (φ : X → ℝ) (hφ : LipschitzOnWith K φ S) (hb : ∀ x ∈ S, ‖φ x‖ ≤ B) :
    |p.mean (φ ∘ F) - ∫ x, φ x ∂μ| ≤ ε := by
  obtain ⟨g,hg,heq,hgb⟩ := exists_real_lipschitz_extension_interval φ S K hφ (-B) B
    (neg_le_self hB) (fun x hx => abs_le.mp (by simpa only [Real.norm_eq_abs] using hb x hx))
  have hmean : p.mean (φ ∘ F) = p.mean (g ∘ F) := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : p.weight x = 0
    · simp only [hx, zero_mul]
    · rw [Function.comp_apply, Function.comp_apply, heq (hF x (lt_of_le_of_ne (p.nonneg x) (Ne.symm hx))) ]
  have hint : (∫ x, φ x ∂μ) = ∫ x, g x ∂μ :=
    integral_congr_ae (hμ.mono (fun x hx => heq hx))
  rw [hmean, hint]
  exact hglobal g hg (fun x => by simpa only [Real.norm_eq_abs] using abs_le.mpr (hgb x))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem product_density_rounding_error {J X : Type*} [Fintype J] [DecidableEq J]
    [PseudoMetricSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (μ : J → Measure X) [∀ j, SigmaFinite (μ j)] (f g : J → X → ℝ)
    (hf : ∀ j, Integrable (f j) (μ j)) (hg : ∀ j, Integrable (g j) (μ j))
    (hf0 : ∀ j x, 0 ≤ f j x) (hg0 : ∀ j x, 0 ≤ g j x)
    (hfm : ∀ j, (∫ x, f j x ∂μ j) = 1) (hgm : ∀ j, (∫ x, g j x ∂μ j) = 1)
    (R : J → X → X) (hR : ∀ j, Measurable (R j)) (δ ε : J → ℝ)
    (hδ : ∀ j, 0 ≤ δ j) (he : ∀ j, (∫ x, |f j x-g j x| ∂μ j) ≤ ε j)
    (hm : ∀ j x, dist (R j x) x ≤ δ j)
    (φ : (J → X) → ℝ) {K : ℝ≥0} {B : ℝ} (hφ : LipschitzWith K φ)
    (hB : 0 ≤ B) (hb : ∀ x, ‖φ x‖ ≤ B) :
    |(∫ x, (∏ j, f j (x j)) * φ (fun j => R j (x j)) ∂Measure.pi μ) -
      ∫ x, (∏ j, g j (x j)) * φ x ∂Measure.pi μ| ≤ B * (∑ j, ε j) + K * (∑ j, δ j) := by
  have herr := (tensor_density_l1_le_sum μ f g hf hg hf0 hg0 hfm hgm).trans
    (Finset.sum_le_sum (fun j _ => he j))
  have hmove (x : J → X) : dist (fun j => R j (x j)) x ≤ ∑ j, δ j := by
    apply (dist_pi_le_iff (Finset.sum_nonneg (fun j _ => hδ j))).mpr
    intro j
    exact (hm j (x j)).trans (Finset.single_le_sum (fun k _ => hδ k) (Finset.mem_univ j))
  have hmass : (∫ x, (∏ j, g j (x j)) ∂Measure.pi μ) = 1 := by
    rw [integral_fintype_prod_eq_prod]
    simp only [hgm, Finset.prod_const_one]
  exact density_rounding_test_error (Measure.pi μ) _ _ (Integrable.fintype_prod_dep hf)
    (Integrable.fintype_prod_dep hg) (fun x => Finset.prod_nonneg (fun j _ => hg0 j (x j)))
    hmass (fun x j => R j (x j)) (Measurable.of_eval (fun j => (hR j).comp (measurable_pi_apply j)))
    hB herr hmove φ hφ hb

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem finiteSource_product_comparison {Ω Z X : Type*} [Fintype Ω]
    [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSingletonClass X]
    (p : FiniteProbabilityWeights Ω) (F : Ω → X)
    (μ : Measure Z) (ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (φ : Z × X → ℝ) (hφ : Measurable φ) {B ε : ℝ} (hb : ∀ x, ‖φ x‖ ≤ B)
    (he : ∀ᵐ z ∂μ, |p.mean (fun x => φ (z, F x)) - ∫ x, φ (z, x) ∂ν| ≤ ε) :
    |(∫ z, p.mean (fun x => φ (z, F x)) ∂μ) - ∫ x, φ x ∂μ.prod ν| ≤ ε := by
  let : IsProbabilityMeasure (p.imageMeasure F) := FiniteProbabilityWeights.imageMeasure_probability p F
  have hf : Integrable φ (μ.prod (p.imageMeasure F)) :=
    (integrable_const B).mono' hφ.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  have hg : Integrable φ (μ.prod ν) :=
    (integrable_const B).mono' hφ.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  have hfi : Integrable (fun z => p.mean (fun x => φ (z, F x))) μ := by
    simpa only [FiniteProbabilityWeights.imageMeasure_integral] using hf.integral_prod_left
  rw [integral_prod _ hg, ← integral_sub hfi hg.integral_prod_left]
  have hbound : ∀ᵐ z ∂μ, ‖p.mean (fun x => φ (z, F x)) - ∫ x, φ (z, x) ∂ν‖ ≤ ε := by
    simpa only [Real.norm_eq_abs] using he
  have ht := norm_integral_le_of_norm_le (integrable_const ε (μ := μ)) hbound
  simpa only [Real.norm_eq_abs, integral_const, probReal_univ, one_smul] using ht

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem scalarCubeProductDensity_measure (J I : Type*) [Fintype J] [Fintype I] [DecidableEq I] :
    scalarCubeProductMeasure J I =
      realDensityMeasure volume (tensorCutoffWeight (fun _ : J => scalarCubeProbabilityDensity I)) := by
  rw [scalarCubeProductMeasure, ← scalarCubeProbabilityDensity_measure I]
  exact realDensityMeasure_pi (fun _ => volume) _
    (fun _ => (scalarCubeProbabilityDensity_spec I).1)
    (fun _ => (scalarCubeProbabilityDensity_spec I).2.1)

theorem scalarCubeResidue_pi_imageMeasure {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (L M : J → ℕ) (hL : ∀ j, 0 < L j) (m : J → Option I → ℕ)
    (r : ∀ j i, ZMod (m j i)) (hm : ∀ j i, 0 < m j i) (hmM : ∀ j i, m j i ≤ M j)
    (hsize : ∀ j, (Fintype.card I + 1)*M j ≤ L j)
    (hpos : ∀ j, 0 < ∫ x, scalarCubeGridHistogram I (scalarResidueGridOffset (m j) (r j))
      (scalarResidueGridScale (L j) (m j)) x) :
    (FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights I (L j) (M j) (hL j)
      (m j) (r j) (hm j) (hmM j) (hsize j))).imageMeasure (fun z j i => (z j i : ℝ) / L j) =
      (realDensityMeasure volume (tensorCutoffWeight (fun j =>
        scalarCubeGridDensity I (scalarResidueGridOffset (m j) (r j)) (scalarResidueGridScale (L j) (m j))))).map
      (fun x j => rectangularLatticeSample (scalarResidueGridOffset (m j) (r j))
        (scalarResidueGridScale (L j) (m j)) (x j)) := by
  let f := fun j => scalarCubeGridDensity I (scalarResidueGridOffset (m j) (r j))
    (scalarResidueGridScale (L j) (m j))
  have hs (j : J) := scalarCubeGridDensity_spec I _ _ (scalarResidueGridScale_pos (hL j) (m j) (hm j)) (hpos j)
  let : ∀ j, IsFiniteMeasure (realDensityMeasure volume (f j)) :=
    fun j => realDensityMeasure_finite volume (f j) (hs j).1 (hs j).2.1
  rw [← FiniteProbabilityWeights.imageMeasure_pi
    (fun j => scalarCubeResidueWeights I (L j) (M j) (hL j) (m j) (r j) (hm j) (hmM j) (hsize j))
    (fun j z i => (z i : ℝ) / L j)]
  simp_rw [scalarCubeResidue_imageMeasure I _ _ _ _ _ _ _ _ (hpos _)]
  rw [← Measure.pi_map_pi (fun j => (rectangularLatticeSample_measurable
    (scalarResidueGridOffset (m j) (r j)) (scalarResidueGridScale (L j) (m j))).aemeasurable)]
  rw [realDensityMeasure_pi (fun _ => volume) f (fun j => (hs j).1) (fun j => (hs j).2.1)]
  rfl

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem scalarCubeResidueWeights_pi_riemann {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (L M : J → ℕ) (hL : ∀ j, 0 < L j) (m : J → Option I → ℕ)
    (r : ∀ j i, ZMod (m j i)) (hm : ∀ j i, 0 < m j i) (hmM : ∀ j i, m j i ≤ M j)
    (hsize : ∀ j, (Fintype.card I + 1)*M j ≤ L j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant I * ((M j : ℝ)/L j) <
      volume.real (scalarCubeDomain I))
    (φ : (J → Option I → ℝ) → ℝ) {K : ℝ≥0} {B : ℝ}
    (hφ : LipschitzWith K φ) (hB : 0 ≤ B) (hb : ∀ x, ‖φ x‖ ≤ B) :
    |(FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights I (L j) (M j) (hL j)
      (m j) (r j) (hm j) (hmM j) (hsize j))).mean
        (fun z => φ (fun j i => (z j i : ℝ) / L j)) -
      ∫ x, φ x ∂scalarCubeProductMeasure J I| ≤
      (2 * B * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I) + K) *
        ∑ j, (M j : ℝ)/L j := by
  let a := fun j => scalarResidueGridOffset (m j) (r j)
  let S := fun j => scalarResidueGridScale (L j) (m j)
  let δ := fun j => (M j : ℝ)/L j
  let f := fun j => scalarCubeGridDensity I (a j) (S j)
  let g := fun _ : J => scalarCubeProbabilityDensity I
  have hS (j) : ∀ i, 0 < S j i := scalarResidueGridScale_pos (hL j) (m j) (hm j)
  have hδ (j) : 0 ≤ δ j := by dsimp only [δ]; positivity
  have hδ1 (j) : δ j ≤ 1 := by
    have hML : M j ≤ L j := by nlinarith [hsize j]
    exact (div_le_one (by exact_mod_cast hL j)).mpr (by exact_mod_cast hML)
  have hmesh (j) (i : Option I) : 1 / S j i ≤ δ j := by
    dsimp only [S, δ, scalarResidueGridScale]
    rw [one_div_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hmM j i) (by positivity)
  have hpos (j) : 0 < ∫ x, scalarCubeGridHistogram I (a j) (S j) x :=
    scalarCubeGridHistogram_mass_pos I _ _ (hS j) (hδ j) (hδ1 j) (hmesh j) (hsmall j)
  have hf (j) := scalarCubeGridDensity_spec I (a j) (S j) (hS j) (hpos j)
  have hg := scalarCubeProbabilityDensity_spec I
  have hfm : Measurable (tensorCutoffWeight f) := by
    apply Finset.measurable_prod
    intro j _
    exact (scalarCubeGridDensity_measurable I (a j) (S j) (hS j)).comp (measurable_pi_apply j)
  have hgm : Measurable (tensorCutoffWeight g) := by
    apply Finset.measurable_prod
    intro j _
    exact (scalarCubeProbabilityDensity_measurable I).comp (measurable_pi_apply j)
  have hR : Measurable (fun (x : J → Option I → ℝ) j => rectangularLatticeSample (a j) (S j) (x j)) :=
    Measurable.of_eval (fun j => (rectangularLatticeSample_measurable _ _).comp (measurable_pi_apply j))
  rw [← FiniteProbabilityWeights.imageMeasure_integral _ _ φ,
    scalarCubeResidue_pi_imageMeasure L M hL m r hm hmM hsize hpos,
    integral_map hR.aemeasurable hφ.continuous.measurable.aestronglyMeasurable,
    realDensityMeasure_integral _ _ hfm (tensorCutoffWeight_nonneg f (fun j => (hf j).2.1)),
    scalarCubeProductDensity_measure,
    realDensityMeasure_integral _ _ hgm (tensorCutoffWeight_nonneg g (fun _ => hg.2.1))]
  have he (j) : (∫ x, |f j x-g j x|) ≤
      (2 * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I)) * δ j :=
    (scalarCubeGridHistogram_normalized_l1 I (a j) (S j) (hS j) (hδ j) (hδ1 j)
      (hmesh j) (hpos j)).trans_eq (by ring)
  have hmove (j) (x) : dist (rectangularLatticeSample (a j) (S j) x) x ≤ δ j := by
    rw [dist_eq_norm]
    exact rectangularLatticeSample_error _ _ (hS j) (hδ j) (hmesh j) x
  exact (product_density_rounding_error (fun _ => volume) f g
    (fun j => (hf j).1) (fun _ => hg.1) (fun j => (hf j).2.1) (fun _ => hg.2.1)
    (fun j => (hf j).2.2) (fun _ => hg.2.2) (fun j => rectangularLatticeSample (a j) (S j))
    (fun j => rectangularLatticeSample_measurable (a j) (S j)) δ _ hδ he hmove φ hφ hB hb).trans_eq
      (by rw [← Finset.mul_sum]; dsimp only [δ]; ring)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem principalTuple_residue_riemann {D α : Type*} [Fintype D] [DecidableEq D]
    [Fintype α] [DecidableEq α] (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    (h : D → ℕ) (L M : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
    (m : PrincipalTupleIndex B h → Option α → ℕ) (r : ∀ j i, ZMod (m j i))
    (hm : ∀ j i, 0 < m j i) (hmM : ∀ j i, m j i ≤ M j)
    (hsize : ∀ j, (Fintype.card α + 1)*M j ≤ L j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((M j : ℝ)/L j) <
      volume.real (scalarCubeDomain α))
    (φ : (JointBlockParameter B h α → ℝ) → ℝ) {K : ℝ≥0} {A : ℝ}
    (hφ : LipschitzWith K φ) (hA : 0 ≤ A) (hb : ∀ x, ‖φ x‖ ≤ A) :
    |(FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights α (L j) (M j) (hL j)
      (m j) (r j) (hm j) (hmM j) (hsize j))).mean
        (fun z => φ (fun s => (z ⟨s.1, s.2.1, s.2.2.1⟩ s.2.2.2 : ℝ) / L ⟨s.1, s.2.1, s.2.2.1⟩)) -
      ∫ x, φ x ∂jointBooleanSource h| ≤
      (2 * A * scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) + K) *
        ∑ j, (M j : ℝ)/L j := by
  have htest : LipschitzWith K (φ ∘ principalTupleFlatten B h α) := by
    simpa only [mul_one] using hφ.comp (principalTupleFlatten_lipschitz B h α)
  rw [jointBooleanSource_principalTuple_integral]
  exact scalarCubeResidueWeights_pi_riemann L M hL m r hm hmM hsize hsmall
    (φ ∘ principalTupleFlatten B h α) htest hA (fun x => hb _)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem scalarCubeResidueWeights_pi_riemann_on_box {J I : Type*}
    [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (L M : J → ℕ) (hL : ∀ j, 0 < L j) (m : J → Option I → ℕ)
    (r : ∀ j i, ZMod (m j i)) (hm : ∀ j i, 0 < m j i) (hmM : ∀ j i, m j i ≤ M j)
    (hsize : ∀ j, (Fintype.card I + 1)*M j ≤ L j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant I * ((M j : ℝ)/L j) <
      volume.real (scalarCubeDomain I))
    (φ : (J → Option I → ℝ) → ℝ) {K : ℝ≥0} {B : ℝ}
    (hφ : LipschitzOnWith K φ (Metric.closedBall 0 1))
    (hB : 0 ≤ B) (hb : ∀ x ∈ Metric.closedBall 0 1, ‖φ x‖ ≤ B) :
    |(FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights I (L j) (M j) (hL j)
      (m j) (r j) (hm j) (hmM j) (hsize j))).mean
        (fun z => φ (fun j i => (z j i : ℝ) / L j)) -
      ∫ x, φ x ∂scalarCubeProductMeasure J I| ≤
      (2 * B * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I) + K) *
        ∑ j, (M j : ℝ)/L j := by
  apply finiteSource_comparison_on_set _ _ _ (Metric.closedBall 0 1) _
    (scalarCubeProductMeasure_ae_closedBall J I) hB
    (fun g hg hgb => scalarCubeResidueWeights_pi_riemann L M hL m r hm hmM hsize hsmall g hg hB hgb)
    φ hφ hb
  intro z
  rw [Metric.mem_closedBall, dist_zero_right]
  exact integerScalarCubeTuple_normalized_norm_le hL z

theorem principalTuple_residue_riemann_on_box {D α : Type*} [Fintype D] [DecidableEq D]
    [Fintype α] [DecidableEq α] (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    (h : D → ℕ) (L M : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
    (m : PrincipalTupleIndex B h → Option α → ℕ) (r : ∀ j i, ZMod (m j i))
    (hm : ∀ j i, 0 < m j i) (hmM : ∀ j i, m j i ≤ M j)
    (hsize : ∀ j, (Fintype.card α + 1)*M j ≤ L j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((M j : ℝ)/L j) <
      volume.real (scalarCubeDomain α))
    (φ : (JointBlockParameter B h α → ℝ) → ℝ) {K : ℝ≥0} {A : ℝ}
    (hφ : LipschitzOnWith K φ (Metric.closedBall 0 1))
    (hA : 0 ≤ A) (hb : ∀ x ∈ Metric.closedBall 0 1, ‖φ x‖ ≤ A) :
    |(FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights α (L j) (M j) (hL j)
      (m j) (r j) (hm j) (hmM j) (hsize j))).mean
        (fun z => φ (fun s => (z ⟨s.1, s.2.1, s.2.2.1⟩ s.2.2.2 : ℝ) / L ⟨s.1, s.2.1, s.2.2.1⟩)) -
      ∫ x, φ x ∂jointBooleanSource h| ≤
      (2 * A * scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) + K) *
        ∑ j, (M j : ℝ)/L j := by
  apply finiteSource_comparison_on_set _ _ _ (Metric.closedBall 0 1) _
    (jointBooleanSource_ae_closedBall B h) hA
    (fun g hg hgb => principalTuple_residue_riemann B h L M hL m r hm hmM hsize hsmall g hg hA hgb)
    φ hφ hb
  intro z
  rw [Metric.mem_closedBall, dist_zero_right]
  exact principalTuple_normalized_norm_le B h hL z

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

theorem masked_product_error {D : Type*} [Fintype D]
    (a f m : D → ℝ) {C G ε : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G) (hε : 0 ≤ ε)
    (hf : ∀ d, |f d| ≤ C) (hm : ∀ d, |m d| ≤ G)
    (he : ∀ d, |a d-m d*f d| ≤ ε) :
    |(∏ d, a d) - (∏ d, m d)*(∏ d, f d)| ≤
      Fintype.card D * ε * (1+G*C+ε)^Fintype.card D := by
  have hb : 1 ≤ 1+G*C+ε := by nlinarith [mul_nonneg hG hC]
  have hmf (d) : |m d*f d| ≤ G*C := by
    rw [abs_mul]
    exact mul_le_mul (hm d) (hf d) (abs_nonneg _) hG
  have ha (d) : |a d| ≤ 1+G*C+ε := by
    have ht := abs_add_le (a d-m d*f d) (m d*f d)
    rw [sub_add_cancel] at ht
    linarith [he d, hmf d]
  simpa only [Finset.card_univ, Finset.prod_mul_distrib] using
    abs_finset_prod_sub_prod_le Finset.univ a (fun d => m d*f d) hb hε
      (fun d _ => ha d) (fun d _ => (hmf d).trans (by linarith)) (fun d _ => he d)

theorem finiteProduct_cap {D X : Type*} [Fintype D] (f : D → X → ℝ) {C : ℝ}
    (_hC : 0 ≤ C) (hf : ∀ d x, |f d x| ≤ C) (x : X) :
    |∏ d, f d x| ≤ C^Fintype.card D := by
  rw [Finset.abs_prod]
  calc
    _ ≤ ∏ _d : D, C := Finset.prod_le_prod₀ (fun d _ => abs_nonneg _) (fun d _ => hf d x)
    _ = _ := by simp

theorem finiteProduct_lipschitzOn {D X : Type*} [Fintype D] [PseudoMetricSpace X]
    (f : D → X → ℝ) (S : Set X) (C K : ℝ≥0) (hC : 1 ≤ C)
    (hf : ∀ d, LipschitzOnWith K (f d) S) (hcap : ∀ d x, x ∈ S → |f d x| ≤ C) :
    LipschitzOnWith (Fintype.card D*K*C^Fintype.card D) (fun x => ∏ d, f d x) S := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [Real.dist_eq]
  have he := abs_finset_prod_sub_prod_le Finset.univ (fun d => f d x) (fun d => f d y)
    (show (1 : ℝ) ≤ C from hC) (show 0 ≤ (K : ℝ)*dist x y by positivity)
    (fun d _ => hcap d x hx) (fun d _ => hcap d y hy)
    (fun d _ => by simpa only [Real.dist_eq] using (hf d).dist_le_mul x hx y hy)
  simpa only [Finset.card_univ, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_pow, mul_assoc,
    mul_left_comm, mul_comm] using he

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem finiteSource_density_l1_of_test_quadrature {Ω T X : Type*} [Fintype Ω]
    [PseudoMetricSpace T] [MeasurableSpace T] [MeasurableSpace X]
    (p : FiniteProbabilityWeights Ω) (F : Ω → T) (μ : Measure T) (ν : Measure X)
    [IsProbabilityMeasure μ] [SFinite ν] (S : Set T)
    (hF : ∀ a, F a ∈ S) (hμ : ∀ᵐ t ∂μ, t ∈ S)
    (D : T → X → ℝ) (hD : Measurable (Function.uncurry D))
    (hp : ∀ t ∈ S, (∀ x, 0 ≤ D t x) ∧ Integrable (D t) ν ∧ (∫ x, D t x ∂ν) = 1)
    {K : ℝ≥0} (hlip : ∀ a ∈ S, ∀ b ∈ S, (∫ x, |D a x - D b x| ∂ν) ≤ K * dist a b)
    {ε : ℝ} (hq : ∀ φ : T → ℝ, LipschitzOnWith K φ S → (∀ t ∈ S, ‖φ t‖ ≤ 1) →
      |p.mean (fun a => φ (F a)) - ∫ t, φ t ∂μ| ≤ ε) :
    Integrable (fun x => p.mean (fun a => D (F a) x) - densityMixture μ D x) ν ∧
      (∫ x, |p.mean (fun a => D (F a) x) - densityMixture μ D x| ∂ν) ≤ ε := by
  have hmi : Integrable (fun x => p.mean (fun a => D (F a) x)) ν :=
    integrable_finsetSum _ (fun a _ => ((hp _ (hF a)).2.1).const_mul (p.weight a))
  have hmm : Measurable (fun x => p.mean (fun a => D (F a) x)) :=
    p.mean_measurable _ (fun a => hD.comp (measurable_const.prodMk measurable_id))
  have hd := densityMixture_joint_integrable μ ν D hD (hμ.mono (fun t ht => hp t ht))
  have hdm : Measurable (densityMixture μ D) :=
    hD.stronglyMeasurable.integral_prod_left'.measurable
  refine ⟨hmi.sub hd.integral_prod_right, ?_⟩
  apply density_l1_le_of_bounded_tests ν _ _ hmm hdm hmi hd.integral_prod_right
  intro φ hφ hb
  have htest := hq (fun t => ∫ x, D t x * φ x ∂ν)
    (density_test_lipschitzOn ν D S (fun t ht => (hp t ht).2.1) hlip φ hφ hb)
    (fun t ht => density_test_norm_le_one ν (D t) (hp t ht).2.1
      (hp t ht).1 (hp t ht).2.2 φ hb)
  rw [densityMixture_test_integral μ ν D hd φ hφ hb]
  have hmtest : (∫ x, p.mean (fun a => D (F a) x) * φ x ∂ν) =
      p.mean (fun a => ∫ x, D (F a) x * φ x ∂ν) := by
    simp only [FiniteProbabilityWeights.mean, Finset.sum_mul, mul_assoc]
    rw [integral_finsetSum _ (fun a _ =>
      (((hp _ (hF a)).2.1).mul_bdd hφ.aestronglyMeasurable
        (Filter.Eventually.of_forall hb)).const_mul (p.weight a))]
    simp only [integral_const_mul]
  rw [hmtest]
  exact htest

theorem principalTuple_density_l1_of_l1_regular {D α X : Type*}
    [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α] [MeasurableSpace X]
    (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
    (L M : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
    (m : PrincipalTupleIndex B h → Option α → ℕ) (r : ∀ j i, ZMod (m j i))
    (hm : ∀ j i, 0 < m j i) (hmM : ∀ j i, m j i ≤ M j)
    (hsize : ∀ j, (Fintype.card α+1)*M j ≤ L j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((M j : ℝ)/L j) < volume.real (scalarCubeDomain α))
    (ν : Measure X) [SFinite ν]
    (ρ : (JointBlockParameter B h α → ℝ) → X → ℝ) (hρ : Measurable (Function.uncurry ρ))
    (hp : ∀ t ∈ Metric.closedBall 0 1,
      (∀ x, 0 ≤ ρ t x) ∧ Integrable (ρ t) ν ∧ (∫ x, ρ t x ∂ν) = 1)
    {K : ℝ≥0} (hlip : ∀ a ∈ Metric.closedBall 0 1, ∀ b ∈ Metric.closedBall 0 1,
      (∫ x, |ρ a x - ρ b x| ∂ν) ≤ K * dist a b) :
    let Δ := fun v => (FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights α (L j) (M j) (hL j)
      (m j) (r j) (hm j) (hmM j) (hsize j))).mean
        (fun y => ρ (fun s => (y ⟨s.1, s.2.1, s.2.2.1⟩ s.2.2.2 : ℝ) / L ⟨s.1, s.2.1, s.2.2.1⟩) v) -
      ∫ x, ρ x v ∂jointBooleanSource h
    Integrable Δ ν ∧ (∫ v, |Δ v| ∂ν) ≤
      (2 * scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) + K) *
        ∑ j, (M j : ℝ)/L j := by
  refine finiteSource_density_l1_of_test_quadrature _ _ (jointBooleanSource h) ν
    (Metric.closedBall 0 1) ?_ (jointBooleanSource_ae_closedBall B h) ρ hρ hp hlip ?_
  · intro y
    rw [Metric.mem_closedBall, dist_zero_right]
    exact principalTuple_normalized_norm_le B h hL y
  · intro φ hφ hb
    simpa only [mul_one] using principalTuple_residue_riemann_on_box B h L M hL m r hm hmM
      hsize hsmall φ hφ (by norm_num : (0 : ℝ) ≤ 1) hb

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem principalTuple_residue_retained_riemann {Z D α : Type*} [MeasurableSpace Z]
    [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
    (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
    (L M : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
    (m : PrincipalTupleIndex B h → Option α → ℕ) (r : ∀ j i, ZMod (m j i))
    (hm : ∀ j i, 0 < m j i) (hmM : ∀ j i, m j i ≤ M j)
    (hsize : ∀ j, (Fintype.card α + 1)*M j ≤ L j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((M j : ℝ)/L j) <
      volume.real (scalarCubeDomain α))
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (φ : Z × (JointBlockParameter B h α → ℝ) → ℝ) (hφ : Measurable φ)
    {K : ℝ≥0} {A : ℝ} (hA : 0 ≤ A) (hb : ∀ x, ‖φ x‖ ≤ A)
    (hlip : ∀ z, LipschitzOnWith K (fun x => φ (z, x)) (Metric.closedBall 0 1)) :
    |(∫ u, (FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights α (L j) (M j) (hL j)
      (m j) (r j) (hm j) (hmM j) (hsize j))).mean
        (fun z => φ (u, fun s => (z ⟨s.1, s.2.1, s.2.2.1⟩ s.2.2.2 : ℝ) / L ⟨s.1, s.2.1, s.2.2.1⟩)) ∂μ) -
      ∫ x, φ x ∂μ.prod (jointBooleanSource h)| ≤
      (2 * A * scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) + K) *
        ∑ j, (M j : ℝ)/L j := by
  apply finiteSource_product_comparison _ _ μ (jointBooleanSource h) φ hφ hb
  apply Filter.Eventually.of_forall
  intro z
  exact principalTuple_residue_riemann_on_box B h L M hL m r hm hmM hsize hsmall
    (fun x => φ (z, x)) (hlip z) hA (fun x _ => hb (z, x))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem jointCoefficient_product_error {D : Type*} [Fintype D] {X : D → Type*}
    [∀ d, Countable (X d)] [∀ d, MeasurableSpace (X d)] [∀ d, MeasurableSingletonClass (X d)]
    (p : ∀ d, PMF (X d)) (S : D → ℝ) (m f : ∀ d, X d → ℝ)
    {C G ε : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G) (hε : 0 ≤ ε)
    (hcap : ∀ d x, |f d x| ≤ C) (hmask : ∀ d x, |m d x| ≤ G)
    (he : ∀ d x, |S d*(p d x).toReal-m d x*f d x| ≤ ε) (x : ∀ d, X d) :
    |(∏ d, S d)*(dependentProductPMF p x).toReal - (∏ d, m d (x d))*(∏ d, f d (x d))| ≤
      Fintype.card D*ε*(1+G*C+ε)^Fintype.card D := by
  rw [dependentProductPMF_scaled]
  exact masked_product_error _ _ _ hC hG hε (fun d => hcap d (x d))
    (fun d => hmask d (x d)) (fun d => he d (x d))

theorem jointCoefficient_mean_error {Ω D : Type*} [Fintype Ω] [Fintype D] {X : D → Type*}
    [∀ d, Countable (X d)] [∀ d, MeasurableSpace (X d)] [∀ d, MeasurableSingletonClass (X d)]
    (q : FiniteProbabilityWeights Ω) (p : Ω → ∀ d, PMF (X d)) (S : D → ℝ)
    (m : ∀ d, X d → ℝ) (f : Ω → ∀ d, X d → ℝ)
    {C G ε : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G) (hε : 0 ≤ ε)
    (hcap : ∀ ω, q.weight ω ≠ 0 → ∀ d x, |f ω d x| ≤ C)
    (hmask : ∀ d x, |m d x| ≤ G)
    (he : ∀ ω, q.weight ω ≠ 0 → ∀ d x, |S d*(p ω d x).toReal-m d x*f ω d x| ≤ ε)
    (x : ∀ d, X d) :
    |q.mean (fun ω => (∏ d, S d)*(dependentProductPMF (p ω) x).toReal) -
      q.mean (fun ω => (∏ d, m d (x d))*(∏ d, f ω d (x d)))| ≤
        Fintype.card D*ε*(1+G*C+ε)^Fintype.card D := by
  apply finiteMean_abs_sub_le_of_support
  intro ω hω
  exact jointCoefficient_product_error (p ω) S m (f ω) hC hG hε (hcap ω hω) hmask (he ω hω) x

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

noncomputable def jointTupleQuadratureError {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
    (B : D → Type*) [∀ d, Fintype (B d)] (h : D → ℕ) (n : ℕ) (C K : ℝ≥0)
    (L : PrincipalTupleIndex B h → ℕ) (m : ℕ) : ℝ :=
  (2 * (C : ℝ)^n * scalarCubeGridBoundaryConstant α / volume.real (scalarCubeDomain α) +
    (n : ℝ)*K*(C : ℝ)^n) * ∑ j, (m : ℝ)/L j

theorem sharedTupleProduct_riemann {A D α : Type*} [Fintype A]
    [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
    (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j) (m : ℕ) (hm : 0 < m)
    (r : PrincipalTupleIndex B h → Option α → ZMod m)
    (hsize : ∀ j, (Fintype.card α+1)*m ≤ L j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((m : ℝ)/L j) < volume.real (scalarCubeDomain α))
    (f : A → (JointBlockParameter B h α → ℝ) → ℝ) (C K : ℝ≥0) (hC : 1 ≤ C)
    (hf : ∀ d, LipschitzOnWith K (f d) (Metric.closedBall 0 1))
    (hcap : ∀ d x, |f d x| ≤ C) :
    |(principalResidueWeights B h L hL m hm r hsize).mean
      (fun y => ∏ d, f d (principalTupleNormalized L y)) -
      ∫ x, (∏ d, f d x) ∂jointBooleanSource h| ≤
        jointTupleQuadratureError (α := α) B h (Fintype.card A) C K L m := by
  have hp := finiteProduct_lipschitzOn f (Metric.closedBall 0 1) C K hC hf (fun d x _ => hcap d x)
  have hb := finiteProduct_cap f C.coe_nonneg hcap
  exact principalTuple_residue_riemann_on_box B h L (fun _ => m) hL (fun _ _ => m) r
    (fun _ _ => hm) (fun _ _ => le_rfl) hsize hsmall (fun x => ∏ d, f d x) hp
    (by positivity) (fun x _ => hb x)

theorem sharedTupleProduct_retained_riemann {Z A D α : Type*} [MeasurableSpace Z] [Fintype A]
    [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
    (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j) (m : ℕ) (hm : 0 < m)
    (r : PrincipalTupleIndex B h → Option α → ZMod m)
    (hsize : ∀ j, (Fintype.card α+1)*m ≤ L j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((m : ℝ)/L j) < volume.real (scalarCubeDomain α))
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (f : Z → A → (JointBlockParameter B h α → ℝ) → ℝ) (C K : ℝ≥0) (hC : 1 ≤ C)
    (hfm : ∀ d, Measurable (fun p : Z × (JointBlockParameter B h α → ℝ) => f p.1 d p.2))
    (hf : ∀ z d, LipschitzOnWith K (f z d) (Metric.closedBall 0 1))
    (hcap : ∀ z d x, |f z d x| ≤ C) :
    |(∫ z, (principalResidueWeights B h L hL m hm r hsize).mean
      (fun y => ∏ d, f z d (principalTupleNormalized L y)) ∂μ) -
      ∫ p, (∏ d, f p.1 d p.2) ∂μ.prod (jointBooleanSource h)| ≤
        jointTupleQuadratureError (α := α) B h (Fintype.card A) C K L m := by
  apply finiteSource_product_comparison _ (principalTupleNormalized L) μ (jointBooleanSource h)
    (fun p => ∏ d, f p.1 d p.2) (Finset.measurable_prod _ (fun d _ => hfm d))
    (fun p => finiteProduct_cap (f p.1) C.coe_nonneg (hcap p.1) p.2)
  exact Filter.Eventually.of_forall (fun z => sharedTupleProduct_riemann B h L hL m hm r hsize hsmall
    (f z) C K hC (hf z) (hcap z))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem jointCoefficient_average_comparison {Ω Q : Type*} [Fintype Ω] [Fintype Q]
    {X : Q → Type*} [∀ d, Countable (X d)] [∀ d, MeasurableSpace (X d)]
    [∀ d, MeasurableSingletonClass (X d)]
    (q : FiniteProbabilityWeights Ω) (p : Ω → ∀ d, PMF (X d)) (S : Q → ℝ)
    (m : ∀ d, X d → ℝ) (f : Ω → ∀ d, X d → ℝ) (target : (∀ d, X d) → ℝ)
    {C G ε η : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G) (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hcap : ∀ ω, q.weight ω ≠ 0 → ∀ d x, |f ω d x| ≤ C)
    (hmask : ∀ d x, 0 ≤ m d x ∧ m d x ≤ G)
    (he : ∀ ω, q.weight ω ≠ 0 → ∀ d x, |S d*(p ω d x).toReal-m d x*f ω d x| ≤ ε)
    (hquad : ∀ x, |q.mean (fun ω => ∏ d, f ω d (x d))-target x| ≤ η)
    (x : ∀ d, X d) :
    |q.mean (fun ω => (∏ d, S d)*(dependentProductPMF (p ω) x).toReal) -
      (∏ d, m d (x d))*target x| ≤
        Fintype.card Q*ε*(1+G*C+ε)^Fintype.card Q + G^Fintype.card Q*η := by
  have hm0 : 0 ≤ ∏ d, m d (x d) := Finset.prod_nonneg (fun d _ => (hmask d (x d)).1)
  have hmG : (∏ d, m d (x d)) ≤ G^Fintype.card Q := by
    calc
      _ ≤ ∏ _d : Q, G := Finset.prod_le_prod₀ (fun d _ => (hmask d (x d)).1)
        (fun d _ => (hmask d (x d)).2)
      _ = _ := by simp
  apply finiteMean_masked_comparison_of_support q _ _ hm0 hmG hη _ (hquad x)
  intro ω hω
  exact jointCoefficient_product_error (p ω) S m (f ω) hC hG hε (hcap ω hω)
    (fun d y => by rw [abs_of_nonneg (hmask d y).1]; exact (hmask d y).2) (he ω hω) x

theorem jointCoefficient_principalTuple_comparison {Q D α : Type*}
    [Fintype Q] [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
    {X : Q → Type*} [∀ d, Countable (X d)] [∀ d, MeasurableSpace (X d)]
    [∀ d, MeasurableSingletonClass (X d)]
    (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
    (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j) (modulus : ℕ) (hm : 0 < modulus)
    (r : PrincipalTupleIndex B h → Option α → ZMod modulus)
    (hsize : ∀ j, (Fintype.card α+1)*modulus ≤ L j)
    (hsmall : ∀ j, scalarCubeGridBoundaryConstant α * ((modulus : ℝ)/L j) < volume.real (scalarCubeDomain α))
    (p : PrincipalIntegerTuples B h α L → ∀ d, PMF (X d)) (S : Q → ℝ)
    (m : ∀ d, X d → ℝ) (f : (JointBlockParameter B h α → ℝ) → ∀ d, X d → ℝ)
    (C K : ℝ≥0) (hC : 1 ≤ C) {G ε : ℝ} (hG : 0 ≤ G) (hε : 0 ≤ ε)
    (hcap : ∀ y d x, |f y d x| ≤ C)
    (hLip : ∀ d x, LipschitzOnWith K (fun y => f y d x) (Metric.closedBall 0 1))
    (hmask : ∀ d x, 0 ≤ m d x ∧ m d x ≤ G)
    (he : ∀ y, (principalResidueWeights B h L hL modulus hm r hsize).weight y ≠ 0 →
      ∀ d x, |S d*(p y d x).toReal-m d x*f (principalTupleNormalized L y) d x| ≤ ε)
    (x : ∀ d, X d) :
    |(principalResidueWeights B h L hL modulus hm r hsize).mean
      (fun y => (∏ d, S d)*(dependentProductPMF (p y) x).toReal) -
      (∏ d, m d (x d))*(∫ y, (∏ d, f y d (x d)) ∂jointBooleanSource h)| ≤
        Fintype.card Q*ε*(1+G*C+ε)^Fintype.card Q +
          G^Fintype.card Q*jointTupleQuadratureError (α := α) B h (Fintype.card Q) C K L modulus := by
  have hquad (x : ∀ d, X d) := sharedTupleProduct_riemann B h L hL modulus hm r hsize hsmall
    (fun d y => f y d (x d)) C K hC (fun d => hLip d (x d)) (fun d y => hcap y d (x d))
  exact jointCoefficient_average_comparison _ p S m (fun y => f (principalTupleNormalized L y))
    (fun x => ∫ y, (∏ d, f y d (x d)) ∂jointBooleanSource h) C.coe_nonneg hG hε
    ((abs_nonneg _).trans (hquad x)) (fun y _ => hcap (principalTupleNormalized L y)) hmask he hquad x

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem jointCoefficient_retained_test {Z Y Q : Type*} [Fintype Z] [Fintype Q]
    {Ω : Z → Type*} [∀ z, Fintype (Ω z)]
    {X : Q → Type*} [∀ d, Countable (X d)] [∀ d, MeasurableSpace (X d)]
    [∀ d, MeasurableSingletonClass (X d)]
    (pZ : FiniteProbabilityWeights Z) (q : ∀ z, FiniteProbabilityWeights (Ω z))
    (p : ∀ z, Ω z → ∀ d, PMF (X d)) (S : Z → Q → ℝ)
    (m : Z → ∀ d, X d → ℝ) (f : ∀ z, Ω z → ∀ d, X d → ℝ)
    (target : Z → (∀ d, X d) → ℝ)
    (s : Z → Finset (∀ d, X d)) (grid : Z → Y) (D : Z → (∀ d, X d) → ℝ)
    (φ : Y → (∀ d, X d) → ℂ)
    {C G ε η M : ℝ} (hC : 0 ≤ C) (hG : 0 ≤ G) (hε : 0 ≤ ε) (hη : 0 ≤ η)
    (hcap : ∀ z, pZ.weight z ≠ 0 → ∀ ω, (q z).weight ω ≠ 0 → ∀ d x, |f z ω d x| ≤ C)
    (hmask : ∀ z, pZ.weight z ≠ 0 → ∀ d x, 0 ≤ m z d x ∧ m z d x ≤ G)
    (he : ∀ z, pZ.weight z ≠ 0 → ∀ ω, (q z).weight ω ≠ 0 → ∀ d x,
      |S z d*(p z ω d x).toReal-m z d x*f z ω d x| ≤ ε)
    (hquad : ∀ z, pZ.weight z ≠ 0 → ∀ x,
      |(q z).mean (fun ω => ∏ d, f z ω d (x d))-target z x| ≤ η)
    (hD : ∀ z, pZ.weight z ≠ 0 → ∀ x ∈ s z, 0 ≤ D z x)
    (hφ : ∀ z, pZ.weight z ≠ 0 → ∀ x ∈ s z, ‖φ (grid z) x‖ ≤ 1)
    (hmass : pZ.mean (fun z => ∑ x ∈ s z, D z x) ≤ M) :
    ‖pZ.complexMean (fun z => ∑ x ∈ s z,
        ((D z x*(q z).mean (fun ω => (∏ d, S z d)*(dependentProductPMF (p z ω) x).toReal) : ℝ) : ℂ) *
          φ (grid z) x) -
      pZ.complexMean (fun z => ∑ x ∈ s z,
        ((D z x*((∏ d, m z d (x d))*target z x) : ℝ) : ℂ)*φ (grid z) x)‖ ≤
        (Fintype.card Q*ε*(1+G*C+ε)^Fintype.card Q+G^Fintype.card Q*η)*M := by
  apply retained_weighted_density_test_of_mass pZ s grid D _ _ φ (by positivity) hD hφ _ hmass
  intro z hz x _
  exact jointCoefficient_average_comparison (q z) (p z) (S z) (m z) (f z) (target z)
    hC hG hε hη (hcap z hz) (hmask z hz) (he z hz) (hquad z hz) x

end Erdos3

end

end OAI
