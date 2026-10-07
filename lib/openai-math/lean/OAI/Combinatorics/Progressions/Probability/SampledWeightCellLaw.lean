/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import OAI.Combinatorics.Progressions.Estimates.BoundedProductDifference
import OAI.Combinatorics.Progressions.Estimates.FiniteReciprocalTenthTail
import OAI.Combinatorics.Progressions.Estimates.NormalizedSampledHistogram
import OAI.Combinatorics.Progressions.Probability.BinaryDensity

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {ι : Type*} [Fintype ι]

noncomputable def independentCoordinateDensity (f : ι → ℝ → ℝ) (x : ι → ℝ) : ℝ :=
  ∏ i, f i (x i)

theorem independentCoordinateDensity_measurable (f : ι → ℝ → ℝ) (hf : ∀ i, Measurable (f i)) :
    Measurable (independentCoordinateDensity f) := by
  apply Finset.measurable_prod
  intro i _
  exact (hf i).comp (measurable_pi_apply i)

theorem independentCoordinateDensity_integrable (f : ι → ℝ → ℝ) (hf : ∀ i, Integrable (f i)) :
    Integrable (independentCoordinateDensity f) := Integrable.fintype_prod hf

theorem independentCoordinateDensity_mass (f : ι → ℝ → ℝ) (hf : ∀ i, (∫ x, f i x) = 1) :
    (∫ x, independentCoordinateDensity f x) = 1 := by
  unfold independentCoordinateDensity
  rw [integral_fintype_prod_volume_eq_prod]
  simp only [hf, Finset.prod_const_one]

theorem independentCoordinateDensity_cap (f : ι → ℝ → ℝ) (C : ι → ℝ)
    (hf : ∀ i x, f i x ∈ Set.Icc (0 : ℝ) (C i)) (x : ι → ℝ) :
    independentCoordinateDensity f x ∈ Set.Icc (0 : ℝ) (∏ i, C i) :=
  ⟨Finset.prod_nonneg (fun i _ => (hf i (x i)).1),
    Finset.prod_le_prod₀ (fun i _ => (hf i (x i)).1) (fun i _ => (hf i (x i)).2)⟩

theorem independentCoordinateDensity_lipschitz (f : ι → ℝ → ℝ) (C L : ι → ℝ≥0)
    (hf : ∀ i x, f i x ∈ Set.Icc (0 : ℝ) (C i)) (hL : ∀ i, LipschitzWith (L i) (f i)) :
    LipschitzWith ((∏ i, (C i + 1)) * ∑ i, L i) (independentCoordinateDensity f) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  have h := bounded_nonnegative_prod_difference Finset.univ (fun i => f i (x i))
    (fun i => f i (y i)) (fun i => (C i : ℝ) + 1)
    (fun i => by linarith [(C i).coe_nonneg])
    (fun i => ⟨(hf i _).1, (hf i _).2.trans (by linarith)⟩)
    (fun i => ⟨(hf i _).1, (hf i _).2.trans (by linarith)⟩)
  have hsum : (∑ i, |f i (x i) - f i (y i)|) ≤ (∑ i, (L i : ℝ)) * dist x y := by
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i _
    have hi := (hL i).dist_le_mul (x i) (y i)
    rw [Real.dist_eq] at hi
    exact hi.trans (mul_le_mul_of_nonneg_left (dist_le_pi_dist x y i) (L i).coe_nonneg)
  apply h.trans
  have hprod : 0 ≤ ∏ i, ((C i : ℝ) + 1) :=
    Finset.prod_nonneg (fun i _ => add_nonneg (C i).coe_nonneg zero_le_one)
  have hb := mul_le_mul_of_nonneg_left hsum hprod
  simpa only [NNReal.coe_mul, NNReal.coe_prod, NNReal.coe_sum, NNReal.coe_add,
    NNReal.coe_one, mul_assoc] using hb

theorem independentCoordinateDensity_test_product (f φ : ι → ℝ → ℝ) :
    (∫ x : ι → ℝ, independentCoordinateDensity f x * ∏ i, φ i (x i)) =
      ∏ i, ∫ x, f i x * φ i x := by
  unfold independentCoordinateDensity
  simp_rw [← Finset.prod_mul_distrib]
  exact integral_fintype_prod_volume_eq_prod (fun i x => f i x * φ i x)

theorem independentCoordinateDensity_lipschitz_uniform (f : ι → ℝ → ℝ) (C L : ℝ≥0)
    (hf : ∀ i x, f i x ∈ Set.Icc (0 : ℝ) C) (hL : ∀ i, LipschitzWith L (f i)) :
    LipschitzWith ((C + 1) ^ Fintype.card ι * (Fintype.card ι * L)) (independentCoordinateDensity f) := by
  have h := independentCoordinateDensity_lipschitz f (fun _ => C) (fun _ => L) hf hL
  simpa only [Finset.prod_const, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem abs_sub_eq_add_sub_two_min (x y : ℝ) : |x - y| = x + y - 2 * min x y := by
  rcases le_total x y with h | h
  · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
    ring

theorem integral_density_overlap (f g : ℝ → ℝ) (hf : Integrable f) (hg : Integrable g)
    (hfmass : (∫ x, f x) = 1) (hgmass : (∫ x, g x) = 1) :
    (∫ x, |f x - g x|) = 2 - 2 * ∫ x, min (f x) (g x) := by
  have hm : Integrable (fun x => min (f x) (g x)) := hf.inf hg
  have hsum : Integrable (fun x => f x + g x) := hf.add hg
  simp_rw [abs_sub_eq_add_sub_two_min]
  rw [integral_sub hsum (hm.const_mul 2), integral_add hf hg, integral_const_mul,
    hfmass, hgmass]
  norm_num

theorem density_overlap_mass (f g : ℝ → ℝ) (hf : Integrable f) (hg : Integrable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) (hfmass : (∫ x, f x) = 1) :
    (∫ x, min (f x) (g x)) ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨integral_nonneg (fun x => le_min (hf0 x) (hg0 x)), ?_⟩
  have hm : Integrable (fun x => min (f x) (g x)) := hf.inf hg
  exact (integral_mono hm hf (fun x => min_le_left _ _)).trans_eq hfmass

theorem product_density_l1_le_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f g : ι → ℝ → ℝ) (hf : ∀ i, Integrable (f i)) (hg : ∀ i, Integrable (g i))
    (hf0 : ∀ i x, 0 ≤ f i x) (hg0 : ∀ i x, 0 ≤ g i x)
    (hfmass : ∀ i, (∫ x, f i x) = 1) (hgmass : ∀ i, (∫ x, g i x) = 1) :
    (∫ x : ι → ℝ, |(∏ i, f i (x i)) - ∏ i, g i (x i)|) ≤
      ∑ i, ∫ x, |f i x - g i x| := by
  let F : (ι → ℝ) → ℝ := fun x => ∏ i, f i (x i)
  let G : (ι → ℝ) → ℝ := fun x => ∏ i, g i (x i)
  let H : (ι → ℝ) → ℝ := fun x => ∏ i, min (f i (x i)) (g i (x i))
  let mass : ι → ℝ := fun i => ∫ x, min (f i x) (g i x)
  have hF : Integrable F := Integrable.fintype_prod hf
  have hG : Integrable G := Integrable.fintype_prod hg
  have hH : Integrable H := Integrable.fintype_prod (fun i => (hf i).inf (hg i))
  have hpoint (x : ι → ℝ) : |F x - G x| ≤ F x + G x - 2 * H x := by
    have hHF : H x ≤ F x := Finset.prod_le_prod₀
      (fun i _ => le_min (hf0 i _) (hg0 i _)) (fun i _ => min_le_left _ _)
    have hHG : H x ≤ G x := Finset.prod_le_prod₀
      (fun i _ => le_min (hf0 i _) (hg0 i _)) (fun i _ => min_le_right _ _)
    rw [abs_sub_eq_add_sub_two_min]
    have hmin := le_min hHF hHG
    linarith
  have hFmass : (∫ x, F x) = 1 := by
    dsimp only [F]
    rw [integral_fintype_prod_volume_eq_prod]
    simp only [hfmass, Finset.prod_const_one]
  have hGmass : (∫ x, G x) = 1 := by
    dsimp only [G]
    rw [integral_fintype_prod_volume_eq_prod]
    simp only [hgmass, Finset.prod_const_one]
  have hHmass : (∫ x, H x) = ∏ i, mass i := by
    exact integral_fintype_prod_volume_eq_prod (fun i x => min (f i x) (g i x))
  have hleft : Integrable (fun x => |F x - G x|) := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hF.sub hG).norm
  have hsum : Integrable (fun x => F x + G x) := hF.add hG
  have hright : Integrable (fun x => F x + G x - 2 * H x) := hsum.sub (hH.const_mul 2)
  have hbound := integral_mono hleft hright hpoint
  rw [integral_sub hsum (hH.const_mul 2), integral_add hF hG,
    integral_const_mul, hFmass, hGmass, hHmass] at hbound
  have hm (i) : mass i ∈ Set.Icc (0 : ℝ) 1 :=
    density_overlap_mass (f i) (g i) (hf i) (hg i) (hf0 i) (hg0 i) (hfmass i)
  have hprod := one_sub_sum_le_positive_prod Finset.univ mass (fun i => 1 - mass i)
    (fun i _ => (hm i).1) (fun i _ => ⟨by linarith [(hm i).2], by linarith [(hm i).1]⟩)
    (fun i _ => by linarith)
  have herr : (∑ i, ∫ x, |f i x - g i x|) = 2 * ∑ i, (1 - mass i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_density_overlap (f i) (g i) (hf i) (hg i) (hfmass i) (hgmass i)]
    dsimp only [mass]
    ring
  rw [herr]
  change (∫ x, |F x - G x|) ≤ _
  linarith

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

noncomputable def realDensityMeasure {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) : Measure X := μ.withDensity (fun x => ENNReal.ofReal (f x))

theorem realDensityMeasure_apply {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℝ) (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x) {s : Set X} (hs : MeasurableSet s) :
    realDensityMeasure μ f s = ENNReal.ofReal (∫ x in s, f x ∂μ) := by
  rw [realDensityMeasure, withDensity_apply _ hs]
  exact (ofReal_integral_eq_lintegral_ofReal hf.integrableOn (Filter.Eventually.of_forall hf0)).symm

theorem realDensityMeasure_probability {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℝ) (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x) (hmass : (∫ x, f x ∂μ) = 1) :
    IsProbabilityMeasure (realDensityMeasure μ f) := by
  constructor
  rw [realDensityMeasure_apply μ f hf hf0 MeasurableSet.univ, Measure.restrict_univ,
    hmass, ENNReal.ofReal_one]

theorem binaryDensity_measure {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (f : X → ℝ) (g : Y → ℝ) (hf : Measurable f) (hg : Measurable g) (hf0 : ∀ x, 0 ≤ f x) :
    (realDensityMeasure μ f).prod (realDensityMeasure ν g) =
      realDensityMeasure (μ.prod ν) (binaryDensity f g) := by
  unfold realDensityMeasure
  rw [prod_withDensity hf.ennreal_ofReal hg.ennreal_ofReal]
  congr 1
  funext p
  exact (ENNReal.ofReal_mul (hf0 p.1)).symm

theorem independentCoordinateDensity_measure {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℝ) (hf : ∀ i, Integrable (f i)) (hf0 : ∀ i x, 0 ≤ f i x)
    (hmass : ∀ i, (∫ x, f i x) = 1) :
    Measure.pi (fun i => realDensityMeasure volume (f i)) =
      realDensityMeasure volume (independentCoordinateDensity f) := by
  let : ∀ i, IsProbabilityMeasure (realDensityMeasure volume (f i)) :=
    fun i => realDensityMeasure_probability volume (f i) (hf i) (hf0 i) (hmass i)
  apply Measure.pi_eq
  intro s hs
  have hprod0 (x : ι → ℝ) : 0 ≤ independentCoordinateDensity f x :=
    Finset.prod_nonneg (fun i _ => hf0 i (x i))
  rw [realDensityMeasure_apply volume _ (independentCoordinateDensity_integrable f hf) hprod0
    (MeasurableSet.univ_pi hs)]
  have hint : (∫ x in Set.univ.pi s, independentCoordinateDensity f x) =
      ∏ i, ∫ x in s i, f i x := by
    change (∫ x, (∏ i, f i (x i)) ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ))).restrict
      (Set.univ.pi s)) = _
    rw [Measure.restrict_pi_pi]
    exact integral_fintype_prod_eq_prod (fun i x => f i x)
  rw [hint, ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hf0 i))]
  apply Finset.prod_congr rfl
  intro i _
  exact (realDensityMeasure_apply volume (f i) (hf i) (hf0 i) (hs i)).symm

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

theorem independentCoordinateDensity_translation_l1 {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℝ → ℝ) (hf : ∀ i, Integrable (f i)) (hf0 : ∀ i x, 0 ≤ f i x)
    (hfmass : ∀ i, (∫ x, f i x) = 1) (D : ι → ℝ≥0)
    (hmove : ∀ i a b, (∫ x, |f i (x + a) - f i (x + b)|) ≤ D i * |a - b|)
    (a b : ι → ℝ) :
    (∫ x, |independentCoordinateDensity f (x + a) - independentCoordinateDensity f (x + b)|) ≤
      (∑ i, (D i : ℝ)) * dist a b := by
  have hi (c : ι → ℝ) (i : ι) : Integrable (fun x => f i (x + c i)) :=
    (hf i).comp_add_right (c i)
  have hmass (c : ι → ℝ) (i : ι) : (∫ x, f i (x + c i)) = 1 := by
    rw [integral_add_right_eq_self, hfmass]
  have h := product_density_l1_le_sum (fun i x => f i (x + a i)) (fun i x => f i (x + b i))
    (hi a) (hi b) (fun i x => hf0 i _) (fun i x => hf0 i _) (hmass a) (hmass b)
  apply h.trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  apply (hmove i (a i) (b i)).trans
  apply mul_le_mul_of_nonneg_left _ (D i).coe_nonneg
  simpa only [Real.dist_eq] using dist_le_pi_dist a b i

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem measured_density_overlap {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f g : X → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hfmass : (∫ x, f x ∂μ) = 1) (hgmass : (∫ x, g x ∂μ) = 1) :
    (∫ x, min (f x) (g x) ∂μ) ∈ Set.Icc (0 : ℝ) 1 ∧
      (∫ x, |f x-g x| ∂μ) = 2 - 2 * ∫ x, min (f x) (g x) ∂μ := by
  have hm : Integrable (fun x => min (f x) (g x)) μ := hf.inf hg
  have hsum : Integrable (fun x => f x + g x) μ := hf.add hg
  constructor
  · exact ⟨integral_nonneg (fun x => le_min (hf0 x) (hg0 x)),
      (integral_mono hm hf (fun x => min_le_left _ _)).trans_eq hfmass⟩
  · simp_rw [abs_sub_eq_add_sub_two_min]
    rw [integral_sub hsum (hm.const_mul 2), integral_add hf hg,
      integral_const_mul, hfmass, hgmass]
    norm_num

theorem tensor_density_l1_le_sum {D : Type*} [Fintype D] [DecidableEq D]
    {X : D → Type*} [∀ d, MeasurableSpace (X d)] (μ : ∀ d, Measure (X d)) [∀ d, SigmaFinite (μ d)]
    (f g : ∀ d, X d → ℝ) (hf : ∀ d, Integrable (f d) (μ d)) (hg : ∀ d, Integrable (g d) (μ d))
    (hf0 : ∀ d x, 0 ≤ f d x) (hg0 : ∀ d x, 0 ≤ g d x)
    (hfmass : ∀ d, (∫ x, f d x ∂μ d) = 1) (hgmass : ∀ d, (∫ x, g d x ∂μ d) = 1) :
    (∫ x, |(∏ d, f d (x d)) - ∏ d, g d (x d)| ∂Measure.pi μ) ≤
      ∑ d, ∫ x, |f d x-g d x| ∂μ d := by
  let F := fun x : ∀ d, X d => ∏ d, f d (x d)
  let G := fun x : ∀ d, X d => ∏ d, g d (x d)
  let H := fun x : ∀ d, X d => ∏ d, min (f d (x d)) (g d (x d))
  let mass := fun d => ∫ x, min (f d x) (g d x) ∂μ d
  have hF : Integrable F (Measure.pi μ) := Integrable.fintype_prod_dep hf
  have hG : Integrable G (Measure.pi μ) := Integrable.fintype_prod_dep hg
  have hH : Integrable H (Measure.pi μ) := Integrable.fintype_prod_dep (fun d => (hf d).inf (hg d))
  have hpoint (x : ∀ d, X d) : |F x-G x| ≤ F x+G x-2*H x := by
    have hl : H x ≤ F x := Finset.prod_le_prod₀
      (fun d _ => le_min (hf0 d _) (hg0 d _)) (fun d _ => min_le_left _ _)
    have hr : H x ≤ G x := Finset.prod_le_prod₀
      (fun d _ => le_min (hf0 d _) (hg0 d _)) (fun d _ => min_le_right _ _)
    rw [abs_sub_eq_add_sub_two_min]
    have hh := le_min hl hr
    linarith
  have hFm : (∫ x, F x ∂Measure.pi μ) = 1 := by
    rw [show F = (fun x => ∏ d, f d (x d)) from rfl, integral_fintype_prod_eq_prod]
    simp only [hfmass, Finset.prod_const_one]
  have hGm : (∫ x, G x ∂Measure.pi μ) = 1 := by
    rw [show G = (fun x => ∏ d, g d (x d)) from rfl, integral_fintype_prod_eq_prod]
    simp only [hgmass, Finset.prod_const_one]
  have hHm : (∫ x, H x ∂Measure.pi μ) = ∏ d, mass d :=
    integral_fintype_prod_eq_prod (fun d x => min (f d x) (g d x))
  have hsum : Integrable (fun x => F x + G x) (Measure.pi μ) := hF.add hG
  have he := integral_mono (hF.sub hG).abs ((hF.add hG).sub (hH.const_mul 2)) hpoint
  change (∫ x, |F x-G x| ∂Measure.pi μ) ≤
    ∫ x, F x+G x-2*H x ∂Measure.pi μ at he
  rw [integral_sub hsum (hH.const_mul 2), integral_add hF hG,
    integral_const_mul, hFm, hGm, hHm] at he
  have hm (d) := measured_density_overlap (μ d) (f d) (g d) (hf d) (hg d)
    (hf0 d) (hg0 d) (hfmass d) (hgmass d)
  have hp := one_sub_sum_le_positive_prod Finset.univ mass (fun d => 1-mass d)
    (fun d _ => (hm d).1.1) (fun d _ => ⟨by linarith [(hm d).1.2], by linarith [(hm d).1.1]⟩)
    (fun d _ => by linarith)
  have hh : (∑ d, ∫ x, |f d x-g d x| ∂μ d) = 2 * ∑ d, (1-mass d) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [(hm d).2]
    dsimp only [mass]
    ring
  rw [hh]
  change (∫ x, |F x-G x| ∂Measure.pi μ) ≤ _
  linarith

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem continuousDensity_eq_of_measure_eq {I : Type*} [Fintype I]
    {f g : (I → ℝ) → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (he : realDensityMeasure volume f = realDensityMeasure volume g) : f = g := by
  have hae := (withDensity_eq_iff_of_sigmaFinite
    hf.measurable.ennreal_ofReal.aemeasurable hg.measurable.ennreal_ofReal.aemeasurable).mp he
  apply (hf.ae_eq_iff_eq volume hg).mp
  filter_upwards [hae] with x hx
  exact (ENNReal.ofReal_eq_ofReal_iff (hf0 x) (hg0 x)).mp hx

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ENNReal

theorem sampledWeightMass_zero_off (ψ : ℝ → ℝ) {a S R : ℝ} (hS : 0 < S)
    (hsupport : ∀ x, R < |x| → ψ x = 0) (k : ℤ) (hk : k ∉ sampledWeightIndices a S R) :
    sampledWeightMass ψ a S R k = 0 := by
  rw [sampledWeightMass, sampledWeight_zero_off_indices ψ hS hsupport k hk, zero_div]

noncomputable def sampledWeightPMF (ψ : ℝ → ℝ) (hψ : ∀ x, 0 ≤ ψ x)
    (a S R : ℝ) (hS : 0 < S) (hsupport : ∀ x, R < |x| → ψ x = 0)
    (hZ : sampledWeightSum ψ a S R ≠ 0) : PMF ℤ :=
  PMF.ofFinset (fun k => ENNReal.ofReal (sampledWeightMass ψ a S R k))
    (sampledWeightIndices a S R)
    (by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => sampledWeightMass_nonneg ψ hψ a S R k),
        sampledWeightMass_sum ψ a S R hZ, ENNReal.ofReal_one])
    (fun k hk => by rw [sampledWeightMass_zero_off ψ hS hsupport k hk, ENNReal.ofReal_zero])

theorem sampledWeightPMF_apply (ψ : ℝ → ℝ) (hψ : ∀ x, 0 ≤ ψ x)
    (a S R : ℝ) (hS : 0 < S) (hsupport : ∀ x, R < |x| → ψ x = 0)
    (hZ : sampledWeightSum ψ a S R ≠ 0) (k : ℤ) :
    (sampledWeightPMF ψ hψ a S R hS hsupport hZ k).toReal = sampledWeightMass ψ a S R k :=
  ENNReal.toReal_ofReal (sampledWeightMass_nonneg ψ hψ a S R k)

theorem sampledWeightPMF_singleton (ψ : ℝ → ℝ) (hψ : ∀ x, 0 ≤ ψ x)
    (a S R : ℝ) (hS : 0 < S) (hsupport : ∀ x, R < |x| → ψ x = 0)
    (hZ : sampledWeightSum ψ a S R ≠ 0) (k : ℤ) :
    (sampledWeightPMF ψ hψ a S R hS hsupport hZ).toMeasure.real {k} = sampledWeightMass ψ a S R k := by
  rw [measureReal_def, PMF.toMeasure_apply_singleton _ k (measurableSet_singleton k)]
  exact sampledWeightPMF_apply ψ hψ a S R hS hsupport hZ k

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem normalizedWeightHistogram_cell_integral (ψ : ℝ → ℝ) {a S R : ℝ} (hS : 0 < S)
    (hsupport : ∀ x, R < |x| → ψ x = 0) (k : ℤ) :
    (∫ x in latticeSamplingCell a S k, normalizedWeightHistogram ψ a S R x) =
      sampledWeightMass ψ a S R k := by
  rw [setIntegral_congr_fun (latticeSamplingCell_measurable a S k)
    (fun x hx => normalizedWeightHistogram_on_cell ψ hS hsupport k hx),
    setIntegral_const, latticeSamplingCell_volume hS, smul_eq_mul]
  field_simp

theorem normalizedWeightHistogram_probability (ψ : ℝ → ℝ) (hψ : ∀ x, 0 ≤ ψ x)
    {a S R : ℝ} (hS : 0 < S) (hsupport : ∀ x, R < |x| → ψ x = 0)
    (hZ : sampledWeightSum ψ a S R ≠ 0) :
    IsProbabilityMeasure (realDensityMeasure volume (normalizedWeightHistogram ψ a S R)) :=
  realDensityMeasure_probability volume _ (normalizedWeightHistogram_integrable ψ a S R)
    (normalizedWeightHistogram_nonneg ψ hψ hS hsupport)
    (normalizedWeightHistogram_integral ψ a R hS hZ)

theorem normalizedWeightHistogram_cell_mass (ψ : ℝ → ℝ) (hψ : ∀ x, 0 ≤ ψ x)
    {a S R : ℝ} (hS : 0 < S) (hsupport : ∀ x, R < |x| → ψ x = 0) (k : ℤ) :
    realDensityMeasure volume (normalizedWeightHistogram ψ a S R) (latticeSamplingCell a S k) =
      ENNReal.ofReal (sampledWeightMass ψ a S R k) := by
  rw [realDensityMeasure_apply volume _ (normalizedWeightHistogram_integrable ψ a S R)
    (normalizedWeightHistogram_nonneg ψ hψ hS hsupport) (latticeSamplingCell_measurable a S k),
    normalizedWeightHistogram_cell_integral ψ hS hsupport]

theorem normalizedWeightHistogram_rounding_law (ψ : ℝ → ℝ) (hψ : ∀ x, 0 ≤ ψ x)
    {a S R : ℝ} (hS : 0 < S) (hsupport : ∀ x, R < |x| → ψ x = 0)
    (hZ : sampledWeightSum ψ a S R ≠ 0) :
    (realDensityMeasure volume (normalizedWeightHistogram ψ a S R)).map
      (fun x => ⌊a + S * x⌋) = (sampledWeightPMF ψ hψ a S R hS hsupport hZ).toMeasure := by
  apply Measure.ext_of_singleton
  intro k
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton k),
    PMF.toMeasure_apply_singleton _ k (measurableSet_singleton k)]
  have hc : (fun x : ℝ => ⌊a + S * x⌋) ⁻¹' {k} = latticeSamplingCell a S k := by
    ext x
    exact (latticeSamplingCell_iff hS k).symm
  rw [hc, normalizedWeightHistogram_cell_mass ψ hψ hS hsupport]
  rfl

end Erdos3

end

end OAI
