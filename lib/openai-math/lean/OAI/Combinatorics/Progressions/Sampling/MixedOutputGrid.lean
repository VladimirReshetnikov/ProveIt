import Mathlib.MeasureTheory.Integral.Prod
import OAI.Combinatorics.Progressions.Estimates.SelectedOutputL1
import OAI.Combinatorics.Progressions.Lattices.LatticeDensityL1
import OAI.Combinatorics.Progressions.Probability.ObservedProductDensity

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem norm_masked_density_sum_sub_le {X : Type*} (s : Finset X)
    (a b mask : X → ℝ) (φ : X → ℂ) {G : ℝ} (_hG : 0 ≤ G)
    (hm : ∀ x ∈ s, |mask x| ≤ G) (hφ : ∀ x ∈ s, ‖φ x‖ ≤ 1) :
    ‖(∑ x ∈ s, ((mask x*a x : ℝ) : ℂ)*φ x)-
      (∑ x ∈ s, ((mask x*b x : ℝ) : ℂ)*φ x)‖ ≤ G*(∑ x ∈ s, |a x-b x|) := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro x hx
  have he : ((mask x*a x : ℝ) : ℂ)*φ x-((mask x*b x : ℝ) : ℂ)*φ x =
      ((mask x*(a x-b x) : ℝ) : ℂ)*φ x := by push_cast; ring
  rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  calc
    _ ≤ |mask x| * |a x-b x| * 1 := mul_le_mul_of_nonneg_left (hφ x hx) (by positivity)
    _ ≤ G*|a x-b x| := by rw [mul_one]; exact mul_le_mul_of_nonneg_right (hm x hx) (abs_nonneg _)

noncomputable def gridDensityTest {J : Type*} [Fintype J]
    (f : (J → ℝ) → ℝ) (a S : J → ℝ) (s : Finset (J → ℤ))
    (mask : (J → ℤ) → ℝ) (φ : (J → ℤ) → ℂ) : ℂ :=
  (∑ k ∈ s, ((mask k*f (rectangularLatticePoint a S k) : ℝ) : ℂ)*φ k) / ((∏ j, S j : ℝ) : ℂ)

theorem gridDensityTest_l1_bound {J : Type*} [Fintype J]
    (f g : (J → ℝ) → ℝ) {Kf Kg : ℝ≥0} (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (a S : J → ℝ) (hS : ∀ j, 0 < S j) {R δ G : ℝ}
    (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ j, 1/S j ≤ δ)
    (hfs : ∀ x, R < ‖x‖ → f x = 0) (hgs : ∀ x, R < ‖x‖ → g x = 0)
    (s : Finset (J → ℤ)) (mask : (J → ℤ) → ℝ) (φ : (J → ℤ) → ℂ)
    (hG : 0 ≤ G) (hm : ∀ k ∈ s, |mask k| ≤ G) (hφ : ∀ k ∈ s, ‖φ k‖ ≤ 1) :
    ‖gridDensityTest f a S s mask φ-gridDensityTest g a S s mask φ‖ ≤
      G*((∫ x, |f x-g x|)+(2*R+2)^Fintype.card J*((Kf : ℝ)+Kg)*δ) := by
  have hprod : 0 < ∏ j, S j := Finset.prod_pos (fun j _ => hS j)
  unfold gridDensityTest
  rw [← sub_div, norm_div, Complex.norm_real, Real.norm_of_nonneg hprod.le]
  calc
    _ ≤ (G*(∑ k ∈ s, |f (rectangularLatticePoint a S k)-g (rectangularLatticePoint a S k)|))/(∏ j, S j) :=
      div_le_div_of_nonneg_right (norm_masked_density_sum_sub_le s _ _ mask φ hG hm hφ) hprod.le
    _ = G*((∑ k ∈ s, |f (rectangularLatticePoint a S k)-g (rectangularLatticePoint a S k)|)/(∏ j, S j)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (rectangular_density_finite_l1_le f g hf hg a S hS hR hδ hδ1 hmesh hfs hgs s) hG

theorem gridDensityTest_error {J : Type*} [Fintype J]
    (f g : (J → ℝ) → ℝ) {Kf Kg : ℝ≥0} (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (a S : J → ℝ) (hS : ∀ j, 0 < S j) {R δ G ε : ℝ}
    (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ j, 1/S j ≤ δ)
    (hfs : ∀ x, R < ‖x‖ → f x = 0) (hgs : ∀ x, R < ‖x‖ → g x = 0)
    (s : Finset (J → ℤ)) (mask : (J → ℤ) → ℝ) (φ : (J → ℤ) → ℂ)
    (hG : 0 ≤ G) (hm : ∀ k ∈ s, |mask k| ≤ G) (hφ : ∀ k ∈ s, ‖φ k‖ ≤ 1)
    (he : (∫ x, |f x-g x|) ≤ ε) :
    ‖gridDensityTest f a S s mask φ-gridDensityTest g a S s mask φ‖ ≤
      G*(ε+(2*R+2)^Fintype.card J*((Kf : ℝ)+Kg)*δ) :=
  (gridDensityTest_l1_bound f g hf hg a S hS hR hδ hδ1 hmesh hfs hgs s mask φ hG hm hφ).trans
    (mul_le_mul_of_nonneg_left (add_le_add he le_rfl) hG)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem frozen_gridDensityTest_error {Z J : Type*} [Fintype Z] [Fintype J]
    (p : FiniteProbabilityWeights Z) (f g : Z → (J → ℝ) → ℝ)
    {Kf Kg : ℝ≥0}
    (hf : ∀ z, p.weight z ≠ 0 → LipschitzWith Kf (f z))
    (hg : ∀ z, p.weight z ≠ 0 → LipschitzWith Kg (g z))
    (a S : Z → J → ℝ) (hS : ∀ z j, 0 < S z j) {R δ G ε : ℝ}
    (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ z j, 1/S z j ≤ δ)
    (hfs : ∀ z, p.weight z ≠ 0 → ∀ x, R < ‖x‖ → f z x = 0)
    (hgs : ∀ z, p.weight z ≠ 0 → ∀ x, R < ‖x‖ → g z x = 0)
    (s : Z → Finset (J → ℤ)) (mask : Z → (J → ℤ) → ℝ) (φ : Z → (J → ℤ) → ℂ)
    (hG : 0 ≤ G)
    (hm : ∀ z, p.weight z ≠ 0 → ∀ k ∈ s z, |mask z k| ≤ G)
    (hφ : ∀ z, p.weight z ≠ 0 → ∀ k ∈ s z, ‖φ z k‖ ≤ 1)
    (he : p.mean (fun z => ∫ x, |f z x-g z x|) ≤ ε) :
    ‖p.complexMean (fun z => gridDensityTest (f z) (a z) (S z) (s z) (mask z) (φ z))-
      p.complexMean (fun z => gridDensityTest (g z) (a z) (S z) (s z) (mask z) (φ z))‖ ≤
      G*(ε+(2*R+2)^Fintype.card J*((Kf : ℝ)+Kg)*δ) := by
  let E := (2*R+2)^Fintype.card J*((Kf : ℝ)+Kg)*δ
  calc
    _ ≤ p.mean (fun z => G*((∫ x, |f z x-g z x|)+E)) :=
      p.norm_complexMean_sub_le _ _ _ (fun z hz => gridDensityTest_l1_bound
        (f z) (g z) (hf z hz) (hg z hz) (a z) (S z) (hS z) hR hδ hδ1 (hmesh z)
        (hfs z hz) (hgs z hz) (s z) (mask z) (φ z) hG (hm z hz) (hφ z hz))
    _ = G*(p.mean (fun z => ∫ x, |f z x-g z x|)+E) := by
      rw [p.mean_const_mul, p.mean_add, p.mean_const]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add he le_rfl) hG

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {Q : Type*} [Fintype Q] (I : Q → Type*) [∀ q, Fintype (I q)]

theorem sigmaAxisCoordinates_norm (v : (Σ q, I q) → ℝ) :
    ‖sigmaAxisCoordinates I v‖ = ‖v‖ := by
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
      (fun q => sigmaAxisProjection_norm_apply_le I q v)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg (sigmaAxisCoordinates I v))).mpr
    intro a
    exact (norm_le_pi_norm (sigmaAxisCoordinates I v a.1) a.2).trans
      (norm_le_pi_norm (sigmaAxisCoordinates I v) a.1)

theorem sigmaAxisCoordinates_lipschitz : LipschitzWith 1 (sigmaAxisCoordinates I) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  simp only [NNReal.coe_one, one_mul, dist_eq_norm, ← map_sub, sigmaAxisCoordinates_norm]
  exact le_rfl

theorem grouped_gridDensityTest_error
    (f g : (∀ q, I q → ℝ) → ℝ) {Kf Kg : ℝ≥0} (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (a S : (Σ q, I q) → ℝ) (hS : ∀ j, 0 < S j) {R δ G ε : ℝ}
    (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ j, 1/S j ≤ δ)
    (hfs : ∀ v, R < ‖v‖ → f v = 0) (hgs : ∀ v, R < ‖v‖ → g v = 0)
    (s : Finset ((Σ q, I q) → ℤ)) (mask : ((Σ q, I q) → ℤ) → ℝ)
    (φ : ((Σ q, I q) → ℤ) → ℂ) (hG : 0 ≤ G)
    (hm : ∀ k ∈ s, |mask k| ≤ G) (hφ : ∀ k ∈ s, ‖φ k‖ ≤ 1)
    (he : (∫ v, |f v-g v|) ≤ ε) :
    ‖gridDensityTest (f ∘ sigmaAxisCoordinates I) a S s mask φ-
      gridDensityTest (g ∘ sigmaAxisCoordinates I) a S s mask φ‖ ≤
      G*(ε+(2*R+2)^Fintype.card (Σ q, I q)*((Kf : ℝ)+Kg)*δ) := by
  apply gridDensityTest_error (f ∘ sigmaAxisCoordinates I) (g ∘ sigmaAxisCoordinates I)
    (by simpa only [mul_one] using hf.comp (sigmaAxisCoordinates_lipschitz I))
    (by simpa only [mul_one] using hg.comp (sigmaAxisCoordinates_lipschitz I))
    a S hS hR hδ hδ1 hmesh
    (fun v hv => hfs _ (by simpa only [sigmaAxisCoordinates_norm] using hv))
    (fun v hv => hgs _ (by simpa only [sigmaAxisCoordinates_norm] using hv))
    s mask φ hG hm hφ
  have hi := (sigmaAxisCoordinates_measurePreserving I).integral_comp
    (sigmaAxisCoordinates I).toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (fun v => |f v-g v|)
  exact hi.trans_le he

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem sliced_gridDensityTest_error {Z J : Type*} [MeasurableSpace Z] [Fintype J]
    (μ : Measure Z) [IsFiniteMeasure μ] (f g : Z → (J → ℝ) → ℝ)
    {Kf Kg : ℝ≥0} (hf : ∀ z, LipschitzWith Kf (f z)) (hg : ∀ z, LipschitzWith Kg (g z))
    (a S : J → ℝ) (hS : ∀ j, 0 < S j) {R δ G ε : ℝ}
    (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ j, 1/S j ≤ δ)
    (hfs : ∀ z x, R < ‖x‖ → f z x = 0) (hgs : ∀ z x, R < ‖x‖ → g z x = 0)
    (s : Finset (J → ℤ)) (mask : Z → (J → ℤ) → ℝ) (φ : Z → (J → ℤ) → ℂ)
    (hG : 0 ≤ G) (hm : ∀ z k, k ∈ s → |mask z k| ≤ G) (hφ : ∀ z k, k ∈ s → ‖φ z k‖ ≤ 1)
    (hL : Integrable (fun z => ∫ x, |f z x-g z x|) μ)
    (he : (∫ z, (∫ x, |f z x-g z x|) ∂μ) ≤ ε) :
    ‖∫ z, gridDensityTest (f z) a S s (mask z) (φ z)-gridDensityTest (g z) a S s (mask z) (φ z) ∂μ‖ ≤
      G*(ε+μ.real Set.univ*((2*R+2)^Fintype.card J*((Kf : ℝ)+Kg)*δ)) := by
  let E := (2*R+2)^Fintype.card J*((Kf : ℝ)+Kg)*δ
  have hi : Integrable (fun z => G*((∫ x, |f z x-g z x|)+E)) μ :=
    (hL.add (integrable_const E)).const_mul G
  calc
    _ ≤ ∫ z, ‖gridDensityTest (f z) a S s (mask z) (φ z)-gridDensityTest (g z) a S s (mask z) (φ z)‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ z, G*((∫ x, |f z x-g z x|)+E) ∂μ :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) hi
        (Filter.Eventually.of_forall (fun z => gridDensityTest_l1_bound (f z) (g z) (hf z) (hg z)
          a S hS hR hδ hδ1 hmesh (hfs z) (hgs z) s (mask z) (φ z) hG (hm z) (hφ z)))
    _ = G*((∫ z, (∫ x, |f z x-g z x|) ∂μ)+μ.real Set.univ*E) := by
      rw [integral_const_mul, integral_add hL (integrable_const E), integral_const, smul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add he le_rfl) hG

theorem partial_gridDensityTest_error {Z J : Type*} [MeasurableSpace Z] [Fintype J]
    (μ : Measure Z) [IsFiniteMeasure μ] (f g : Z → (J → ℝ) → ℝ)
    {Kf Kg : ℝ≥0} (hf : ∀ z, LipschitzWith Kf (f z)) (hg : ∀ z, LipschitzWith Kg (g z))
    (a S : J → ℝ) (hS : ∀ j, 0 < S j) {R δ G ε : ℝ}
    (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ j, 1/S j ≤ δ)
    (hfs : ∀ z x, R < ‖x‖ → f z x = 0) (hgs : ∀ z x, R < ‖x‖ → g z x = 0)
    (s : Finset (J → ℤ)) (mask : Z → (J → ℤ) → ℝ) (φ : Z → (J → ℤ) → ℂ)
    (hG : 0 ≤ G) (hm : ∀ z k, k ∈ s → |mask z k| ≤ G) (hφ : ∀ z k, k ∈ s → ‖φ z k‖ ≤ 1)
    (hfg : Integrable (fun p : Z × (J → ℝ) => f p.1 p.2-g p.1 p.2) (μ.prod volume))
    (he : (∫ p : Z × (J → ℝ), |f p.1 p.2-g p.1 p.2| ∂μ.prod volume) ≤ ε) :
    ‖∫ z, gridDensityTest (f z) a S s (mask z) (φ z)-gridDensityTest (g z) a S s (mask z) (φ z) ∂μ‖ ≤
      G*(ε+μ.real Set.univ*((2*R+2)^Fintype.card J*((Kf : ℝ)+Kg)*δ)) := by
  have habs : Integrable (fun p : Z × (J → ℝ) => |f p.1 p.2-g p.1 p.2|) (μ.prod volume) := by
    simpa only [Real.norm_eq_abs] using hfg.norm
  apply sliced_gridDensityTest_error μ f g hf hg a S hS hR hδ hδ1 hmesh hfs hgs s mask φ hG hm hφ
    habs.integral_prod_left
  rw [← integral_prod _ habs]
  exact he

end Erdos3

end

section

namespace Erdos3

open scoped NNReal BigOperators

theorem FiniteProbabilityWeights.mean_lipschitz {Ω X : Type*} [Fintype Ω] [PseudoMetricSpace X]
    (p : FiniteProbabilityWeights Ω) (f : Ω → X → ℝ) {K : ℝ≥0}
    (hf : ∀ a, p.weight a ≠ 0 → LipschitzWith K (f a)) :
    LipschitzWith K (fun x => p.mean (fun a => f a x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, ← p.mean_sub]
  apply p.abs_mean_le_on_support
  intro a ha
  exact (hf a ha).dist_le_mul x y

theorem gridDensityTest_mean {Ω J : Type*} [Fintype Ω] [Fintype J]
    (p : FiniteProbabilityWeights Ω) (f : Ω → (J → ℝ) → ℝ)
    (a S : J → ℝ) (s : Finset (J → ℤ)) (mask : (J → ℤ) → ℝ) (φ : (J → ℤ) → ℂ) :
    gridDensityTest (fun x => p.mean (fun t => f t x)) a S s mask φ =
      p.complexMean (fun t => gridDensityTest (f t) a S s mask φ) := by
  unfold gridDensityTest FiniteProbabilityWeights.complexMean FiniteProbabilityWeights.mean
  simp only [Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul,
    Finset.sum_div, mul_div_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro k _
  ring

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem partial_gridDensityTest_error_ae {Z J : Type*} [MeasurableSpace Z] [Fintype J]
    (μ : Measure Z) [IsFiniteMeasure μ] (f g : Z → (J → ℝ) → ℝ)
    {Kf Kg : ℝ≥0} (a S : J → ℝ) (hS : ∀ j, 0 < S j) {R δ G ε : ℝ}
    (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ j, 1/S j ≤ δ)
    (hgood : ∀ᵐ z ∂μ, LipschitzWith Kf (f z) ∧ LipschitzWith Kg (g z) ∧
      (∀ x, R < ‖x‖ → f z x = 0) ∧ (∀ x, R < ‖x‖ → g z x = 0))
    (s : Finset (J → ℤ)) (mask : Z → (J → ℤ) → ℝ) (φ : Z → (J → ℤ) → ℂ)
    (hG : 0 ≤ G) (hm : ∀ z k, k ∈ s → |mask z k| ≤ G) (hφ : ∀ z k, k ∈ s → ‖φ z k‖ ≤ 1)
    (hfg : Integrable (fun p : Z × (J → ℝ) => f p.1 p.2-g p.1 p.2) (μ.prod volume))
    (he : (∫ p : Z × (J → ℝ), |f p.1 p.2-g p.1 p.2| ∂μ.prod volume) ≤ ε) :
    ‖∫ z, gridDensityTest (f z) a S s (mask z) (φ z)-gridDensityTest (g z) a S s (mask z) (φ z) ∂μ‖ ≤
      G*(ε+μ.real Set.univ*((2*R+2)^Fintype.card J*((Kf : ℝ)+Kg)*δ)) := by
  let E := (2*R+2)^Fintype.card J*((Kf : ℝ)+Kg)*δ
  have habs : Integrable (fun p : Z × (J → ℝ) => |f p.1 p.2-g p.1 p.2|) (μ.prod volume) := by
    simpa only [Real.norm_eq_abs] using hfg.norm
  have hL := habs.integral_prod_left
  have hi : Integrable (fun z => G*((∫ x, |f z x-g z x|)+E)) μ :=
    (hL.add (integrable_const E)).const_mul G
  have hiter : (∫ z, (∫ x, |f z x-g z x|) ∂μ) ≤ ε := by
    rw [← integral_prod _ habs]
    exact he
  calc
    _ ≤ ∫ z, ‖gridDensityTest (f z) a S s (mask z) (φ z)-gridDensityTest (g z) a S s (mask z) (φ z)‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ z, G*((∫ x, |f z x-g z x|)+E) ∂μ := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) hi
      filter_upwards [hgood] with z hz
      exact gridDensityTest_l1_bound (f z) (g z) hz.1 hz.2.1 a S hS hR hδ hδ1 hmesh
        hz.2.2.1 hz.2.2.2 s (mask z) (φ z) hG (hm z) (hφ z)
    _ = G*((∫ z, (∫ x, |f z x-g z x|) ∂μ)+μ.real Set.univ*E) := by
      rw [integral_const_mul, integral_add hL (integrable_const E), integral_const, smul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hiter le_rfl) hG

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem finiteSource_gridDensityTest_error {Ω T J : Type*} [Fintype Ω]
    [MeasurableSpace T] [Fintype J]
    (p : FiniteProbabilityWeights Ω) (F : Ω → T) (μ : Measure T) [IsProbabilityMeasure μ]
    (U : Set T) (hF : ∀ a, F a ∈ U) (hμ : ∀ᵐ t ∂μ, t ∈ U)
    (ρ : T → (J → ℝ) → ℝ) (hρ : Measurable (Function.uncurry ρ))
    (H K : ℝ≥0) (hcap : ∀ t ∈ U, ∀ v, ρ t v ∈ Set.Icc (0 : ℝ) H)
    (hlip : ∀ t ∈ U, LipschitzWith K (ρ t))
    (a S : J → ℝ) (hS : ∀ j, 0 < S j) {R δ G ε : ℝ}
    (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ j, 1 / S j ≤ δ)
    (hs : ∀ t ∈ U, ∀ v, R < ‖v‖ → ρ t v = 0)
    (s : Finset (J → ℤ)) (mask : (J → ℤ) → ℝ) (φ : (J → ℤ) → ℂ)
    (hG : 0 ≤ G) (hm : ∀ k ∈ s, |mask k| ≤ G) (hφ : ∀ k ∈ s, ‖φ k‖ ≤ 1)
    (he : (∫ v, |p.mean (fun t => ρ (F t) v) - densityMixture μ ρ v|) ≤ ε) :
    ‖p.complexMean (fun t => gridDensityTest (ρ (F t)) a S s mask φ) -
      gridDensityTest (densityMixture μ ρ) a S s mask φ‖ ≤
        G * (ε + (2 * R + 2)^Fintype.card J * ((K : ℝ) + K) * δ) := by
  have hmean := p.mean_lipschitz (fun t => ρ (F t)) (fun t _ => hlip _ (hF t))
  have hmix := densityMixture_uniform_bound μ ρ H K
    (fun v => (hρ.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
    (hμ.mono (fun t ht => ⟨hcap t ht, hlip t ht⟩))
  have hfs (v) (hv : R < ‖v‖) : p.mean (fun t => ρ (F t) v) = 0 := by
    have hz : (fun t => ρ (F t) v) = fun _ => 0 := funext (fun t => hs _ (hF t) v hv)
    rw [hz, p.mean_const]
  have hgs (v) (hv : R < ‖v‖) : densityMixture μ ρ v = 0 :=
    integral_eq_zero_of_ae (hμ.mono (fun t ht => hs t ht v hv))
  rw [← gridDensityTest_mean]
  exact gridDensityTest_error _ _ hmean hmix.2 a S hS hR hδ hδ1 hmesh hfs hgs
    s mask φ hG hm hφ he

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem partial_gridDensityTest_family_error_ae {Z J : Type*} [MeasurableSpace Z] [Fintype J]
    (μ : Measure Z) [IsFiniteMeasure μ] (f g : Z → (J → ℝ) → ℝ)
    {Kf Kg : ℝ≥0} (a S : Z → J → ℝ) (hS : ∀ z j, 0 < S z j) {R δ G ε : ℝ}
    (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ z j, 1/S z j ≤ δ)
    (hgood : ∀ᵐ z ∂μ, LipschitzWith Kf (f z) ∧ LipschitzWith Kg (g z) ∧
      (∀ x, R < ‖x‖ → f z x = 0) ∧ (∀ x, R < ‖x‖ → g z x = 0))
    (s : Z → Finset (J → ℤ)) (mask : Z → (J → ℤ) → ℝ) (φ : Z → (J → ℤ) → ℂ)
    (hG : 0 ≤ G) (hm : ∀ z k, k ∈ s z → |mask z k| ≤ G) (hφ : ∀ z k, k ∈ s z → ‖φ z k‖ ≤ 1)
    (hfg : Integrable (fun p : Z × (J → ℝ) => f p.1 p.2-g p.1 p.2) (μ.prod volume))
    (he : (∫ p : Z × (J → ℝ), |f p.1 p.2-g p.1 p.2| ∂μ.prod volume) ≤ ε) :
    ‖∫ z, gridDensityTest (f z) (a z) (S z) (s z) (mask z) (φ z)-gridDensityTest (g z) (a z) (S z) (s z) (mask z) (φ z) ∂μ‖ ≤
      G*(ε+μ.real Set.univ*((2*R+2)^Fintype.card J*((Kf : ℝ)+Kg)*δ)) := by
  let E := (2*R+2)^Fintype.card J*((Kf : ℝ)+Kg)*δ
  have habs : Integrable (fun p : Z × (J → ℝ) => |f p.1 p.2-g p.1 p.2|) (μ.prod volume) := by
    simpa only [Real.norm_eq_abs] using hfg.norm
  have hL := habs.integral_prod_left
  have hi : Integrable (fun z => G*((∫ x, |f z x-g z x|)+E)) μ :=
    (hL.add (integrable_const E)).const_mul G
  have hiter : (∫ z, (∫ x, |f z x-g z x|) ∂μ) ≤ ε := by
    rw [← integral_prod _ habs]
    exact he
  calc
    _ ≤ ∫ z, ‖gridDensityTest (f z) (a z) (S z) (s z) (mask z) (φ z)-gridDensityTest (g z) (a z) (S z) (s z) (mask z) (φ z)‖ ∂μ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ z, G*((∫ x, |f z x-g z x|)+E) ∂μ := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) hi
      filter_upwards [hgood] with z hz
      exact gridDensityTest_l1_bound (f z) (g z) hz.1 hz.2.1 (a z) (S z) (hS z) hR hδ hδ1 (hmesh z)
        hz.2.2.1 hz.2.2.2 (s z) (mask z) (φ z) hG (hm z) (hφ z)
    _ = G*((∫ z, (∫ x, |f z x-g z x|) ∂μ)+μ.real Set.univ*E) := by
      rw [integral_const_mul, integral_add hL (integrable_const E), integral_const, smul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hiter le_rfl) hG

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem image_comparison_on_output_grid {Ω J : Type*} [MeasurableSpace Ω] [Fintype J]
    (μ : Measure Ω) (U V : Ω → (J → ℝ)) (hU : Measurable U) (hV : Measurable V)
    (f g : (J → ℝ) → ℝ) {Kf Kg : ℝ≥0} (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hUf : μ.map U = realDensityMeasure volume f) (hVg : μ.map V = realDensityMeasure volume g)
    {ε : ℝ} (he : ∀ φ : (J → ℝ) → ℝ, Measurable φ → (∀ x, ‖φ x‖ ≤ 1) →
      |mappedTest μ U φ-mappedTest μ V φ| ≤ ε)
    (a S : J → ℝ) (hS : ∀ j, 0 < S j) {R δ G : ℝ}
    (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ j, 1/S j ≤ δ)
    (hfs : ∀ x, R < ‖x‖ → f x = 0) (hgs : ∀ x, R < ‖x‖ → g x = 0)
    (s : Finset (J → ℤ)) (mask : (J → ℤ) → ℝ) (φ : (J → ℤ) → ℂ)
    (hG : 0 ≤ G) (hm : ∀ k ∈ s, |mask k| ≤ G) (hφ : ∀ k ∈ s, ‖φ k‖ ≤ 1) :
    ‖gridDensityTest f a S s mask φ-gridDensityTest g a S s mask φ‖ ≤
      G*(ε+(2*R+2)^Fintype.card J*((Kf : ℝ)+Kg)*δ) := by
  apply gridDensityTest_error f g hf hg a S hS hR hδ hδ1 hmesh hfs hgs s mask φ hG hm hφ
  exact imageComparison_density_l1 μ volume U V hU hV f g hf.continuous.measurable hg.continuous.measurable
    (compactBox_integrable f hf.continuous R hfs) (compactBox_integrable g hg.continuous R hgs)
    hf0 hg0 hUf hVg he

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

theorem partial_image_comparison_on_output_grid {Ω Z J : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Z] [Fintype J]
    (μ : Measure Ω) (ν : Measure Z) [IsFiniteMeasure ν]
    (U V : Ω → Z × (J → ℝ)) (hU : Measurable U) (hV : Measurable V)
    (f g : Z → (J → ℝ) → ℝ)
    (hfm : Measurable (Function.uncurry f)) (hgm : Measurable (Function.uncurry g))
    (hfi : Integrable (Function.uncurry f) (ν.prod volume))
    (hgi : Integrable (Function.uncurry g) (ν.prod volume))
    (hf0 : ∀ z x, 0 ≤ f z x) (hg0 : ∀ z x, 0 ≤ g z x)
    (hUf : μ.map U = realDensityMeasure (ν.prod volume) (Function.uncurry f))
    (hVg : μ.map V = realDensityMeasure (ν.prod volume) (Function.uncurry g))
    {ε : ℝ} (he : ∀ φ : Z × (J → ℝ) → ℝ, Measurable φ → (∀ x, ‖φ x‖ ≤ 1) →
      |mappedTest μ U φ-mappedTest μ V φ| ≤ ε)
    {Kf Kg : ℝ≥0} (hf : ∀ z, LipschitzWith Kf (f z)) (hg : ∀ z, LipschitzWith Kg (g z))
    (a S : J → ℝ) (hS : ∀ j, 0 < S j) {R δ G : ℝ}
    (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ j, 1/S j ≤ δ)
    (hfs : ∀ z x, R < ‖x‖ → f z x = 0) (hgs : ∀ z x, R < ‖x‖ → g z x = 0)
    (s : Finset (J → ℤ)) (mask : Z → (J → ℤ) → ℝ) (φ : Z → (J → ℤ) → ℂ)
    (hG : 0 ≤ G) (hm : ∀ z k, k ∈ s → |mask z k| ≤ G) (hφ : ∀ z k, k ∈ s → ‖φ z k‖ ≤ 1) :
    ‖∫ z, gridDensityTest (f z) a S s (mask z) (φ z)-gridDensityTest (g z) a S s (mask z) (φ z) ∂ν‖ ≤
      G*(ε+ν.real Set.univ*((2*R+2)^Fintype.card J*((Kf : ℝ)+Kg)*δ)) := by
  apply partial_gridDensityTest_error ν f g hf hg a S hS hR hδ hδ1 hmesh hfs hgs s mask φ hG hm hφ
    (hfi.sub hgi)
  exact imageComparison_density_l1 μ (ν.prod volume) U V hU hV (Function.uncurry f) (Function.uncurry g)
    hfm hgm hfi hgi (fun p => hf0 p.1 p.2) (fun p => hg0 p.1 p.2) hUf hVg he

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem mixed_output_grid_error {W I J : Type*} [MeasurableSpace W]
    [Fintype I] [Fintype J] (select : J ↪ I) (μ : Measure W) [IsProbabilityMeasure μ]
    (f g : W → (I → ℝ) → ℝ) {Kf Kg : ℝ≥0} (R : ℝ≥0)
    (hgood : ∀ᵐ w ∂μ, LipschitzWith Kf (f w) ∧ LipschitzWith Kg (g w) ∧
      (∀ v, (R : ℝ) < ‖v‖ → f w v = 0) ∧ (∀ v, (R : ℝ) < ‖v‖ → g w v = 0))
    (hfg : Integrable (fun p : W × (I → ℝ) => f p.1 p.2-g p.1 p.2) (μ.prod volume))
    {ε : ℝ} (he : (∫ p : W × (I → ℝ), |f p.1 p.2-g p.1 p.2| ∂μ.prod volume) ≤ ε)
    (a S : W × (UnselectedColumn select → ℝ) → J → ℝ)
    (hS : ∀ p j, 0 < S p j) {mesh M : ℝ}
    (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1) (hmesh : ∀ p j, 1/S p j ≤ mesh)
    (grid : W × (UnselectedColumn select → ℝ) → Finset (J → ℤ)) (mask : W × (UnselectedColumn select → ℝ) → (J → ℤ) → ℝ)
    (φ : W × (UnselectedColumn select → ℝ) → (J → ℤ) → ℂ)
    (hM : 0 ≤ M) (hmask : ∀ p k, k ∈ grid p → |mask p k| ≤ M)
    (hφ : ∀ p k, k ∈ grid p → ‖φ p k‖ ≤ 1) :
    ‖∫ p : W × (UnselectedColumn select → ℝ),
      gridDensityTest (selectedOutputSlice select (f p.1) p.2) (a p) (S p) (grid p) (mask p) (φ p)-
      gridDensityTest (selectedOutputSlice select (g p.1) p.2) (a p) (S p) (grid p) (mask p) (φ p) ∂μ.prod volume‖ ≤
      M*(ε+(2*(R : ℝ))^Fintype.card (UnselectedColumn select)*
        ((2*(R : ℝ)+2)^Fintype.card J*((Kf : ℝ)+Kg)*mesh)) := by
  let ν := μ.prod (continuousOutputBoxMeasure (UnselectedColumn select) R)
  let F := fun p : W × (UnselectedColumn select → ℝ) => selectedOutputSlice select (f p.1) p.2
  let G := fun p : W × (UnselectedColumn select → ℝ) => selectedOutputSlice select (g p.1) p.2
  let test := fun p => gridDensityTest (F p) (a p) (S p) (grid p) (mask p) (φ p)-
    gridDensityTest (G p) (a p) (S p) (grid p) (mask p) (φ p)
  have hsplit := selectedOutput_restricted_l1 select μ R
    (fun p => f p.1 p.2-g p.1 p.2) hfg he
  have hs : ∀ᵐ p ∂ν, LipschitzWith Kf (F p) ∧ LipschitzWith Kg (G p) ∧
      (∀ y, (R : ℝ) < ‖y‖ → F p y = 0) ∧ (∀ y, (R : ℝ) < ‖y‖ → G p y = 0) := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hgood] with p hp
    exact ⟨selectedOutputSlice_lipschitz select hp.1 p.2,
      selectedOutputSlice_lipschitz select hp.2.1 p.2,
      selectedOutputSlice_support_right select hp.2.2.1 p.2,
      selectedOutputSlice_support_right select hp.2.2.2 p.2⟩
  have hbound := partial_gridDensityTest_family_error_ae ν F G a S hS R.coe_nonneg
    hmesh0 hmesh1 hmesh hs grid mask φ hM hmask hφ hsplit.1 hsplit.2
  have hrestrict : (∫ p, test p ∂ν) = ∫ p, test p ∂μ.prod volume := by
    change (∫ p, test p ∂μ.prod (continuousOutputBoxMeasure (UnselectedColumn select) R)) = _
    rw [continuousOutputBoxMeasure_prod]
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hgood] with p hp
    intro hout
    have hx : (R : ℝ) < ‖p.2‖ := lt_of_not_ge (fun hx => hout
      ⟨Set.mem_univ _, (continuousOutputBox_mem_iff R p.2).mpr hx⟩)
    have hF : F p = 0 := funext (fun y => selectedOutputSlice_support_left select hp.2.2.1 p.2 y hx)
    have hG : G p = 0 := funext (fun y => selectedOutputSlice_support_left select hp.2.2.2 p.2 y hx)
    simp only [test, hF, hG, sub_self]
  change ‖∫ p, test p ∂μ.prod volume‖ ≤ _
  rw [← hrestrict]
  simpa only [ν, continuousOutputBoxMeasure_prod_mass] using hbound

end Erdos3

end

end OAI
