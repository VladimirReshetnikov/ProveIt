import OAI.Combinatorics.Progressions.Lattices.ResidueCoefficientFamily
import OAI.Combinatorics.Progressions.Probability.CoefficientDeckDensityLawCongruence
import OAI.Combinatorics.Progressions.Probability.SmallTensorDensityError

namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem integrable_snd_probability {Z X : Type*}
    [MeasurableSpace Z] [MeasurableSpace X]
    (μ : Measure Z) [IsProbabilityMeasure μ] (ν : Measure X) [SigmaFinite ν]
    (f : X → ℝ) (hf : Integrable f ν) :
    Integrable (fun x : Z × X => f x.2) (μ.prod ν) := by
  simpa only [one_mul] using
    (integrable_const (1 : ℝ) : Integrable (fun _ : Z => (1 : ℝ)) μ).mul_prod hf

theorem integral_snd_probability {Z X : Type*}
    [MeasurableSpace Z] [MeasurableSpace X]
    (μ : Measure Z) [IsProbabilityMeasure μ] (ν : Measure X) [SigmaFinite ν]
    (f : X → ℝ) (hf : Integrable f ν) :
    (∫ x : Z × X, f x.2 ∂μ.prod ν) = ∫ x, f x ∂ν := by
  rw [integral_prod _ (integrable_snd_probability μ ν f hf)]
  simp

theorem retained_density_test_error {Z X Y : Type*}
    [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure Z) [IsProbabilityMeasure μ] (ν : Measure X) [SigmaFinite ν]
    (f g : X → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable f ν) (hgi : Integrable g ν)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (T : Z × X → Y) (hT : Measurable T) (φ : Y → ℝ) (hφ : Measurable φ)
    {B : ℝ} (hb : ∀ y, ‖φ y‖ ≤ B) :
    |(∫ y, φ y ∂(μ.prod (realDensityMeasure ν f)).map T) -
      ∫ y, φ y ∂(μ.prod (realDensityMeasure ν g)).map T| ≤
      B * ∫ x, |f x - g x| ∂ν := by
  rw [integral_map hT.aemeasurable hφ.aestronglyMeasurable,
    integral_map hT.aemeasurable hφ.aestronglyMeasurable,
    realDensityMeasure_prod_right μ ν f hf,
    realDensityMeasure_prod_right μ ν g hg,
    realDensityMeasure_integral (μ.prod ν) (fun x : Z × X => f x.2)
      (hf.comp measurable_snd) (fun x => hf0 x.2),
    realDensityMeasure_integral (μ.prod ν) (fun x : Z × X => g x.2)
      (hg.comp measurable_snd) (fun x => hg0 x.2)]
  have he := density_bounded_test_error (μ.prod ν)
    (fun x => f x.2) (fun x => g x.2)
    (integrable_snd_probability μ ν f hfi) (integrable_snd_probability μ ν g hgi)
    (fun x => φ (T x)) (hφ.comp hT) (fun x => hb (T x))
  rwa [integral_snd_probability μ ν (fun x => |f x - g x|) (hfi.sub hgi).abs] at he

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem pmf_real_integral_count {X : Type*} [Countable X]
    [MeasurableSpace X] [MeasurableSingletonClass X] (p : PMF X) :
    (∫ x, (p x).toReal ∂Measure.count) = 1 := by
  rw [integral_countable (pmf_real_integrable p)]
  simpa only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]
    using pmf_real_mass p

theorem independentPMF_count_density {I : Type*} [Fintype I]
    {X : I → Type*} [∀ i, Countable (X i)]
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]
    (p : ∀ i, PMF (X i)) :
    Measure.pi (fun i => (p i).toMeasure) =
      realDensityMeasure (Measure.pi (fun i => (Measure.count : Measure (X i))))
        (fun x => ∏ i, (p i (x i)).toReal) := by
  simp_rw [pmf_realDensity_count]
  exact realDensityMeasure_pi (fun i => (Measure.count : Measure (X i)))
    (fun i x => (p i x).toReal) (fun i => pmf_real_integrable (p i))
    (fun _ _ => ENNReal.toReal_nonneg)

theorem independentPMF_retained_grid_error {I Z Y : Type*} [Fintype I]
    {X : I → Type*} [∀ i, Countable (X i)]
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]
    [MeasurableSpace Z] [MeasurableSpace Y]
    (μ : Measure Z) [IsProbabilityMeasure μ]
    (p : ∀ i, PMF (X i)) (g : ∀ i, X i → ℝ)
    (hg : ∀ i, Integrable (g i) Measure.count) (hg0 : ∀ i x, 0 ≤ g i x)
    (ε : I → ℝ)
    (he : ∀ i, (∫ x, |(p i x).toReal - g i x| ∂Measure.count) ≤ ε i)
    (hsmall : (∑ i, ε i) ≤ 1)
    (T : Z × (∀ i, X i) → Y) (hT : Measurable T)
    (φ : Y → ℝ) (hφ : Measurable φ) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ y, ‖φ y‖ ≤ B) :
    |(∫ y, φ y ∂(μ.prod (Measure.pi (fun i => (p i).toMeasure))).map T) -
      ∫ y, φ y ∂(μ.prod (realDensityMeasure
        (Measure.pi (fun i => (Measure.count : Measure (X i))))
        (fun x => ∏ i, g i (x i)))).map T| ≤ B * (2 * ∑ i, ε i) := by
  rw [independentPMF_count_density p]
  have hfm (i) : Measurable (fun x => (p i x).toReal) := measurable_of_countable _
  have hgm (i) : Measurable (g i) := measurable_of_countable _
  have ht := retained_density_test_error μ
    (Measure.pi (fun i => (Measure.count : Measure (X i))))
    (fun x => ∏ i, (p i (x i)).toReal) (fun x => ∏ i, g i (x i))
    (Finset.measurable_prod _ (fun i _ => (hfm i).comp (measurable_pi_apply i)))
    (Finset.measurable_prod _ (fun i _ => (hgm i).comp (measurable_pi_apply i)))
    (Integrable.fintype_prod_dep (fun i => pmf_real_integrable (p i)))
    (Integrable.fintype_prod_dep hg)
    (fun x => Finset.prod_nonneg (fun _ _ => ENNReal.toReal_nonneg))
    (fun x => Finset.prod_nonneg (fun i _ => hg0 i (x i))) T hT φ hφ hb
  exact ht.trans (mul_le_mul_of_nonneg_left
    (tensor_density_l1_le_twice_sum (fun i => (Measure.count : Measure (X i)))
      (fun i x => (p i x).toReal) g (fun i => pmf_real_integrable (p i)) hg
      (fun _ _ => ENNReal.toReal_nonneg) hg0
      (fun i => pmf_real_integral_count (p i)) ε he hsmall) hB)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem realDensityMeasure_integral_complex {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (φ : X → ℂ) :
    (∫ x, φ x ∂realDensityMeasure μ f) = ∫ x, (f x : ℂ) * φ x ∂μ := by
  unfold realDensityMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hf0 _), Complex.real_smul]

theorem density_bounded_complex_test_error {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f g : X → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (φ : X → ℂ) (hφ : Measurable φ) {B : ℝ} (hb : ∀ x, ‖φ x‖ ≤ B) :
    ‖(∫ x, (f x : ℂ) * φ x ∂μ) - ∫ x, (g x : ℂ) * φ x ∂μ‖ ≤
      B * ∫ x, |f x - g x| ∂μ := by
  have hfi : Integrable (fun x => (f x : ℂ) * φ x) μ :=
    hf.ofReal.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  have hgi : Integrable (fun x => (g x : ℂ) * φ x) μ :=
    hg.ofReal.mul_bdd hφ.aestronglyMeasurable (Filter.Eventually.of_forall hb)
  rw [← integral_sub hfi hgi]
  refine (norm_integral_le_integral_norm _).trans ?_
  calc
    _ ≤ ∫ x, B * |f x - g x| ∂μ := by
      apply integral_mono (hfi.sub hgi).norm ((hf.sub hg).abs.const_mul B)
      intro x
      change ‖(f x : ℂ) * φ x - (g x : ℂ) * φ x‖ ≤ B * |f x - g x|
      rw [← sub_mul, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      simpa only [mul_comm B] using mul_le_mul_of_nonneg_left (hb x) (abs_nonneg (f x - g x))
    _ = _ := integral_const_mul _ _

theorem retained_density_complex_test_error {Z X Y : Type*}
    [MeasurableSpace Z] [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure Z) [IsProbabilityMeasure μ] (ν : Measure X) [SigmaFinite ν]
    (f g : X → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hfi : Integrable f ν) (hgi : Integrable g ν)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (T : Z × X → Y) (hT : Measurable T) (φ : Y → ℂ) (hφ : Measurable φ)
    {B : ℝ} (hb : ∀ y, ‖φ y‖ ≤ B) :
    ‖(∫ y, φ y ∂(μ.prod (realDensityMeasure ν f)).map T) -
      ∫ y, φ y ∂(μ.prod (realDensityMeasure ν g)).map T‖ ≤ B * ∫ x, |f x - g x| ∂ν := by
  rw [integral_map hT.aemeasurable hφ.aestronglyMeasurable,
    integral_map hT.aemeasurable hφ.aestronglyMeasurable,
    realDensityMeasure_prod_right μ ν f hf, realDensityMeasure_prod_right μ ν g hg,
    realDensityMeasure_integral_complex (μ.prod ν) (fun x : Z × X => f x.2)
      (hf.comp measurable_snd) (fun x => hf0 x.2),
    realDensityMeasure_integral_complex (μ.prod ν) (fun x : Z × X => g x.2)
      (hg.comp measurable_snd) (fun x => hg0 x.2)]
  have he := density_bounded_complex_test_error (μ.prod ν) (fun x => f x.2) (fun x => g x.2)
    (integrable_snd_probability μ ν f hfi) (integrable_snd_probability μ ν g hgi)
    (fun x => φ (T x)) (hφ.comp hT) (fun x => hb (T x))
  rwa [integral_snd_probability μ ν (fun x => |f x - g x|) (hfi.sub hgi).abs] at he

theorem independentPMF_retained_complex_grid_error {I Z Y : Type*} [Fintype I]
    {X : I → Type*} [∀ i, Countable (X i)]
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]
    [MeasurableSpace Z] [MeasurableSpace Y]
    (μ : Measure Z) [IsProbabilityMeasure μ] (p : ∀ i, PMF (X i)) (g : ∀ i, X i → ℝ)
    (hg : ∀ i, Integrable (g i) Measure.count) (hg0 : ∀ i x, 0 ≤ g i x)
    (ε : I → ℝ) (he : ∀ i, (∫ x, |(p i x).toReal - g i x| ∂Measure.count) ≤ ε i)
    (hsmall : (∑ i, ε i) ≤ 1) (T : Z × (∀ i, X i) → Y) (hT : Measurable T)
    (φ : Y → ℂ) (hφ : Measurable φ) {B : ℝ} (hB : 0 ≤ B) (hb : ∀ y, ‖φ y‖ ≤ B) :
    ‖(∫ y, φ y ∂(μ.prod (Measure.pi (fun i => (p i).toMeasure))).map T) -
      ∫ y, φ y ∂(μ.prod (realDensityMeasure
        (Measure.pi (fun i => (Measure.count : Measure (X i))))
        (fun x => ∏ i, g i (x i)))).map T‖ ≤ B * (2 * ∑ i, ε i) := by
  rw [independentPMF_count_density p]
  have hfm (i) : Measurable (fun x => (p i x).toReal) := measurable_of_countable _
  have hgm (i) : Measurable (g i) := measurable_of_countable _
  have ht := retained_density_complex_test_error μ
    (Measure.pi (fun i => (Measure.count : Measure (X i))))
    (fun x => ∏ i, (p i (x i)).toReal) (fun x => ∏ i, g i (x i))
    (Finset.measurable_prod _ (fun i _ => (hfm i).comp (measurable_pi_apply i)))
    (Finset.measurable_prod _ (fun i _ => (hgm i).comp (measurable_pi_apply i)))
    (Integrable.fintype_prod_dep (fun i => pmf_real_integrable (p i)))
    (Integrable.fintype_prod_dep hg)
    (fun x => Finset.prod_nonneg (fun _ _ => ENNReal.toReal_nonneg))
    (fun x => Finset.prod_nonneg (fun i _ => hg0 i (x i))) T hT φ hφ hb
  exact ht.trans (mul_le_mul_of_nonneg_left
    (tensor_density_l1_le_twice_sum (fun i => (Measure.count : Measure (X i)))
      (fun i x => (p i x).toReal) g (fun i => pmf_real_integrable (p i)) hg
      (fun _ _ => ENNReal.toReal_nonneg) hg0 (fun i => pmf_real_integral_count (p i)) ε he hsmall) hB)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem count_finite_sum_le_integral {X : Type*} [Countable X] [MeasurableSpace X]
    [MeasurableSingletonClass X] (f : X → ℝ) (hf : Integrable f Measure.count)
    (hf0 : ∀ x, 0 ≤ f x) (s : Finset X) :
    (∑ x ∈ s, f x) ≤ ∫ x, f x ∂Measure.count := by
  have hs : Summable f := by
    simpa only [Real.norm_of_nonneg (hf0 _)] using integrable_count_iff.mp hf
  rw [integral_countable hf]
  simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]
  exact hs.sum_le_tsum s (fun x _ => hf0 x)

theorem independentPMF_finite_test_error {Q : Type*} [Fintype Q]
    {X : Q → Type*} [∀ q, Countable (X q)]
    [∀ q, MeasurableSpace (X q)] [∀ q, MeasurableSingletonClass (X q)]
    (p : ∀ q, PMF (X q)) (g : ∀ q, X q → ℝ)
    (hg : ∀ q, Integrable (g q) Measure.count) (hg0 : ∀ q x, 0 ≤ g q x)
    (ε : Q → ℝ) (he : ∀ q, (∫ x, |(p q x).toReal - g q x| ∂Measure.count) ≤ ε q)
    (hsmall : (∑ q, ε q) ≤ 1) (s : Finset (∀ q, X q)) (φ : (∀ q, X q) → ℂ)
    (hφ : ∀ x ∈ s, ‖φ x‖ ≤ 1) :
    ‖(∑ x ∈ s, ((∏ q, (p q (x q)).toReal : ℝ) : ℂ) * φ x) -
      (∑ x ∈ s, ((∏ q, g q (x q) : ℝ) : ℂ) * φ x)‖ ≤ 2 * ∑ q, ε q := by
  have hi : Integrable (fun x : ∀ q, X q => |(∏ q, (p q (x q)).toReal) - ∏ q, g q (x q)|) Measure.count := by
    rw [← pi_count_measure]
    exact ((Integrable.fintype_prod_dep (fun q => pmf_real_integrable (p q))).sub
      (Integrable.fintype_prod_dep hg)).abs
  have hn := norm_masked_density_sum_sub_le s (fun x => ∏ q, (p q (x q)).toReal)
    (fun x => ∏ q, g q (x q)) (fun _ => 1) φ (by norm_num : (0 : ℝ) ≤ 1)
    (fun _ _ => by norm_num) hφ
  simp only [one_mul] at hn
  apply hn.trans
  apply (count_finite_sum_le_integral _ hi (fun _ => abs_nonneg _) s).trans
  rw [← pi_count_measure]
  exact tensor_density_l1_le_twice_sum (fun q => (Measure.count : Measure (X q)))
    (fun q x => (p q x).toReal) g (fun q => pmf_real_integrable (p q)) hg
    (fun _ _ => ENNReal.toReal_nonneg) hg0 (fun q => pmf_real_integral_count (p q)) ε he hsmall

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem conditionalPMF_retained_grid_error {Ω I Z Y : Type*} [Fintype Ω] [Fintype I]
    {X : I → Type*} [∀ i, Countable (X i)]
    [∀ i, MeasurableSpace (X i)] [∀ i, MeasurableSingletonClass (X i)]
    [MeasurableSpace Z] [MeasurableSpace Y]
    (q : FiniteProbabilityWeights Ω) (μ : Ω → Measure Z) [∀ ω, IsProbabilityMeasure (μ ω)]
    (p : Ω → ∀ i, PMF (X i)) (g : Ω → ∀ i, X i → ℝ) (ε : Ω → I → ℝ)
    (hg : ∀ ω, q.weight ω ≠ 0 → ∀ i, Integrable (g ω i) Measure.count)
    (hg0 : ∀ ω, q.weight ω ≠ 0 → ∀ i x, 0 ≤ g ω i x)
    (he : ∀ ω, q.weight ω ≠ 0 → ∀ i,
      (∫ x, |(p ω i x).toReal - g ω i x| ∂Measure.count) ≤ ε ω i)
    (hsmall : ∀ ω, q.weight ω ≠ 0 → (∑ i, ε ω i) ≤ 1)
    (T : Ω → Z × (∀ i, X i) → Y) (hT : ∀ ω, Measurable (T ω))
    (φ : Ω → Y → ℂ) (hφ : ∀ ω, Measurable (φ ω)) {B : ℝ} (hB : 0 ≤ B)
    (hb : ∀ ω y, ‖φ ω y‖ ≤ B) :
    ‖q.complexMean (fun ω => ∫ y, φ ω y ∂((μ ω).prod
        (Measure.pi (fun i => (p ω i).toMeasure))).map (T ω)) -
      q.complexMean (fun ω => ∫ y, φ ω y ∂((μ ω).prod (realDensityMeasure
        (Measure.pi (fun i => (Measure.count : Measure (X i))))
        (fun x => ∏ i, g ω i (x i)))).map (T ω))‖ ≤
      q.mean (fun ω => B * (2 * ∑ i, ε ω i)) := by
  apply q.norm_complexMean_sub_le
  intro ω hω
  exact independentPMF_retained_complex_grid_error (μ ω) (p ω) (g ω) (hg ω hω) (hg0 ω hω)
    (ε ω) (he ω hω) (hsmall ω hω) (T ω) (hT ω) (φ ω) (hφ ω) hB (hb ω)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem gridDensityTest_independent {Q : Type*} [Fintype Q]
    (I : Q → Type*) [∀ q, Fintype (I q)]
    (ρ : ∀ q, (I q → ℝ) → ℝ) (H : Q → ℝ)
    (mask : ∀ q, (I q → ℤ) → ℝ) (grid : Finset ((Σ q, I q) → ℤ))
    (φ : ((Σ q, I q) → ℤ) → ℂ) :
    gridDensityTest (J := Σ q, I q) (fun x => ∏ q, ρ q (fun i => x ⟨q, i⟩)) 0 (fun j => H j.1)
      grid (fun v => ∏ q, mask q (fun i => v ⟨q, i⟩)) φ =
        ∑ v ∈ grid, ((∏ q, mask q (fun i => v ⟨q, i⟩) *
          ρ q (fun i => (v ⟨q, i⟩ : ℝ) / H q) / H q^Fintype.card (I q) : ℝ) : ℂ) * φ v := by
  have hprod : (∏ j : Σ q, I q, H j.1) = ∏ q, H q^Fintype.card (I q) := by
    rw [Fintype.prod_sigma]
    simp only [Finset.prod_const, Finset.card_univ]
  unfold gridDensityTest
  rw [hprod, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro v _
  simp only [rectangularLatticePoint, Pi.zero_apply, sub_zero, Finset.prod_div_distrib,
    Finset.prod_mul_distrib, Complex.ofReal_div, Complex.ofReal_mul]
  ring

theorem independentPMF_grid_test_error {Q : Type*} [Fintype Q]
    (I : Q → Type*) [∀ q, Fintype (I q)]
    (p : ∀ q, PMF (I q → ℤ)) (ρ : ∀ q, (I q → ℝ) → ℝ)
    (H : Q → ℝ) (mask : ∀ q, (I q → ℤ) → ℝ) (ε : Q → ℝ)
    (hg : ∀ q, Integrable (fun v => mask q v * ρ q (fun i => (v i : ℝ) / H q) /
      H q^Fintype.card (I q)) Measure.count)
    (hg0 : ∀ q v, 0 ≤ mask q v * ρ q (fun i => (v i : ℝ) / H q) / H q^Fintype.card (I q))
    (he : ∀ q, (∫ v, |(p q v).toReal - mask q v * ρ q (fun i => (v i : ℝ) / H q) /
      H q^Fintype.card (I q)| ∂Measure.count) ≤ ε q)
    (hsmall : (∑ q, ε q) ≤ 1) (grid : Finset ((Σ q, I q) → ℤ))
    (φ : ((Σ q, I q) → ℤ) → ℂ) (hφ : ∀ v ∈ grid, ‖φ v‖ ≤ 1) :
    ‖(∑ v ∈ grid, ((∏ q, (p q (fun i => v ⟨q, i⟩)).toReal : ℝ) : ℂ) * φ v) -
      gridDensityTest (J := Σ q, I q) (fun x => ∏ q, ρ q (fun i => x ⟨q, i⟩)) 0 (fun j => H j.1)
        grid (fun v => ∏ q, mask q (fun i => v ⟨q, i⟩)) φ‖ ≤ 2 * ∑ q, ε q := by
  classical
  let E : ((Σ q, I q) → ℤ) ↪ (∀ q, I q → ℤ) :=
    ⟨fun v q i => v ⟨q, i⟩, fun v w h => funext (fun j => congrFun (congrFun h j.1) j.2)⟩
  have htest : ∀ x ∈ grid.map E, ‖φ (fun j => x j.1 j.2)‖ ≤ 1 := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hx
    exact hφ v hv
  have hc := independentPMF_finite_test_error p
    (fun q v => mask q v * ρ q (fun i => (v i : ℝ) / H q) / H q^Fintype.card (I q))
    hg hg0 ε he hsmall (grid.map E) (fun x => φ (fun j => x j.1 j.2)) htest
  rw [gridDensityTest_independent]
  have hround (v : (Σ q, I q) → ℤ) : (fun j => E v j.1 j.2) = v := by
    funext j
    cases j
    rfl
  have hE (v : (Σ q, I q) → ℤ) (q) : E v q = fun i => v ⟨q, i⟩ := rfl
  simp only [Finset.sum_map] at hc
  simp only [hround] at hc
  simpa only [hE] using hc

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem fixed_mixed_output_grid_error {I J : Type*} [Fintype I] [Fintype J]
    (select : J ↪ I) (f g : (I → ℝ) → ℝ) {Kf Kg : ℝ≥0} (R : ℝ≥0)
    (hf : LipschitzWith Kf f) (hg : LipschitzWith Kg g)
    (hfs : ∀ v, (R : ℝ) < ‖v‖ → f v = 0)
    (hgs : ∀ v, (R : ℝ) < ‖v‖ → g v = 0)
    (hfg : Integrable (fun v => f v - g v)) {ε : ℝ}
    (he : (∫ v, |f v - g v|) ≤ ε)
    (a S : (UnselectedColumn select → ℝ) → J → ℝ)
    (hS : ∀ v j, 0 < S v j) {mesh M : ℝ}
    (hmesh0 : 0 ≤ mesh) (hmesh1 : mesh ≤ 1) (hmesh : ∀ v j, 1 / S v j ≤ mesh)
    (grid : (UnselectedColumn select → ℝ) → Finset (J → ℤ))
    (mask : (UnselectedColumn select → ℝ) → (J → ℤ) → ℝ)
    (φ : (UnselectedColumn select → ℝ) → (J → ℤ) → ℂ)
    (hM : 0 ≤ M) (hmask : ∀ v k, k ∈ grid v → |mask v k| ≤ M)
    (hφ : ∀ v k, k ∈ grid v → ‖φ v k‖ ≤ 1) :
    ‖∫ v, gridDensityTest (selectedOutputSlice select f v) (a v) (S v)
        (grid v) (mask v) (φ v) -
      gridDensityTest (selectedOutputSlice select g v) (a v) (S v)
        (grid v) (mask v) (φ v)‖ ≤
      M * (ε + (2 * (R : ℝ)) ^ Fintype.card (UnselectedColumn select) *
        ((2 * (R : ℝ) + 2) ^ Fintype.card J * ((Kf : ℝ) + Kg) * mesh)) := by
  have hi := integrable_snd_probability (Measure.dirac ()) volume (fun v => f v - g v) hfg
  have he' : (∫ p : Unit × (I → ℝ), |f p.2 - g p.2| ∂(Measure.dirac ()).prod volume) ≤ ε := by
    rw [integral_snd_probability (Measure.dirac ()) volume (fun v => |f v - g v|) hfg.abs]
    exact he
  have ht := mixed_output_grid_error select (Measure.dirac ()) (fun _ => f) (fun _ => g) R
    (Filter.Eventually.of_forall (fun _ => ⟨hf, hg, hfs, hgs⟩)) hi he'
    (fun p => a p.2) (fun p => S p.2) (fun p => hS p.2)
    hmesh0 hmesh1 (fun p => hmesh p.2) (fun p => grid p.2)
    (fun p => mask p.2) (fun p => φ p.2) hM (fun p => hmask p.2) (fun p => hφ p.2)
  rw [Measure.dirac_prod, (measurableEmbedding_prodMk_left ()).integral_map] at ht
  exact ht

end Erdos3

end

section

namespace Erdos3

theorem coefficientGridBoxFactor_le_exp (i j : ℕ) {C R b : ℝ}
    (hb : 0 ≤ b) (hC0 : 0 ≤ C) (hR0 : 0 ≤ R)
    (hC : C ≤ Real.exp b) (hR : R ≤ Real.exp b) :
    coefficientGridBoxFactor i j C R ≤ Real.exp ((i : ℝ) * (j + 2 * b + 3)) := by
  have hj : (j : ℝ) ≤ Real.exp (j : ℝ) := by linarith [Real.add_one_le_exp (j : ℝ)]
  have hprod : (j : ℝ) * C * R ≤ Real.exp (j + 2 * b) := by
    calc
      _ ≤ Real.exp (j : ℝ) * Real.exp b * Real.exp b := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hone : 1 ≤ Real.exp (j + 2 * b) := Real.one_le_exp_iff.mpr (by positivity)
  have hthree : (3 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  have hbase : 2 * (j * C * R) + 1 ≤ Real.exp (j + 2 * b + 3) := by
    rw [Real.exp_add]
    nlinarith [Real.exp_pos (j + 2 * b)]
  calc
    _ ≤ (Real.exp (j + 2 * b + 3)) ^ i := pow_le_pow_left₀ (by positivity) hbase i
    _ = _ := (Real.exp_nat_mul _ _).symm

theorem coefficientGridReplacementScale_le {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) {C R b t ε L : ℝ} (h : ℕ)
    (hb : 0 ≤ b) (hC0 : 0 ≤ C) (hR0 : 0 ≤ R) (hε : 0 < ε) (hL : 0 ≤ L)
    (hC : C ≤ Real.exp b) (hR : R ≤ Real.exp b) :
    coefficientGridReplacementScale s C R b t ε L h ≤
      Real.exp (coefficientLogAllowance (Fintype.card I) (Fintype.card (UnselectedColumn s))
        (affineCoefficientCommonBudget (Fintype.card J) (Fintype.card (UnselectedColumn s)) b t) +
          (Fintype.card I : ℝ) * (Fintype.card J + 2 * b + 3)) *
        (1 + ε⁻¹) * L ^ (h * (Fintype.card I + 1)) := by
  let q : ℝ := (Fintype.card I : ℝ) * (Fintype.card J + 2 * b + 3)
  have hbox : coefficientGridBoxFactor (Fintype.card I) (Fintype.card J) C R ≤ Real.exp q :=
    coefficientGridBoxFactor_le_exp _ _ hb hC0 hR0 hC hR
  have hone : 1 ≤ Real.exp q := Real.one_le_exp_iff.mpr (by dsimp [q]; positivity)
  have hfac : 1 + coefficientGridBoxFactor (Fintype.card I) (Fintype.card J) C R / ε ≤
      Real.exp q * (1 + ε⁻¹) := by
    rw [div_eq_mul_inv, mul_add, mul_one]
    exact add_le_add hone (mul_le_mul_of_nonneg_right hbox (inv_nonneg.mpr hε.le))
  rw [coefficientGridReplacementScale_eq, Real.exp_add]
  calc
    _ ≤ _ * (Real.exp q * (1 + ε⁻¹)) * L ^ (h * (Fintype.card I + 1)) := by
      gcongr
    _ = _ := by dsimp only [q]; ring

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

theorem affineCoefficientGrid_joint_tolerance {Ω K Z Y : Type*} [Fintype Ω] [Fintype K]
    {O J : K → Type*} [∀ k, Fintype (O k)] [∀ k, DecidableEq (O k)]
    [∀ k, Fintype (J k)] [∀ k, DecidableEq (J k)]
    [MeasurableSpace Z] [MeasurableSpace Y]
    (q : FiniteProbabilityWeights Ω) (μ : Ω → Measure Z) [∀ ω, IsProbabilityMeasure (μ ω)]
    (A : Ω → ∀ k, Matrix (O k) (J k) ℤ) (s : ∀ k, O k ↪ J k)
    (hA : ∀ ω k, ((A ω k).submatrix id (s k)).det ≠ 0)
    (S : ∀ k, J k → ℝ) (hS : ∀ k j, 0 < S k j) (H L C U G : K → ℝ) (h : K → ℕ)
    (ctrl : ∀ ω, q.weight ω ≠ 0 → ∀ k,
      CoefficientFiberControl (A ω k) (s k) (S k) (H k) (L k) (h k) (C k) (U k) (G k))
    (hL : ∀ k, 0 < L k) (hH : ∀ k, 0 < H k) (hH1 : ∀ k, 1 ≤ H k)
    (hC0 : ∀ k, 0 ≤ C k) (hU0 : ∀ k, 0 ≤ U k) (hG0 : ∀ k, 0 ≤ G k)
    (c w : ∀ k, J k → ℝ) (hw : ∀ k j, 0 < w k j) (δ : K → ℝ≥0) (hδ : ∀ k, 0 < δ k)
    (hwidth : ∀ k j, (δ k : ℝ) ≤ w k j) (R b t ε : K → ℝ)
    (hR0 : ∀ k, 0 ≤ R k) (hsupport : ∀ k j, |c k j| + w k j ≤ R k)
    (hb : ∀ k, 0 ≤ b k) (ht : ∀ k, 0 ≤ t k) (hε : ∀ k, 0 < ε k)
    (hG : ∀ k, G k ≤ Real.exp (b k)) (hU : ∀ k, U k ≤ Real.exp (b k))
    (hC : ∀ k, C k ≤ Real.exp (b k)) (hR : ∀ k, R k ≤ Real.exp (b k))
    (hi : ∀ k, (δ k : ℝ)⁻¹ ≤ Real.exp (t k))
    (hlarge : ∀ k, coefficientGridReplacementScale (s k) (C k) (R k) (b k) (t k)
      (ε k) (L k) (h k) ≤ H k) (hsmall : (∑ k, ε k) ≤ 1)
    (F : Ω → Z × (∀ k, O k → ℤ) → Y) (hF : ∀ ω, Measurable (F ω))
    (φ : Ω → Y → ℂ) (hφ : ∀ ω, Measurable (φ ω)) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ ω y, ‖φ ω y‖ ≤ B) :
    ∃ hZ : ∀ k, 0 < coefficientWeightSum (affineProductProfile (c k) (w k)) (S k),
      ‖q.complexMean (fun ω => ∫ y, φ ω y ∂((μ ω).prod (Measure.pi (fun k =>
          (coefficientImagePMF (A ω k) (affineProductProfile (c k) (w k))
            (affineProductProfile_nonneg (c k) (w k) (hw k)) (S k) (hS k)
            (affineProductProfile_zero_outside (c k) (w k) (hw k) (hR0 k) (hsupport k))
            (hZ k)).toMeasure))).map (F ω)) -
        q.complexMean (fun ω => ∫ y, φ ω y ∂((μ ω).prod (realDensityMeasure
          (Measure.pi (fun k => (Measure.count : Measure (O k → ℤ))))
          (fun x => ∏ k, coefficientGridProxy (A ω k) (s k) (hA ω k) (S k) (fun _ => H k)
            (hS k) (fun _ => hH k) (affineProductProfile (c k) (w k)) (x k)))).map (F ω))‖ ≤
        B * (2 * ∑ k, ε k) := by
  classical
  obtain ⟨ω₀, hω₀⟩ := finiteProbability_exists_nonzero_weight q
  have hrow (ω : Ω) (hω : q.weight ω ≠ 0) (k : K) :=
    affineCoefficientGrid_tolerance (A ω k) (s k) (S k) (hS k) (h k) (ctrl ω hω k)
      (hL k) (hH k) (hH1 k) (hC0 k) (hU0 k) (hG0 k)
      (c k) (w k) (hw k) (hδ k) (hwidth k) (hR0 k) (hsupport k)
      (hb k) (ht k) (hε k) (hG k) (hU k) (hC k) (hR k) (hi k) (hlarge k)
  choose hZ hzero using hrow ω₀ hω₀
  refine ⟨hZ, ?_⟩
  let p : Ω → ∀ k, PMF (O k → ℤ) := fun ω k =>
    coefficientImagePMF (A ω k) (affineProductProfile (c k) (w k))
      (affineProductProfile_nonneg (c k) (w k) (hw k)) (S k) (hS k)
      (affineProductProfile_zero_outside (c k) (w k) (hw k) (hR0 k) (hsupport k)) (hZ k)
  let g : Ω → ∀ k, (O k → ℤ) → ℝ := fun ω k =>
    coefficientGridProxy (A ω k) (s k) (hA ω k) (S k) (fun _ => H k)
      (hS k) (fun _ => hH k) (affineProductProfile (c k) (w k))
  have hgi (ω) (hω : q.weight ω ≠ 0) (k) : Integrable (g ω k) Measure.count :=
    coefficientGridProxy_integrable_of_control (A ω k) (s k) (S k) (hS k) (h k) (ctrl ω hω k)
      (hH k) (hC0 k) (affineProductProfile (c k) (w k)) (hR0 k)
      (affineProductProfile_zero_outside (c k) (w k) (hw k) (hR0 k) (hsupport k))
  have hg0 (ω) (_hω : q.weight ω ≠ 0) (k) (v) : 0 ≤ g ω k v :=
    coefficientGridProxy_nonneg (A ω k) (s k) (hA ω k) (S k) (fun _ => H k)
      (hS k) (fun _ => hH k) _ (affineProductProfile_nonneg (c k) (w k) (hw k)) v
  have he (ω) (hω : q.weight ω ≠ 0) (k) :
      (∫ v, |(p ω k v).toReal - g ω k v| ∂Measure.count) ≤ ε k := by
    obtain ⟨_, he⟩ := hrow ω hω k
    exact he
  have herr := conditionalPMF_retained_grid_error q μ p g (fun _ => ε)
    hgi hg0 he (fun _ _ => hsmall) F hF φ hφ hB hbound
  simpa only [q.mean_const] using herr

end Erdos3

end

end OAI
