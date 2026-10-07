/-
Modified for ProveIt: identify the interval residue filters explicitly
on Lean 4.32. Mathematical statements are unchanged.
-/
import OAI.Combinatorics.Progressions.Estimates.PositiveNormalizationError

namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

noncomputable def reweightPositive {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (hm : 0 < p.mean w) : FiniteProbabilityWeights X :=
  ofPositiveWeights (fun x => p.weight x * w x) (fun x => mul_nonneg (p.nonneg x) (hw x)) hm

theorem reweightPositive_weight {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (hm : 0 < p.mean w) (x : X) :
    (p.reweightPositive w hw hm).weight x = p.weight x * w x / p.mean w := rfl

theorem reweightPositive_mean {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (hm : 0 < p.mean w) (f : X → ℝ) :
    (p.reweightPositive w hw hm).mean f = p.mean (fun x => w x * f x) / p.mean w := by
  simp only [mean, reweightPositive_weight, div_mul_eq_mul_div, mul_assoc, Finset.sum_div]

theorem reweightPositive_complexMean {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (hm : 0 < p.mean w) (f : X → ℂ) :
    (p.reweightPositive w hw hm).complexMean f =
      p.complexMean (fun x => (w x : ℂ) * f x) / (p.mean w : ℂ) := by
  simp only [complexMean, reweightPositive_weight, Complex.ofReal_div, Complex.ofReal_mul,
    div_mul_eq_mul_div, mul_assoc, Finset.sum_div]

theorem reweightPositive_fiberLaw_weight {X R : Type*} [Fintype X] [Fintype R]
    (p : FiniteProbabilityWeights X) (F : X → R)
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (hm : 0 < p.mean w) (r : R) :
    ((p.reweightPositive w hw hm).fiberLaw F).weight r = p.fiberMean F r w / p.mean w := by
  rw [fiberLaw_weight, fiberMean, reweightPositive_mean]
  simp only [mul_ite, mul_one, mul_zero, fiberMean]

theorem uniform_reweightPositive_eq {X : Type*} [Fintype X] [Nonempty X]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (hm : 0 < (uniform X).mean w) (hsum : 0 < ∑ x, w x) :
    (uniform X).reweightPositive w hw hm = ofPositiveWeights w hw hsum := by
  apply eq_of_weight_eq
  intro x
  change ((Fintype.card X : ℝ)⁻¹ * w x) /
    (∑ y, (Fintype.card X : ℝ)⁻¹ * w y) = w x / ∑ y, w y
  rw [← Finset.mul_sum]
  have hc : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp [hc, hsum.ne']

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

theorem mean_mul_le_of_capped_comparison {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (D g φ : X → ℝ) {C ε : ℝ}
    (hφ : ∀ x, 0 ≤ φ x) (hg : ∀ x, g x ≤ C)
    (he : |p.mean (fun x => D x * φ x) - p.mean (fun x => g x * φ x)| ≤ ε) :
    p.mean (fun x => D x * φ x) ≤ C * p.mean φ + ε := by
  have hb : p.mean (fun x => g x * φ x) ≤ C * p.mean φ := by
    rw [← p.mean_const_mul]
    exact p.mean_mono (fun x => mul_le_mul_of_nonneg_right (hg x) (hφ x))
  have ht := (abs_le.mp he).2
  linarith

theorem reweightPositive_test_le {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (D : X → ℝ) (hD0 : ∀ x, 0 ≤ D x)
    (hD : 0 < p.mean D) (φ : X → ℝ) (hφ : ∀ x, 0 ≤ φ x)
    {C ε a : ℝ} (ha : 0 < a) (hlower : a ≤ p.mean D)
    (he : p.mean (fun x => D x * φ x) ≤ C * p.mean φ + ε) :
    (p.reweightPositive D hD0 hD).mean φ ≤ (C * p.mean φ + ε) / a := by
  rw [p.reweightPositive_mean]
  have hnum : 0 ≤ C * p.mean φ + ε :=
    (p.mean_nonneg (fun x => mul_nonneg (hD0 x) (hφ x))).trans he
  exact (div_le_div_of_nonneg_right he hD.le).trans
    (div_le_div_of_nonneg_left hnum ha hlower)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

theorem reweightPositive_lowWeightFibers_mass {X R : Type*} [Fintype X] [Fintype R]
    (p : FiniteProbabilityWeights X) (F : X → R)
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (hm : 0 < p.mean w) {η : ℝ} (hη : 0 ≤ η) :
    (p.reweightPositive w hw hm).mass
      (Finset.univ.filter (fun x => F x ∈ p.lowWeightFibers F w η)) ≤ η / p.mean w := by
  rw [← fiberLaw_mass_preimage]
  unfold mass
  simp only [reweightPositive_fiberLaw_weight]
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right (p.lowWeightFibers_weighted_mass F w hη) hm.le

theorem reweightPositive_remove_lowWeightFibers_error {X R : Type*} [Fintype X] [Fintype R]
    (p : FiniteProbabilityWeights X) (F : X → R)
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (hm : 0 < p.mean w) {η : ℝ} (hη : 0 ≤ η)
    (f : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖(p.reweightPositive w hw hm).complexMean f -
      (p.reweightPositive w hw hm).complexMean
        (fun x => if x ∈ Finset.univ.filter (fun y => F y ∈ p.lowWeightFibers F w η) then 0 else f x)‖ ≤
      η / p.mean w :=
  ((p.reweightPositive w hw hm).norm_complexMean_remove_set_le_mass _ f hf).trans
    (p.reweightPositive_lowWeightFibers_mass F w hw hm hη)

theorem reweightPositive_lowWeightFibers_mass_le {X R : Type*} [Fintype X] [Fintype R]
    (p : FiniteProbabilityWeights X) (F : X → R)
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) {μ η : ℝ} (hμ : 0 < μ)
    (hm : μ ≤ p.mean w) (hη : 0 ≤ η) :
    (p.reweightPositive w hw (hμ.trans_le hm)).mass
      (Finset.univ.filter (fun x => F x ∈ p.lowWeightFibers F w η)) ≤ η / μ :=
  (p.reweightPositive_lowWeightFibers_mass F w hw (hμ.trans_le hm) hη).trans
    (div_le_div_of_nonneg_left hη hμ hm)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open MeasureTheory

variable {X C : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

noncomputable def normalizedDensityTest (D : X → ℝ) (f : X → ℂ) : ℂ :=
  p.complexMean (fun x => (D x : ℂ)*f x)/(p.mean D : ℂ)

theorem normalizedDensityTest_norm_le_one (D : X → ℝ) (hD : ∀ x, 0 ≤ D x)
    (hmass : 0 < p.mean D) (f : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖p.normalizedDensityTest D f‖ ≤ 1 := by
  rw [normalizedDensityTest, norm_div, Complex.norm_real, Real.norm_of_nonneg hmass.le]
  exact (div_le_one hmass).mpr (p.norm_density_weighted_complexMean_le D hD f hf)

variable [MeasurableSpace C]

theorem normalizedDensityTest_measurable (D : C → X → ℝ)
    (hD : ∀ x, Measurable (fun c => D c x)) (f : X → ℂ) :
    Measurable (fun c => p.normalizedDensityTest (D c) f) :=
  (p.complexMean_measurable (fun c x => (D c x : ℂ)*f x)
    (fun x => (Complex.continuous_ofReal.measurable.comp (hD x)).mul_const (f x))).div
    (Complex.continuous_ofReal.measurable.comp (p.mean_measurable D hD))

theorem normalizedDensityTest_integrable (μ : Measure C) [IsFiniteMeasure μ]
    (D : C → X → ℝ) (hD : ∀ x, Measurable (fun c => D c x))
    (hD0 : ∀ c x, 0 ≤ D c x) (hmass : ∀ c, 0 < p.mean (D c))
    (f : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    Integrable (fun c => p.normalizedDensityTest (D c) f) μ :=
  Integrable.of_bound (p.normalizedDensityTest_measurable D hD f).aestronglyMeasurable 1
    (ae_of_all μ (fun c => p.normalizedDensityTest_norm_le_one (D c) (hD0 c) (hmass c) f hf))

theorem integral_normalizedDensityTest_compare (μ : Measure C) [IsProbabilityMeasure μ]
    (D : C → X → ℝ) (hD : ∀ x, Measurable (fun c => D c x))
    (hD0 : ∀ c x, 0 ≤ D c x) (hmass : ∀ c, 0 < p.mean (D c))
    (F : C → X → ℝ) (hF : ∀ x, Integrable (fun c => F c x) μ)
    (hFmass : ∀ x, (∫ c, F c x ∂μ) = 1)
    (f : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) {ε : ℝ}
    (herror : ∀ c, ‖p.normalizedDensityTest (D c) f -
      p.complexMean (fun x => f x*(F c x : ℂ))‖ ≤ ε) :
    ‖(∫ c, p.normalizedDensityTest (D c) f ∂μ)-p.complexMean f‖ ≤ ε := by
  have hi := p.normalizedDensityTest_integrable μ D hD hD0 hmass f hf
  have hterm (x : X) : Integrable (fun c => f x*(F c x : ℂ)) μ := (hF x).ofReal.const_mul (f x)
  have href := p.complexMean_integrable μ (fun c x => f x*(F c x : ℂ)) hterm
  have hmean : (∫ c, p.complexMean (fun x => f x*(F c x : ℂ)) ∂μ) = p.complexMean f := by
    rw [p.integral_complexMean μ _ hterm]
    congr 1
    funext x
    rw [integral_const_mul, integral_complex_ofReal, hFmass x, Complex.ofReal_one, mul_one]
  rw [← hmean, ← integral_sub hi href]
  have h := norm_integral_le_of_norm_le (integrable_const ε (μ := μ)) (ae_of_all μ herror)
  simpa only [integral_const, probReal_univ, one_smul] using h

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem mean_prod (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (f : X × Y → ℝ) :
    (p.prod q).mean f = p.mean (fun x => q.mean (fun y => f (x,y))) := by
  simp only [mean, prod, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

theorem mean_mem_Icc (p : FiniteProbabilityWeights X) (f : X → ℝ) {a b : ℝ}
    (hf : ∀ x, f x ∈ Set.Icc a b) : p.mean f ∈ Set.Icc a b := by
  constructor
  · exact (p.mean_const a).symm.trans_le (p.mean_mono (fun x => (hf x).1))
  · exact (p.mean_mono (fun x => (hf x).2)).trans_eq (p.mean_const b)

theorem abs_mean_sub_const_le (p : FiniteProbabilityWeights X) (f : X → ℝ) (c ε : ℝ)
    (hf : ∀ x, |f x-c| ≤ ε) : |p.mean f-c| ≤ ε := by
  have h := p.mean_mem_Icc f (a := c-ε) (b := c+ε) (fun x => by
    have hx := abs_le.mp (hf x)
    constructor <;> linarith)
  exact abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩

theorem reweightPositive_complexMean_eq_normalizedDensityTest
    (p : FiniteProbabilityWeights X) (D : X → ℝ) (hD : ∀ x, 0 ≤ D x)
    (hmass : 0 < p.mean D) (f : X → ℂ) :
    (p.reweightPositive D hD hmass).complexMean f = p.normalizedDensityTest D f :=
  p.reweightPositive_complexMean D hD hmass f

theorem normalizedDensityTest_remove_normalization (p : FiniteProbabilityWeights X)
    (D : X → ℝ) (hD : ∀ x, 0 ≤ D x) (hmass : 0 < p.mean D)
    (f : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖p.normalizedDensityTest D f - p.complexMean (fun x => (D x : ℂ)*f x)‖ ≤ |p.mean D-1| :=
  complex_remove_normalization hmass (p.norm_density_weighted_complexMean_le D hD f hf)

theorem joint_normalization_compare (p : FiniteProbabilityWeights X) (q : FiniteProbabilityWeights Y)
    (D : X × Y → ℝ) (hD : ∀ z, 0 ≤ D z)
    (hlocal : ∀ x, 0 < q.mean (fun y => D (x,y))) (hglobal : 0 < (p.prod q).mean D)
    (f : X × Y → ℂ) (hf : ∀ z, ‖f z‖ ≤ 1) {ε : ℝ}
    (hclose : ∀ x, |q.mean (fun y => D (x,y))-1| ≤ ε) :
    ‖(p.prod q).normalizedDensityTest D f -
      p.complexMean (fun x => q.normalizedDensityTest (fun y => D (x,y)) (fun y => f (x,y)))‖ ≤ 2*ε := by
  have hmass : |(p.prod q).mean D-1| ≤ ε := by
    rw [mean_prod]
    exact p.abs_mean_sub_const_le _ 1 ε hclose
  have hj := ((p.prod q).normalizedDensityTest_remove_normalization D hD hglobal f hf).trans hmass
  have hl := p.norm_complexMean_sub_le
    (fun x => q.normalizedDensityTest (fun y => D (x,y)) (fun y => f (x,y)))
    (fun x => q.complexMean (fun y => (D (x,y) : ℂ)*f (x,y))) (fun _ => ε)
    (fun x _ => (q.normalizedDensityTest_remove_normalization _ (fun y => hD (x,y))
      (hlocal x) _ (fun y => hf (x,y))).trans (hclose x))
  rw [p.mean_const, ← complexMean_prod p q (fun z => (D z : ℂ)*f z)] at hl
  have ht := norm_sub_le_norm_sub_add_norm_sub
    ((p.prod q).normalizedDensityTest D f)
    ((p.prod q).complexMean (fun z => (D z : ℂ)*f z))
    (p.complexMean (fun x => q.normalizedDensityTest (fun y => D (x,y)) (fun y => f (x,y))))
  rw [norm_sub_rev ((p.prod q).complexMean _)] at ht
  linarith

noncomputable def uniformFinset {A : Type*} (S : Finset A) (hS : S.Nonempty) :
    FiniteProbabilityWeights S := by
  letI : Nonempty S := hS.to_subtype
  exact uniform S

theorem uniformFinset_mean {A : Type*} (S : Finset A) (hS : S.Nonempty) (f : A → ℝ) :
    (uniformFinset S hS).mean (fun x => f x.val) = 𝔼 x ∈ S, f x := by
  let : Nonempty S := hS.to_subtype
  rw [uniformFinset, uniform_mean]
  simp only [Finset.expect_eq_sum_div_card, Finset.card_univ,
    Finset.sum_coe_sort, Fintype.card_coe]

theorem uniformFinset_complexMean {A : Type*} (S : Finset A) (hS : S.Nonempty) (f : A → ℂ) :
    (uniformFinset S hS).complexMean (fun x => f x.val) = 𝔼 x ∈ S, f x := by
  let : Nonempty S := hS.to_subtype
  rw [uniformFinset, uniform_complexMean]
  simp only [Finset.expect_eq_sum_div_card, Finset.card_univ,
    Finset.sum_coe_sort, Fintype.card_coe]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem fiberLaw_complexMean {Ω X : Type*} [Fintype Ω] [Fintype X]
    (p : FiniteProbabilityWeights Ω) (F : Ω → X) (f : X → ℂ) :
    (p.fiberLaw F).complexMean f = p.complexMean (fun x => f (F x)) := by
  have h := p.complexMean_fiber_factor F (fun _ => 1) f
  simpa only [Complex.ofReal_one, one_mul, complexMean, fiberLaw_weight] using h.symm

theorem fiberLaw_mean {Ω X : Type*} [Fintype Ω] [Fintype X]
    (p : FiniteProbabilityWeights Ω) (F : Ω → X) (f : X → ℝ) :
    (p.fiberLaw F).mean f = p.mean (fun x => f (F x)) := by
  have h := congrArg Complex.re (p.fiberLaw_complexMean F (fun x => (f x : ℂ)))
  simpa only [complexMean_re, Complex.ofReal_re] using h

noncomputable def siteLaw {Ω T X : Type*} [Fintype Ω] [Fintype T] [Nonempty T] [Fintype X]
    (p : FiniteProbabilityWeights Ω) (F : Ω → T → X) : FiniteProbabilityWeights X :=
  (p.prod (uniform T)).fiberLaw (fun z => F z.1 z.2)

theorem siteLaw_mean {Ω T X : Type*} [Fintype Ω] [Fintype T] [Nonempty T] [Fintype X]
    (p : FiniteProbabilityWeights Ω) (F : Ω → T → X) (f : X → ℝ) :
    (p.siteLaw F).mean f = p.mean (fun z => 𝔼 t, f (F z t)) := by
  rw [siteLaw, fiberLaw_mean, mean_prod]
  simp_rw [uniform_mean]

theorem siteLaw_complexMean {Ω T X : Type*} [Fintype Ω] [Fintype T] [Nonempty T] [Fintype X]
    (p : FiniteProbabilityWeights Ω) (F : Ω → T → X) (f : X → ℂ) :
    (p.siteLaw F).complexMean f = p.complexMean (fun z => 𝔼 t, f (F z t)) := by
  rw [siteLaw, fiberLaw_complexMean, complexMean_prod]
  simp_rw [uniform_complexMean]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators Classical

noncomputable def intervalUniformWeights (a b : ℤ) (hab : a < b) :
    FiniteProbabilityWeights (Finset.Ico a b) := by
  let : Nonempty (Finset.Ico a b) := ⟨⟨a, Finset.mem_Ico.mpr ⟨le_rfl, hab⟩⟩⟩
  exact FiniteProbabilityWeights.uniform _

theorem intervalUniformWeights_mean (a b : ℤ) (hab : a < b) (f : Finset.Ico a b → ℝ) :
    (intervalUniformWeights a b hab).mean f = 𝔼 x, f x := by
  let : Nonempty (Finset.Ico a b) := ⟨⟨a, Finset.mem_Ico.mpr ⟨le_rfl, hab⟩⟩⟩
  unfold intervalUniformWeights
  exact FiniteProbabilityWeights.uniform_mean f

theorem interval_mod_probability (a b m v : ℤ) (hab : a < b) (hm : 0 < m) :
    (intervalUniformWeights a b hab).eventProbability (fun x => (x : ℤ) ≡ v [ZMOD m]) ≤
      1 / (m : ℝ) + 1 / ((b - a : ℤ) : ℝ) := by
  have hL : (0 : ℝ) < ((b - a : ℤ) : ℝ) := by exact_mod_cast sub_pos.mpr hab
  unfold FiniteProbabilityWeights.eventProbability
  rw [intervalUniformWeights_mean,
    @integerInterval_indicator_expect a b hab.le (fun x : ℤ => x ≡ v [ZMOD m])
      (fun _ => Classical.propDecidable _)]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have heq : (((b - a : ℤ) : ℝ) / (m : ℝ) + 1) / ((b - a : ℤ) : ℝ) =
      1 / (m : ℝ) + 1 / ((b - a : ℤ) : ℝ) := by
    field_simp
  have hdiv := div_le_div_of_nonneg_right
    (scalarResidue_card_real_le a b m v hab.le hm) hL.le
  convert hdiv.trans_eq heq using 1 <;> try rfl
  apply congrArg (fun s : Finset ℤ => (s.card : ℝ) / ((b - a : ℤ) : ℝ))
  ext x
  simp

theorem interval_divisor_probability (a b m v : ℤ) (hab : a < b) (hm : 0 < m) :
    (intervalUniformWeights a b hab).eventProbability (fun x => m ∣ (x : ℤ) - v) ≤
      1 / (m : ℝ) + 1 / ((b - a : ℤ) : ℝ) := by
  have heq : (fun x : Finset.Ico a b => m ∣ (x : ℤ) - v) =
      (fun x : Finset.Ico a b => (x : ℤ) ≡ v [ZMOD m]) := by
    funext x
    exact propext (by rw [Int.modEq_iff_dvd, dvd_sub_comm])
  rw [heq]
  exact interval_mod_probability a b m v hab hm

end Erdos3

end

end OAI
