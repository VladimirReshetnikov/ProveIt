import Mathlib.MeasureTheory.Integral.Bochner.Basic
import OAI.Combinatorics.Progressions.Estimates.QuantitativeNoninjectivity

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

namespace FiniteProbabilityWeights

theorem productive_mass_lower_bound {Ω : Type*} [Fintype Ω]
    (p : FiniteProbabilityWeights Ω) (score : Ω → ℝ) (bad : Finset Ω)
    {a : ℝ} (ha : 0 ≤ a) (hscore : ∀ x, score x ≤ 1) :
    p.mean score - a - p.mass bad ≤
      p.mass (Finset.univ.filter (fun x => x ∉ bad ∧ a ≤ score x)) := by
  classical
  let productive := Finset.univ.filter (fun x => x ∉ bad ∧ a ≤ score x)
  have hpoint (x : Ω) : score x ≤ a + (if x ∈ productive then 1 else 0) +
      (if x ∈ bad then 1 else 0) := by
    by_cases hb : x ∈ bad
    · simp only [hb, ite_true]
      split_ifs <;> linarith [hscore x]
    · by_cases hs : a ≤ score x
      · have hp : x ∈ productive := by simp [productive, hb, hs]
        simp only [hb, hp, ite_true, ite_false]
        linarith [hscore x]
      · have hp : x ∉ productive := by simp [productive, hs]
        simp only [hb, hp, ite_false, add_zero]
        linarith
  have h := p.mean_mono hpoint
  rw [p.mean_add, p.mean_add, p.mean_const, p.mean_indicator, p.mean_indicator] at h
  linarith

end FiniteProbabilityWeights

theorem exists_productive_sampler_center {C Ω : Type*} [MeasurableSpace C] [Fintype Ω]
    (μ : Measure C) [IsProbabilityMeasure μ]
    (law : C → FiniteProbabilityWeights Ω) (score : C → Ω → ℝ) (bad : C → Finset Ω)
    {σ : ℝ} (hσ : 0 < σ)
    (hscore : ∀ c x, score c x ≤ 1)
    (hbad : ∀ c, (law c).mass (bad c) ≤ σ / 16)
    (hint : Integrable (fun c => (law c).mean (score c)) μ)
    (hmean : 7 * σ / 8 ≤ ∫ c, (law c).mean (score c) ∂μ) :
    ∃ c, σ / 4 ≤ (law c).mass
      (Finset.univ.filter (fun x => x ∉ bad c ∧ σ / 2 ≤ score c x)) := by
  classical
  have hex : ∃ c, 13 * σ / 16 < (law c).mean (score c) := by
    by_contra! h
    have hi := integral_mono hint (integrable_const (13 * σ / 16)) h
    rw [integral_const, probReal_univ, one_smul] at hi
    linarith
  obtain ⟨c, hc⟩ := hex
  refine ⟨c, ?_⟩
  have hmass := (law c).productive_mass_lower_bound (score c) (bad c)
    (by positivity : 0 ≤ σ / 2) (hscore c)
  linarith [hbad c]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

theorem exists_productive_injective_center {C Ω R Y : Type*}
    [MeasurableSpace C] [Fintype Ω] [Fintype R]
    (μ : Measure C) [IsProbabilityMeasure μ]
    (law : C → FiniteProbabilityWeights Ω) (sites : FiniteProbabilityWeights R)
    (image : Ω → R → Y) (test : Y → ℝ)
    {σ η parent : ℝ} (hσ : 0 < σ) (hη : η ≤ σ / 8) (hparent : σ ≤ parent)
    (htest : ∀ y, test y ≤ 1)
    (hint : ∀ r, Integrable (fun c => (law c).mean (fun z => test (image z r))) μ)
    (hmarginal : ∀ r, parent - η ≤ ∫ c, (law c).mean (fun z => test (image z r)) ∂μ)
    (hcollision : ∀ c, (law c).mean (fun z => noninjectivityIndicator (image z)) ≤ σ / 16) :
    ∃ c, σ / 4 ≤ (law c).mass (Finset.univ.filter (fun z =>
      Function.Injective (image z) ∧ σ / 2 ≤ sites.mean (fun r => test (image z r)))) := by
  let score := fun z => sites.mean (fun r => test (image z r))
  let bad := Finset.univ.filter (fun z => ¬Function.Injective (image z))
  have hscore (z) : score z ≤ 1 := by
    calc
      _ ≤ sites.mean (fun _ => 1) := sites.mean_mono (fun r => htest _)
      _ = 1 := sites.mean_const 1
  have hbad (c) : (law c).mass bad ≤ σ / 16 := by
    rw [← (law c).mean_indicator]
    convert hcollision c using 1
    congr 1
    funext z
    by_cases hz : Function.Injective (image z) <;> simp [bad, hz, noninjectivityIndicator]
  have he (c) : (law c).mean score =
      sites.mean (fun r => (law c).mean (fun z => test (image z r))) :=
    (law c).mean_comm sites (fun z r => test (image z r))
  have hi : Integrable (fun c => (law c).mean score) μ := by
    simp_rw [he]
    exact sites.mean_integrable μ _ hint
  have havg : 7 * σ / 8 ≤ ∫ c, (law c).mean score ∂μ := by
    simp_rw [he]
    rw [sites.integral_mean μ _ hint]
    calc
      _ ≤ parent - η := by linarith
      _ = sites.mean (fun _ => parent - η) := (sites.mean_const _).symm
      _ ≤ _ := sites.mean_mono hmarginal
  obtain ⟨c, hc⟩ := exists_productive_sampler_center μ law (fun _ => score) (fun _ => bad)
    hσ (fun _ => hscore) hbad hi havg
  refine ⟨c, ?_⟩
  simpa only [bad, Finset.mem_filter, Finset.mem_univ, true_and, not_not, score] using hc

theorem exists_productive_injective_center_of_complex_marginals {C Ω R Y : Type*}
    [MeasurableSpace C] [Fintype Ω] [Fintype R]
    (μ : Measure C) [IsProbabilityMeasure μ]
    (law : C → FiniteProbabilityWeights Ω) (sites : FiniteProbabilityWeights R)
    (image : Ω → R → Y) (test : Y → ℝ)
    {σ η parent : ℝ} (hσ : 0 < σ) (hη : η ≤ σ / 8) (hparent : σ ≤ parent)
    (htest : ∀ y, test y ≤ 1)
    (hint : ∀ r, Integrable
      (fun c => (law c).complexMean (fun z => (test (image z r) : ℂ))) μ)
    (hmarginal : ∀ r, ‖(∫ c, (law c).complexMean (fun z => (test (image z r) : ℂ)) ∂μ) -
      (parent : ℂ)‖ ≤ η)
    (hcollision : ∀ c, (law c).mean (fun z => noninjectivityIndicator (image z)) ≤ σ / 16) :
    ∃ c, σ / 4 ≤ (law c).mass (Finset.univ.filter (fun z =>
      Function.Injective (image z) ∧ σ / 2 ≤ sites.mean (fun r => test (image z r)))) := by
  apply exists_productive_injective_center μ law sites image test hσ hη hparent htest
  · intro r
    have hi := (hint r).re
    change Integrable (fun c => ((law c).complexMean
      (fun z => (test (image z r) : ℂ))).re) μ at hi
    simpa only [FiniteProbabilityWeights.complexMean_ofReal, Complex.ofReal_re] using hi
  · intro r
    have h := hmarginal r
    simp only [FiniteProbabilityWeights.complexMean_ofReal, integral_complex_ofReal,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
    linarith [(abs_le.mp h).1]
  · exact hcollision

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

theorem integral_productive_sampler_mass {C Ω : Type*}
    [MeasurableSpace C] [Fintype Ω]
    (μ : Measure C) [IsProbabilityMeasure μ]
    (law : C → FiniteProbabilityWeights Ω) (score : C → Ω → ℝ)
    (bad : C → Finset Ω) {σ : ℝ} (hσ : 0 < σ)
    (hscore : ∀ c z, score c z ≤ 1)
    (hiScore : Integrable (fun c => (law c).mean (score c)) μ)
    (hiBad : Integrable (fun c => (law c).mass (bad c)) μ)
    (hiProductive : Integrable (fun c => (law c).mass
      (Finset.univ.filter (fun z => z ∉ bad c ∧ σ / 2 ≤ score c z))) μ)
    (hmean : 7 * σ / 8 ≤ ∫ c, (law c).mean (score c) ∂μ)
    (hbad : (∫ c, (law c).mass (bad c) ∂μ) ≤ σ / 16) :
    σ / 4 ≤ ∫ c, (law c).mass
      (Finset.univ.filter (fun z => z ∉ bad c ∧ σ / 2 ≤ score c z)) ∂μ := by
  have h := integral_mono ((hiScore.sub (integrable_const (σ / 2))).sub hiBad)
    hiProductive (fun c => (law c).productive_mass_lower_bound (score c) (bad c)
      (by positivity : 0 ≤ σ / 2) (hscore c))
  simp only [Pi.sub_apply] at h
  rw [integral_sub (f := fun c => (law c).mean (score c) - σ / 2)
      (g := fun c => (law c).mass (bad c))
      (hiScore.sub (integrable_const (σ / 2))) hiBad,
    integral_sub hiScore (integrable_const (σ / 2)),
    integral_const, probReal_univ, one_smul] at h
  linarith

theorem integral_productive_injective_mass {C Ω R Y : Type*}
    [MeasurableSpace C] [Fintype Ω] [Fintype R]
    (μ : Measure C) [IsProbabilityMeasure μ]
    (law : C → FiniteProbabilityWeights Ω) (sites : FiniteProbabilityWeights R)
    (image : Ω → R → Y) (test : Y → ℝ)
    {σ η parent : ℝ} (hσ : 0 < σ) (hη : η ≤ σ / 8) (hparent : σ ≤ parent)
    (htest : ∀ y, test y ≤ 1)
    (hint : ∀ r, Integrable (fun c => (law c).mean (fun z => test (image z r))) μ)
    (hmarginal : ∀ r, parent - η ≤ ∫ c, (law c).mean (fun z => test (image z r)) ∂μ)
    (hiBad : Integrable (fun c => (law c).mean
      (fun z => noninjectivityIndicator (image z))) μ)
    (hiProductive : Integrable (fun c => (law c).mass (Finset.univ.filter (fun z =>
      Function.Injective (image z) ∧ σ / 2 ≤ sites.mean (fun r => test (image z r))))) μ)
    (hcollision : (∫ c, (law c).mean (fun z => noninjectivityIndicator (image z)) ∂μ) ≤ σ / 16) :
    σ / 4 ≤ ∫ c, (law c).mass (Finset.univ.filter (fun z =>
      Function.Injective (image z) ∧ σ / 2 ≤ sites.mean (fun r => test (image z r)))) ∂μ := by
  let score := fun z => sites.mean (fun r => test (image z r))
  let bad := Finset.univ.filter (fun z => ¬Function.Injective (image z))
  have hscore (z) : score z ≤ 1 := by
    calc
      _ ≤ sites.mean (fun _ => 1) := sites.mean_mono (fun r => htest _)
      _ = 1 := sites.mean_const 1
  have hbad (c) : (law c).mass bad =
      (law c).mean (fun z => noninjectivityIndicator (image z)) := by
    rw [← (law c).mean_indicator]
    congr 1
    funext z
    by_cases hz : Function.Injective (image z) <;> simp [bad, hz, noninjectivityIndicator]
  have hprod : (Finset.univ.filter (fun z => z ∉ bad ∧ σ / 2 ≤ score z)) =
      Finset.univ.filter (fun z => Function.Injective (image z) ∧
        σ / 2 ≤ sites.mean (fun r => test (image z r))) := by
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and, not_not, score]
  have he (c) : (law c).mean score =
      sites.mean (fun r => (law c).mean (fun z => test (image z r))) :=
    (law c).mean_comm sites (fun z r => test (image z r))
  have hi : Integrable (fun c => (law c).mean score) μ := by
    simp_rw [he]
    exact sites.mean_integrable μ _ hint
  have havg : 7 * σ / 8 ≤ ∫ c, (law c).mean score ∂μ := by
    simp_rw [he]
    rw [sites.integral_mean μ _ hint]
    calc
      _ ≤ parent - η := by linarith
      _ = sites.mean (fun _ => parent - η) := (sites.mean_const _).symm
      _ ≤ _ := sites.mean_mono hmarginal
  have hiBad' : Integrable (fun c => (law c).mass bad) μ := by
    simp_rw [hbad]
    exact hiBad
  have hiProd' : Integrable (fun c => (law c).mass
      (Finset.univ.filter (fun z => z ∉ bad ∧ σ / 2 ≤ score z))) μ := by
    simpa only [hprod] using hiProductive
  have hbad' : (∫ c, (law c).mass bad ∂μ) ≤ σ / 16 := by
    simpa only [hbad] using hcollision
  have h := integral_productive_sampler_mass μ law (fun _ => score) (fun _ => bad)
    hσ (fun _ => hscore) hi hiBad' hiProd' havg hbad'
  simpa only [hprod] using h

theorem integral_productive_injective_mass_of_complex_marginals {C Ω R Y : Type*}
    [MeasurableSpace C] [Fintype Ω] [Fintype R]
    (μ : Measure C) [IsProbabilityMeasure μ]
    (law : C → FiniteProbabilityWeights Ω) (sites : FiniteProbabilityWeights R)
    (image : Ω → R → Y) (test : Y → ℝ)
    {σ η parent : ℝ} (hσ : 0 < σ) (hη : η ≤ σ / 8) (hparent : σ ≤ parent)
    (htest : ∀ y, test y ≤ 1)
    (hint : ∀ r, Integrable
      (fun c => (law c).complexMean (fun z => (test (image z r) : ℂ))) μ)
    (hmarginal : ∀ r, ‖(∫ c, (law c).complexMean (fun z => (test (image z r) : ℂ)) ∂μ) -
      (parent : ℂ)‖ ≤ η)
    (hiBad : Integrable (fun c => (law c).mean
      (fun z => noninjectivityIndicator (image z))) μ)
    (hiProductive : Integrable (fun c => (law c).mass (Finset.univ.filter (fun z =>
      Function.Injective (image z) ∧ σ / 2 ≤ sites.mean (fun r => test (image z r))))) μ)
    (hcollision : (∫ c, (law c).mean (fun z => noninjectivityIndicator (image z)) ∂μ) ≤ σ / 16) :
    σ / 4 ≤ ∫ c, (law c).mass (Finset.univ.filter (fun z =>
      Function.Injective (image z) ∧ σ / 2 ≤ sites.mean (fun r => test (image z r)))) ∂μ := by
  apply integral_productive_injective_mass μ law sites image test hσ hη hparent htest
  · intro r
    have hi := (hint r).re
    change Integrable (fun c => ((law c).complexMean
      (fun z => (test (image z r) : ℂ))).re) μ at hi
    simpa only [FiniteProbabilityWeights.complexMean_ofReal, Complex.ofReal_re] using hi
  · intro r
    have h := hmarginal r
    simp only [FiniteProbabilityWeights.complexMean_ofReal, integral_complex_ofReal,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h
    linarith [(abs_le.mp h).1]
  · exact hiBad
  · exact hiProductive
  · exact hcollision

end Erdos3

end

end OAI
