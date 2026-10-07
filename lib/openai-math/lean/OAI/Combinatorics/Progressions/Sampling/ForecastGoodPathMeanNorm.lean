import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import OAI.Combinatorics.Progressions.Estimates.FiniteFiberTest

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem forecastUniformAtomTransfer
    {Sample Term : Type*} [Fintype Sample] [Fintype Term]
    (μ : FiniteProbabilityWeights Sample)
    (target signal : Sample → ℂ) (coefficient : Term → ℂ)
    (atom : Term → Sample → ℂ) {M ε δ : ℝ}
    (hε : 0 ≤ ε)
    (happrox : ∀ x, ‖target x - ∑ t, coefficient t * atom t x‖ ≤ δ)
    (hmass : (∑ t, ‖coefficient t‖) ≤ M)
    (hsignal : ∀ x, ‖signal x‖ ≤ 1)
    (hatom : ∀ t, ‖μ.complexMean (fun x => signal x * atom t x)‖ ≤ ε) :
    ‖μ.complexMean (fun x => signal x * target x)‖ ≤ M * ε + δ := by
  let model := fun x => ∑ t, coefficient t * atom t x
  have hmodel : μ.complexMean (fun x => signal x * model x) =
      ∑ t, coefficient t * μ.complexMean (fun x => signal x * atom t x) := by
    unfold FiniteProbabilityWeights.complexMean
    simp only [model, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hmodelBound : ‖μ.complexMean (fun x => signal x * model x)‖ ≤ M * ε := by
    rw [hmodel]
    calc
      _ ≤ ∑ t, ‖coefficient t * μ.complexMean (fun x => signal x * atom t x)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ t, ‖coefficient t‖ * ε := by
        apply Finset.sum_le_sum
        intro t _
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hatom t) (norm_nonneg _)
      _ = (∑ t, ‖coefficient t‖) * ε := (Finset.sum_mul ..).symm
      _ ≤ M * ε := mul_le_mul_of_nonneg_right hmass hε
  have herror : ‖μ.complexMean (fun x => signal x * target x) -
      μ.complexMean (fun x => signal x * model x)‖ ≤ δ := by
    apply (μ.norm_complexMean_sub_le _ _ (fun _ => δ) ?_).trans_eq (μ.mean_const δ)
    intro x _
    rw [← mul_sub, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hsignal x)).trans (happrox x)
  have htriangle := norm_sub_le_norm_sub_add_norm_sub
    (μ.complexMean (fun x => signal x * target x))
    (μ.complexMean (fun x => signal x * model x)) 0
  simp only [sub_zero] at htriangle
  exact (htriangle.trans (add_le_add herror hmodelBound)).trans_eq (add_comm δ (M * ε))

theorem forecastUniformAtomTransfer_outer
    {Path Sample : Type*} [Fintype Path] [Fintype Sample]
    (p : FiniteProbabilityWeights Path) (μ : Path → FiniteProbabilityWeights Sample)
    (Term : Path → Type*) [∀ path, Fintype (Term path)]
    (target signal : Path → Sample → ℂ)
    (coefficient : (path : Path) → Term path → ℂ)
    (atom : (path : Path) → Term path → Sample → ℂ) {M ε δ : ℝ}
    (hε : 0 ≤ ε)
    (happrox : ∀ path x, ‖target path x - ∑ t, coefficient path t * atom path t x‖ ≤ δ)
    (hmass : ∀ path, (∑ t, ‖coefficient path t‖) ≤ M)
    (hsignal : ∀ path x, ‖signal path x‖ ≤ 1)
    (hatom : ∀ path t,
      ‖(μ path).complexMean (fun x => signal path x * atom path t x)‖ ≤ ε) :
    ‖p.complexMean (fun path =>
      (μ path).complexMean (fun x => signal path x * target path x))‖ ≤ M * ε + δ := by
  apply (p.norm_complexMean_le_mean_norm _).trans
  exact (p.mean_mono (fun path => forecastUniformAtomTransfer (μ path)
    (target path) (signal path) (coefficient path) (atom path) hε
    (happrox path) (hmass path) (hsignal path) (hatom path))).trans_eq
    (p.mean_const (M * ε + δ))

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators

theorem forecastBoundedSignalTransfer
    {Sample Term : Type*} [Fintype Sample] [Fintype Term]
    (μ : FiniteProbabilityWeights Sample)
    (target signal : Sample → ℂ) (coefficient : Term → ℂ)
    (atom : Term → Sample → ℂ) {M ε δ B : ℝ}
    (hε : 0 ≤ ε) (hB : 0 ≤ B)
    (happrox : ∀ x, ‖target x - ∑ t, coefficient t * atom t x‖ ≤ δ)
    (hmass : (∑ t, ‖coefficient t‖) ≤ M)
    (hsignal : ∀ x, ‖signal x‖ ≤ B)
    (hatom : ∀ t, ‖μ.complexMean (fun x => signal x * atom t x)‖ ≤ ε) :
    ‖μ.complexMean (fun x => signal x * target x)‖ ≤ M * ε + B * δ := by
  let model := fun x => ∑ t, coefficient t * atom t x
  have hmodel : μ.complexMean (fun x => signal x * model x) =
      ∑ t, coefficient t * μ.complexMean (fun x => signal x * atom t x) := by
    unfold FiniteProbabilityWeights.complexMean
    simp only [model, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    apply Finset.sum_congr rfl
    intro x _
    ring
  have hmodelBound : ‖μ.complexMean (fun x => signal x * model x)‖ ≤ M * ε := by
    rw [hmodel]
    calc
      _ ≤ ∑ t, ‖coefficient t * μ.complexMean (fun x => signal x * atom t x)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ t, ‖coefficient t‖ * ε := by
        apply Finset.sum_le_sum
        intro t _
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hatom t) (norm_nonneg _)
      _ = (∑ t, ‖coefficient t‖) * ε := (Finset.sum_mul ..).symm
      _ ≤ M * ε := mul_le_mul_of_nonneg_right hmass hε
  have herror : ‖μ.complexMean (fun x => signal x * target x) -
      μ.complexMean (fun x => signal x * model x)‖ ≤ B * δ := by
    apply (μ.norm_complexMean_sub_le _ _ (fun _ => B * δ) ?_).trans_eq (μ.mean_const (B * δ))
    intro x _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (hsignal x) (happrox x) (norm_nonneg _) hB
  have htriangle := norm_sub_le_norm_sub_add_norm_sub
    (μ.complexMean (fun x => signal x * target x))
    (μ.complexMean (fun x => signal x * model x)) 0
  simp only [sub_zero] at htriangle
  exact (htriangle.trans (add_le_add herror hmodelBound)).trans_eq (add_comm (B * δ) (M * ε))

theorem exists_forecast_detecting_atom
    {Sample Term : Type*} [Fintype Sample] [Fintype Term]
    (μ : FiniteProbabilityWeights Sample) (target signal : Sample → ℂ)
    (coefficient : Term → ℂ) (atom : Term → Sample → ℂ)
    {a B M : ℝ} (ha : 0 < a) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hsignal : ∀ x, ‖signal x‖ ≤ B)
    (happrox : ∀ x, ‖target x - ∑ t, coefficient t * atom t x‖ ≤ a / (2 * (B + 1)))
    (hmass : (∑ t, ‖coefficient t‖) ≤ M)
    (hlarge : a ≤ ‖μ.complexMean (fun x => signal x * target x)‖) :
    ∃ t, a / (4 * (M + 1)) ≤ ‖μ.complexMean (fun x => signal x * atom t x)‖ := by
  by_contra! hn
  have hu := forecastBoundedSignalTransfer μ target signal coefficient atom
    (show 0 ≤ a / (4 * (M + 1)) by positivity) hB happrox hmass hsignal
    (fun t => (hn t).le)
  have hm : M * (a / (4 * (M + 1))) ≤ a / 4 := by
    rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < 4 * (M + 1))]
    nlinarith
  have hb : B * (a / (2 * (B + 1))) ≤ a / 2 := by
    rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < 2 * (B + 1))]
    nlinarith
  linarith

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

universe uTerm

theorem forecastUniformAtomTransfer_integral_of_exists
    {Path Sample : Type*} [MeasurableSpace Path] [Fintype Sample]
    (p : Measure Path) [IsProbabilityMeasure p]
    (μ : Path → FiniteProbabilityWeights Sample)
    (target signal : Path → Sample → ℂ) {M ε δ : ℝ}
    (hε : 0 ≤ ε)
    (hmeas : AEStronglyMeasurable (fun path =>
      (μ path).complexMean (fun x => signal path x * target path x)) p)
    (hsignal : ∀ᵐ path ∂p, ∀ x, ‖signal path x‖ ≤ 1)
    (hmodels : ∀ᵐ path ∂p,
      ∃ (Term : Type uTerm) (termFinite : Fintype Term),
        let _ := termFinite
        ∃ (coefficient : Term → ℂ) (atom : Term → Sample → ℂ),
          (∀ x, ‖target path x - ∑ t, coefficient t * atom t x‖ ≤ δ) ∧
          (∑ t, ‖coefficient t‖) ≤ M ∧
          ∀ t, ‖(μ path).complexMean (fun x => signal path x * atom t x)‖ ≤ ε) :
    Integrable (fun path =>
      (μ path).complexMean (fun x => signal path x * target path x)) p ∧
    ‖∫ path, (μ path).complexMean (fun x => signal path x * target path x) ∂p‖ ≤
      M * ε + δ := by
  have hbound : ∀ᵐ path ∂p,
      ‖(μ path).complexMean (fun x => signal path x * target path x)‖ ≤ M * ε + δ := by
    filter_upwards [hsignal, hmodels] with path hs hm
    obtain ⟨Term, termFinite, coefficient, atom, happ, hmass, hatom⟩ := hm
    let _ := termFinite
    exact forecastUniformAtomTransfer (μ path) (target path) (signal path)
      coefficient atom hε happ hmass hs hatom
  refine ⟨Integrable.of_bound hmeas (M * ε + δ) hbound, ?_⟩
  simpa only [probReal_univ, mul_one] using norm_integral_le_of_norm_le_const hbound

theorem forecastUniformAtomTransfer_integral
    {Path Sample : Type*} [MeasurableSpace Path] [Fintype Sample]
    (p : Measure Path) [IsProbabilityMeasure p]
    (μ : Path → FiniteProbabilityWeights Sample)
    (Term : Path → Type uTerm) [∀ path, Fintype (Term path)]
    (target signal : Path → Sample → ℂ)
    (coefficient : (path : Path) → Term path → ℂ)
    (atom : (path : Path) → Term path → Sample → ℂ) {M ε δ : ℝ}
    (hε : 0 ≤ ε)
    (hmeas : AEStronglyMeasurable (fun path =>
      (μ path).complexMean (fun x => signal path x * target path x)) p)
    (happrox : ∀ᵐ path ∂p,
      ∀ x, ‖target path x - ∑ t, coefficient path t * atom path t x‖ ≤ δ)
    (hmass : ∀ᵐ path ∂p, (∑ t, ‖coefficient path t‖) ≤ M)
    (hsignal : ∀ᵐ path ∂p, ∀ x, ‖signal path x‖ ≤ 1)
    (hatom : ∀ᵐ path ∂p, ∀ t,
      ‖(μ path).complexMean (fun x => signal path x * atom path t x)‖ ≤ ε) :
    Integrable (fun path =>
      (μ path).complexMean (fun x => signal path x * target path x)) p ∧
    ‖∫ path, (μ path).complexMean (fun x => signal path x * target path x) ∂p‖ ≤
      M * ε + δ := by
  apply forecastUniformAtomTransfer_integral_of_exists p μ target signal hε hmeas hsignal
  filter_upwards [happrox, hmass, hatom] with path happ hm ha
  exact ⟨Term path, inferInstance, coefficient path, atom path, happ, hm, ha⟩

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators
universe uTerm

theorem norm_integral_le_good_bound_add_exception
    {Path : Type*} [MeasurableSpace Path] (p : Measure Path) [IsProbabilityMeasure p]
    (f : Path → ℂ) (bad : Set Path) (hbad : MeasurableSet bad)
    {B C η : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hmeas : AEStronglyMeasurable f p)
    (hglobal : ∀ᵐ path ∂p, ‖f path‖ ≤ B)
    (hgood : ∀ᵐ path ∂p, path ∉ bad → ‖f path‖ ≤ C)
    (hprob : p.real bad ≤ η) :
    Integrable f p ∧ ‖∫ path, f path ∂p‖ ≤ C + B * η := by
  have hf : Integrable f p := Integrable.of_bound hmeas B hglobal
  have hbi : Integrable (bad.indicator (fun _ : Path => B)) p :=
    (integrable_const B).indicator hbad
  have henv : ∀ᵐ path ∂p, ‖f path‖ ≤ C + bad.indicator (fun _ : Path => B) path := by
    filter_upwards [hglobal, hgood] with path hg hh
    by_cases hx : path ∈ bad
    · simp only [Set.indicator_of_mem hx]
      linarith
    · simpa only [Set.indicator_of_notMem hx, add_zero] using hh hx
  refine ⟨hf, ?_⟩
  calc
    _ ≤ ∫ path, ‖f path‖ ∂p := norm_integral_le_integral_norm f
    _ ≤ ∫ path, C + bad.indicator (fun _ : Path => B) path ∂p :=
      integral_mono_ae hf.norm ((integrable_const C).add hbi) henv
    _ = C + B * p.real bad := by
      rw [integral_add (integrable_const C) hbi, integral_const,
        integral_indicator_const B hbad, probReal_univ, one_smul, smul_eq_mul, mul_comm]
    _ ≤ C + B * η := add_le_add_right (mul_le_mul_of_nonneg_left hprob hB) C

theorem forecastUniformAtomTransfer_integral_of_exists_off_exception
    {Path Sample : Type*} [MeasurableSpace Path] [Fintype Sample]
    (p : Measure Path) [IsProbabilityMeasure p]
    (μ : Path → FiniteProbabilityWeights Sample)
    (target signal : Path → Sample → ℂ) (bad : Set Path) (hbad : MeasurableSet bad)
    {M ε δ B η : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (hmeas : AEStronglyMeasurable (fun path =>
      (μ path).complexMean (fun x => signal path x * target path x)) p)
    (hglobal : ∀ᵐ path ∂p,
      ‖(μ path).complexMean (fun x => signal path x * target path x)‖ ≤ B)
    (hsignal : ∀ᵐ path ∂p, ∀ x, ‖signal path x‖ ≤ 1)
    (hmodels : ∀ᵐ path ∂p, path ∉ bad →
      ∃ (Term : Type uTerm) (termFinite : Fintype Term),
        let _ := termFinite
        ∃ (coefficient : Term → ℂ) (atom : Term → Sample → ℂ),
          (∀ x, ‖target path x - ∑ t, coefficient t * atom t x‖ ≤ δ) ∧
          (∑ t, ‖coefficient t‖) ≤ M ∧
          ∀ t, ‖(μ path).complexMean (fun x => signal path x * atom t x)‖ ≤ ε)
    (hprob : p.real bad ≤ η) :
    Integrable (fun path =>
      (μ path).complexMean (fun x => signal path x * target path x)) p ∧
    ‖∫ path, (μ path).complexMean (fun x => signal path x * target path x) ∂p‖ ≤
      M * ε + δ + B * η := by
  apply norm_integral_le_good_bound_add_exception p _ bad hbad hB
    (add_nonneg (mul_nonneg hM hε) hδ) hmeas hglobal _ hprob
  filter_upwards [hsignal, hmodels] with path hs hm
  intro hg
  obtain ⟨Term, termFinite, coefficient, atom, happ, hmass, hatom⟩ := hm hg
  let _ := termFinite
  exact forecastUniformAtomTransfer (μ path) (target path) (signal path)
    coefficient atom hε happ hmass hs hatom

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators
universe uTerm

theorem integral_norm_le_good_bound_add_exception
    {Path : Type*} [MeasurableSpace Path] (p : Measure Path) [IsProbabilityMeasure p]
    (f : Path → ℂ) (bad : Set Path) (hbad : MeasurableSet bad)
    {B C η : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hmeas : AEStronglyMeasurable f p)
    (hglobal : ∀ᵐ path ∂p, ‖f path‖ ≤ B)
    (hgood : ∀ᵐ path ∂p, path ∉ bad → ‖f path‖ ≤ C)
    (hprob : p.real bad ≤ η) :
    Integrable f p ∧ (∫ path, ‖f path‖ ∂p) ≤ C + B * η := by
  have hf : Integrable f p := Integrable.of_bound hmeas B hglobal
  have hbi : Integrable (bad.indicator (fun _ : Path => B)) p :=
    (integrable_const B).indicator hbad
  have henv : ∀ᵐ path ∂p, ‖f path‖ ≤ C + bad.indicator (fun _ : Path => B) path := by
    filter_upwards [hglobal, hgood] with path hg hh
    by_cases hx : path ∈ bad
    · simp only [Set.indicator_of_mem hx]
      linarith
    · simpa only [Set.indicator_of_notMem hx, add_zero] using hh hx
  refine ⟨hf, ?_⟩
  calc
    _ ≤ ∫ path, C + bad.indicator (fun _ : Path => B) path ∂p :=
      integral_mono_ae hf.norm ((integrable_const C).add hbi) henv
    _ = C + B * p.real bad := by
      rw [integral_add (integrable_const C) hbi, integral_const,
        integral_indicator_const B hbad, probReal_univ, one_smul, smul_eq_mul, mul_comm]
    _ ≤ C + B * η := add_le_add_right (mul_le_mul_of_nonneg_left hprob hB) C

theorem forecastUniformAtomTransfer_mean_norm_of_exists_off_exception
    {Path Sample : Type*} [MeasurableSpace Path] [Fintype Sample]
    (p : Measure Path) [IsProbabilityMeasure p]
    (μ : Path → FiniteProbabilityWeights Sample)
    (target signal : Path → Sample → ℂ) (bad : Set Path) (hbad : MeasurableSet bad)
    {M ε δ B η : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hB : 0 ≤ B)
    (hmeas : AEStronglyMeasurable (fun path =>
      (μ path).complexMean (fun x => signal path x * target path x)) p)
    (hglobal : ∀ᵐ path ∂p,
      ‖(μ path).complexMean (fun x => signal path x * target path x)‖ ≤ B)
    (hsignal : ∀ᵐ path ∂p, ∀ x, ‖signal path x‖ ≤ 1)
    (hmodels : ∀ᵐ path ∂p, path ∉ bad →
      ∃ (Term : Type uTerm) (termFinite : Fintype Term),
        let _ := termFinite
        ∃ (coefficient : Term → ℂ) (atom : Term → Sample → ℂ),
          (∀ x, ‖target path x - ∑ t, coefficient t * atom t x‖ ≤ δ) ∧
          (∑ t, ‖coefficient t‖) ≤ M ∧
          ∀ t, ‖(μ path).complexMean (fun x => signal path x * atom t x)‖ ≤ ε)
    (hprob : p.real bad ≤ η) :
    Integrable (fun path =>
      (μ path).complexMean (fun x => signal path x * target path x)) p ∧
    (∫ path, ‖(μ path).complexMean (fun x => signal path x * target path x)‖ ∂p) ≤
      M * ε + δ + B * η := by
  apply integral_norm_le_good_bound_add_exception p _ bad hbad hB
    (add_nonneg (mul_nonneg hM hε) hδ) hmeas hglobal _ hprob
  filter_upwards [hsignal, hmodels] with path hs hm
  intro hg
  obtain ⟨Term, termFinite, coefficient, atom, happ, hmass, hatom⟩ := hm hg
  let _ := termFinite
  exact forecastUniformAtomTransfer (μ path) (target path) (signal path)
    coefficient atom hε happ hmass hs hatom

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators
universe uTerm

theorem physicalForecastComparison_mean_norm
    {Path Sample : Type*} [MeasurableSpace Path] [Fintype Sample]
    (p : Measure Path) [IsProbabilityMeasure p]
    (actual : Path → ℂ) (μ : Path → FiniteProbabilityWeights Sample)
    (target signal : Path → Sample → ℂ) (bad : Set Path) (hbad : MeasurableSet bad)
    {M ε δ ζ B η : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (hζ : 0 ≤ ζ) (hB : 0 ≤ B)
    (hmeas : AEStronglyMeasurable actual p)
    (hglobal : ∀ᵐ path ∂p, ‖actual path‖ ≤ B)
    (hcomparison : ∀ᵐ path ∂p, path ∉ bad →
      ‖actual path - (μ path).complexMean (fun x => signal path x * target path x)‖ ≤ ζ)
    (hsignal : ∀ᵐ path ∂p, path ∉ bad → ∀ x, ‖signal path x‖ ≤ 1)
    (hmodels : ∀ᵐ path ∂p, path ∉ bad →
      ∃ (Term : Type uTerm) (termFinite : Fintype Term),
        let _ := termFinite
        ∃ (coefficient : Term → ℂ) (atom : Term → Sample → ℂ),
          (∀ x, ‖target path x - ∑ t, coefficient t * atom t x‖ ≤ δ) ∧
          (∑ t, ‖coefficient t‖) ≤ M ∧
          ∀ t, ‖(μ path).complexMean (fun x => signal path x * atom t x)‖ ≤ ε)
    (hprob : p.real bad ≤ η) :
    Integrable actual p ∧ (∫ path, ‖actual path‖ ∂p) ≤ ζ + (M * ε + δ) + B * η := by
  apply integral_norm_le_good_bound_add_exception p actual bad hbad hB
    (add_nonneg hζ (add_nonneg (mul_nonneg hM hε) hδ)) hmeas hglobal _ hprob
  filter_upwards [hcomparison, hsignal, hmodels] with path hcomp hs hm
  intro hg
  obtain ⟨Term, termFinite, coefficient, atom, happ, hmass, hatom⟩ := hm hg
  let _ := termFinite
  have hc := forecastUniformAtomTransfer (μ path) (target path) (signal path)
    coefficient atom hε happ hmass (hs hg) hatom
  have ht := norm_sub_le_norm_sub_add_norm_sub (actual path)
    ((μ path).complexMean (fun x => signal path x * target path x)) 0
  simp only [sub_zero] at ht
  exact ht.trans (add_le_add (hcomp hg) hc)

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators
universe uTerm

theorem integral_norm_off_exception_le
    {Path : Type*} [MeasurableSpace Path]
    (p : Measure Path) [IsProbabilityMeasure p]
    (f : Path → ℂ) (bad : Set Path) (hbad : MeasurableSet bad)
    {C : ℝ} (hC : 0 ≤ C) (hmeas : AEStronglyMeasurable f p)
    (hgood : ∀ᵐ path ∂p, path ∉ bad → ‖f path‖ ≤ C) :
    Integrable (badᶜ.indicator f) p ∧
      (∫ path, ‖badᶜ.indicator f path‖ ∂p) ≤ C := by
  have hbound : ∀ᵐ path ∂p, ‖badᶜ.indicator f path‖ ≤ C := by
    filter_upwards [hgood] with path hg
    by_cases hb : path ∈ badᶜ
    · simpa only [Set.indicator_of_mem hb] using hg hb
    · simpa only [Set.indicator_of_notMem hb, norm_zero] using hC
  have hi : Integrable (badᶜ.indicator f) p :=
    Integrable.of_bound (hmeas.indicator hbad.compl) C hbound
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ _, C ∂p := integral_mono_ae hi.norm (integrable_const C) hbound
    _ = C := by simp

theorem physicalForecastComparison_good_mean_norm
    {Path Sample : Type*} [MeasurableSpace Path] [Fintype Sample]
    (p : Measure Path) [IsProbabilityMeasure p]
    (actual : Path → ℂ) (μ : Path → FiniteProbabilityWeights Sample)
    (target signal : Path → Sample → ℂ) (bad : Set Path) (hbad : MeasurableSet bad)
    {M ε δ ζ : ℝ} (hM : 0 ≤ M) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hζ : 0 ≤ ζ)
    (hmeas : AEStronglyMeasurable actual p)
    (hcomparison : ∀ᵐ path ∂p, path ∉ bad →
      ‖actual path - (μ path).complexMean (fun x => signal path x * target path x)‖ ≤ ζ)
    (hsignal : ∀ᵐ path ∂p, path ∉ bad → ∀ x, ‖signal path x‖ ≤ 1)
    (hmodels : ∀ᵐ path ∂p, path ∉ bad →
      ∃ (Term : Type uTerm) (termFinite : Fintype Term),
        let _ := termFinite
        ∃ (coefficient : Term → ℂ) (atom : Term → Sample → ℂ),
          (∀ x, ‖target path x - ∑ t, coefficient t * atom t x‖ ≤ δ) ∧
          (∑ t, ‖coefficient t‖) ≤ M ∧
          ∀ t, ‖(μ path).complexMean (fun x => signal path x * atom t x)‖ ≤ ε) :
    Integrable (badᶜ.indicator actual) p ∧
      (∫ path, ‖badᶜ.indicator actual path‖ ∂p) ≤ ζ + (M * ε + δ) := by
  apply integral_norm_off_exception_le p actual bad hbad
    (add_nonneg hζ (add_nonneg (mul_nonneg hM hε) hδ)) hmeas
  filter_upwards [hcomparison, hsignal, hmodels] with path hcomp hs hm
  intro hg
  obtain ⟨Term, termFinite, coefficient, atom, happ, hmass, hatom⟩ := hm hg
  let _ := termFinite
  have hc := forecastUniformAtomTransfer (μ path) (target path) (signal path)
    coefficient atom hε happ hmass (hs hg) hatom
  have ht := norm_sub_le_norm_sub_add_norm_sub (actual path)
    ((μ path).complexMean (fun x => signal path x * target path x)) 0
  simp only [sub_zero] at ht
  exact ht.trans (add_le_add (hcomp hg) hc)

end Erdos3

end

end OAI
