-- Modified for ProveIt: in positiveRestriction_mean and positiveRestriction_complexMean, `; all_goals rfl` after `rw [dite_eq_left ...]` (rw does not close the goal by rfl in Lean 4.32.0).
-- Modified for ProveIt: added `import OAI.Compat.*` lines (backported names); see lib/openai-math/README.md.
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import OAI.Combinatorics.Progressions.Estimates.CorrelationDerivative
import OAI.Combinatorics.Progressions.Estimates.UnitExpansionCorrelation
import OAI.Compat.Core

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

def finiteMask (G : Finset Ω) : (Ω → ℂ) →ₗ[ℂ] (Ω → ℂ) where
  toFun v x := if x ∈ G then v x else 0
  map_add' v w := by ext x; by_cases hx : x ∈ G <;> simp [hx]
  map_smul' c v := by ext x; by_cases hx : x ∈ G <;> simp [hx]

omit [Fintype Ω] in
@[simp] theorem finiteMask_apply (G : Finset Ω) (v : Ω → ℂ) (x : Ω) :
    finiteMask G v x = if x ∈ G then v x else 0 := rfl

namespace FiniteProbabilityWeights

variable (p : FiniteProbabilityWeights Ω) (G : Finset Ω)

omit [DecidableEq Ω] in
theorem mean_add (f g : Ω → ℝ) :
    p.mean (fun x => f x + g x) = p.mean f + p.mean g := by
  simp [mean, mul_add, Finset.sum_add_distrib]

omit [DecidableEq Ω] in
theorem mean_const_mul (c : ℝ) (f : Ω → ℝ) :
    p.mean (fun x => c * f x) = c * p.mean f := by
  simp only [mean, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

noncomputable def mass : ℝ := ∑ x ∈ G, p.weight x

omit [DecidableEq Ω] in
theorem mass_nonneg : 0 ≤ p.mass G :=
  Finset.sum_nonneg (fun x _ => p.nonneg x)

omit [DecidableEq Ω] in
theorem mass_le_one : p.mass G ≤ 1 := by
  rw [← p.total]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ G)
    (fun x _ _ => p.nonneg x)

omit [DecidableEq Ω] in
theorem weight_le_mass {x : Ω} (hx : x ∈ G) : p.weight x ≤ p.mass G :=
  Finset.single_le_sum (fun y _ => p.nonneg y) hx

theorem mean_indicator : p.mean (fun x => if x ∈ G then 1 else 0) = p.mass G := by
  simp [mean, mass, mul_ite]

noncomputable def condition (hG : 0 < p.mass G) : FiniteProbabilityWeights Ω where
  weight x := (if x ∈ G then p.weight x else 0) / p.mass G
  nonneg x := div_nonneg (by split_ifs; exact p.nonneg x; exact le_rfl) hG.le
  total := by
    rw [← Finset.sum_div]
    have hsum : (∑ x, if x ∈ G then p.weight x else 0) = p.mass G := by
      simp [mass]
    rw [hsum, div_self hG.ne']

theorem condition_mean (hG : 0 < p.mass G) (f : Ω → ℝ) :
    (p.condition G hG).mean f =
      p.mean (fun x => if x ∈ G then f x else 0) / p.mass G := by
  unfold mean condition
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x ∈ G <;> simp [hx, div_mul_eq_mul_div]

theorem mass_mul_condition_mean (hG : 0 < p.mass G) (f : Ω → ℝ) :
    p.mass G * (p.condition G hG).mean f =
      p.mean (fun x => if x ∈ G then f x else 0) := by
  rw [condition_mean, mul_div_cancel₀ _ hG.ne']

theorem mass_mul_condition_correlation (hG : 0 < p.mass G) (v Q : Ω → ℂ) :
    (p.mass G : ℂ) * (p.condition G hG).correlation v Q =
      p.correlation (finiteMask G v) Q := by
  unfold correlation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x ∈ G
  · simp only [condition, hx, ite_true, finiteMask_apply]
    have hm : (p.mass G : ℂ) ≠ 0 := by exact_mod_cast hG.ne'
    push_cast
    field_simp
  · simp [condition, hx]

theorem norm_correlation_mask (hG : 0 < p.mass G) (v Q : Ω → ℂ) :
    ‖p.correlation (finiteMask G v) Q‖ =
      p.mass G * ‖(p.condition G hG).correlation v Q‖ := by
  rw [← mass_mul_condition_correlation, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (p.mass_nonneg G)]

theorem mean_mask_zero (hG : p.mass G = 0) (f : Ω → ℝ) :
    p.mean (fun x => if x ∈ G then f x else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro x _
  by_cases hx : x ∈ G
  · have hw : p.weight x = 0 := le_antisymm
      (by simpa [hG] using p.weight_le_mass G hx) (p.nonneg x)
    simp [hx, hw]
  · simp [hx]

end FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_productive_good_path {H : Type*} [Fintype H]
    (p : FiniteProbabilityWeights H) (productive bad : Finset H) (err : H → ℝ)
    {τ r : ℝ} (hτ : 0 < τ) (hr : 0 < r) (herr : ∀ h, 0 ≤ err h)
    (hproductive : τ ≤ p.mass productive) (hbad : p.mass bad ≤ τ / 4)
    (hmean : p.mean err ≤ τ * r / 4) :
    ∃ h ∈ productive, h ∉ bad ∧ err h ≤ r := by
  classical
  by_contra! hnone
  have hpoint (h : H) : r * (if h ∈ productive then (1 : ℝ) else 0) ≤
      r * (if h ∈ bad then (1 : ℝ) else 0) + err h := by
    by_cases hp : h ∈ productive
    · by_cases hb : h ∈ bad
      · simp only [hp, hb, ite_true, mul_one]
        linarith [herr h]
      · simpa only [hp, hb, ite_true, ite_false, mul_one, mul_zero, zero_add] using
          (hnone h hp hb).le
    · simp only [hp, ite_false, mul_zero]
      exact add_nonneg (mul_nonneg hr.le (by split_ifs <;> norm_num)) (herr h)
  have h := p.mean_mono hpoint
  rw [p.mean_add, p.mean_const_mul, p.mean_const_mul, p.mean_indicator, p.mean_indicator] at h
  have hp := mul_le_mul_of_nonneg_left hproductive hr.le
  have hb := mul_le_mul_of_nonneg_left hbad hr.le
  nlinarith [mul_pos hτ hr]

theorem exists_productive_model_transfer {H V I : Type*} [Fintype H]
    [AddCommGroup V] [Module ℂ V] [Fintype I]
    (p : FiniteProbabilityWeights H) (productive bad : Finset H)
    (A B : H → V →ₗ[ℂ] ℂ) (v e : V) (J : I → V) (c : I → ℂ) (err : H → ℝ)
    (hmodel : v = (∑ i, c i • J i) + e) {τ r M η α ρ : ℝ}
    (hτ : 0 < τ) (hr : 0 < r) (herr : ∀ h, 0 ≤ err h)
    (hproductive : τ ≤ p.mass productive) (hbad : p.mass bad ≤ τ / 4)
    (hmean : p.mean err ≤ τ * r / 4)
    (hη : 0 ≤ η) (hc : (∑ i, ‖c i‖) ≤ M)
    (hatom : ∀ h ∈ productive, h ∉ bad → ∀ i, ‖A h (J i) - B h (J i)‖ ≤ η)
    (heA : ∀ h ∈ productive, h ∉ bad → ‖A h e‖ ≤ α)
    (heB : ∀ h ∈ productive, ‖B h e‖ ≤ err h)
    (hscore : ∀ h ∈ productive, ρ ≤ (B h v).re)
    (hbudget : M * η + α + r ≤ ρ / 2) :
    ∃ h ∈ productive, h ∉ bad ∧ ρ / 2 ≤ (A h v).re := by
  obtain ⟨h, hp, hb, he⟩ := exists_productive_good_path p productive bad err hτ hr herr
    hproductive hbad hmean
  refine ⟨h, hp, hb, ?_⟩
  have hs := finite_model_score_transfer (A h) (B h) v e J c hmodel hη hc
    (hatom h hp hb) (heA h hp hb) ((heB h hp).trans he) (hscore h hp)
  linarith

theorem model_transfer_eighths {M ρ α : ℝ} (hM : 0 ≤ M) (hρ : 0 ≤ ρ) (hα : α ≤ ρ / 8) :
    M * (ρ / (8 * (1 + M))) + α + ρ / 8 ≤ ρ / 2 := by
  have hden : 0 < 8 * (1 + M) := by positivity
  have hm : M * (ρ / (8 * (1 + M))) ≤ ρ / 8 := by
    rw [← mul_div_assoc, div_le_iff₀ hden]
    nlinarith
  linarith

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

theorem complexMean_congr_support {f g : X → ℂ}
    (h : ∀ x, p.weight x ≠ 0 → f x = g x) : p.complexMean f = p.complexMean g := by
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : p.weight x = 0
  · simp only [hx, Complex.ofReal_zero, zero_mul]
  · rw [h x hx]

theorem complexMean_sub (f g : X → ℂ) :
    p.complexMean (fun x => f x - g x) = p.complexMean f - p.complexMean g := by
  simp only [complexMean, mul_sub, Finset.sum_sub_distrib]

theorem complexMean_ofReal (f : X → ℝ) :
    p.complexMean (fun x => (f x : ℂ)) = (p.mean f : ℂ) := by
  simp only [complexMean, mean, Complex.ofReal_sum, Complex.ofReal_mul]

theorem complexMean_ofReal_mul (f : X → ℝ) (z : ℂ) :
    p.complexMean (fun x => (f x : ℂ) * z) = (p.mean f : ℂ) * z := by
  simp only [complexMean, mean, Complex.ofReal_sum, Complex.ofReal_mul,
    Finset.sum_mul, mul_assoc]

theorem complexMean_finset_expect {V : Type*} (s : Finset V) (f : X → V → ℂ) :
    p.complexMean (fun x => 𝔼 v ∈ s, f x v) = 𝔼 v ∈ s, p.complexMean (fun x => f x v) := by
  unfold complexMean
  simp_rw [Finset.mul_expect]
  exact (Finset.expect_sum_comm _ _ _).symm

theorem norm_complexMean_le_mean_norm (f : X → ℂ) :
    ‖p.complexMean f‖ ≤ p.mean (fun x => ‖f x‖) := by
  apply (norm_sum_le _ _).trans_eq
  apply Finset.sum_congr rfl
  intro x _
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (p.nonneg x)]

theorem norm_complexMean_sub_le (f g : X → ℂ) (e : X → ℝ)
    (h : ∀ x, p.weight x ≠ 0 → ‖f x - g x‖ ≤ e x) :
    ‖p.complexMean f - p.complexMean g‖ ≤ p.mean e := by
  rw [← p.complexMean_sub]
  apply (p.norm_complexMean_le_mean_norm _).trans
  apply Finset.sum_le_sum
  intro x _
  by_cases hx : p.weight x = 0
  · simp only [hx, zero_mul, le_refl]
  · exact mul_le_mul_of_nonneg_left (h x hx) (p.nonneg x)

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3
open scoped BigOperators Classical

theorem exists_external_test_bins
    {X Y I : Type*} [Fintype I] [Nonempty I]
    (external : X → Y → ℂ) (center : I → Y → ℂ) {η : ℝ}
    (hnet : ∀ x, ∃ i, ∀ y, ‖external x y - center i y‖ ≤ η) :
    ∃ bin : X → I,
      (∀ x y, ‖external x y - center (bin x) y‖ ≤ η) ∧
      ∀ {T : Type*} [Fintype T] (law : FiniteProbabilityWeights T)
        (site : T → X) (path : T → Y) (signal : X → ℂ) {B δ : ℝ},
        0 ≤ B → 0 < δ → (∀ x, ‖signal x‖ ≤ B) → B * η ≤ δ / 2 →
        δ ≤ ‖law.complexMean (fun t => signal (site t) * external (site t) (path t))‖ →
        ∃ i, δ / (2 * Fintype.card I) ≤
          ‖law.complexMean (fun t =>
            (if bin (site t) = i then signal (site t) else 0) * center i (path t))‖ := by
  choose bin hbin using hnet
  refine ⟨bin, hbin, ?_⟩
  intro T _ law site path signal B δ hB hδ hsignal hsmall hbias
  let term := fun i => law.complexMean (fun t =>
    (if bin (site t) = i then signal (site t) else 0) * center i (path t))
  have hsum : (∑ i, term i) =
      law.complexMean (fun t => signal (site t) * center (bin (site t)) (path t)) := by
    unfold term FiniteProbabilityWeights.complexMean
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    rw [← Finset.mul_sum]
    congr 1
    simp
  have herr : ‖law.complexMean (fun t => signal (site t) * external (site t) (path t)) -
      law.complexMean (fun t => signal (site t) * center (bin (site t)) (path t))‖ ≤ δ / 2 := by
    have he := law.norm_complexMean_sub_le
      (fun t => signal (site t) * external (site t) (path t))
      (fun t => signal (site t) * center (bin (site t)) (path t)) (fun _ => B * η)
      (fun t _ => by
        rw [← mul_sub, norm_mul]
        exact mul_le_mul (hsignal _) (hbin _ _) (norm_nonneg _) hB)
    rw [law.mean_const] at he
    exact he.trans hsmall
  have hlarge : δ / 2 ≤ ‖∑ i, term i‖ := by
    rw [hsum]
    have hh := norm_sub_le_norm_sub_add_norm_sub
      (law.complexMean (fun t => signal (site t) * external (site t) (path t)))
      (law.complexMean (fun t => signal (site t) * center (bin (site t)) (path t))) 0
    simp only [sub_zero] at hh
    linarith
  obtain ⟨i, hi⟩ := exists_large_weighted_term (fun _ : I => (1 : ℂ)) term
    (by positivity : 0 < δ / 2) (Nat.cast_pos.mpr Fintype.card_pos : (0 : ℝ) < Fintype.card I)
    (by simp) (by simpa using hlarge)
  refine ⟨i, ?_⟩
  convert hi using 1
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem norm_complex_profile_sum_sub {T : Type*} [Fintype T]
    (a f g : T → ℂ) :
    ‖(∑ t, a t * f t) - ∑ t, a t * g t‖ ≤ ∑ t, ‖a t‖ * ‖f t - g t‖ := by
  rw [← Finset.sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro t _
  rw [← mul_sub, norm_mul]

theorem norm_nested_complex_profile_reference_sub {Ω R T : Type*}
    [Fintype Ω] [Fintype R] [Fintype T]
    (p : FiniteProbabilityWeights Ω) (q : FiniteProbabilityWeights R)
    (a f g : Ω → R → T → ℂ) {E Z : ℝ} (hZ : 0 < Z)
    (he : ∀ u r, (∑ t, ‖a u r t‖ * ‖f u r t - g u r t‖) ≤ E) :
    ‖p.complexMean (fun u => q.complexMean (fun r => ∑ t, a u r t * f u r t)) / (Z : ℂ) -
      p.complexMean (fun u => q.complexMean (fun r => ∑ t, a u r t * g u r t)) / (Z : ℂ)‖ ≤ E / Z := by
  have hi (u) : ‖q.complexMean (fun r => ∑ t, a u r t * f u r t) -
      q.complexMean (fun r => ∑ t, a u r t * g u r t)‖ ≤ E := by
    exact (q.norm_complexMean_sub_le _ _ (fun _ => E)
      (fun r _ => (norm_complex_profile_sum_sub (a u r) (f u r) (g u r)).trans (he u r))).trans_eq (q.mean_const E)
  have ho := (p.norm_complexMean_sub_le _ _ (fun _ => E) (fun u _ => hi u)).trans_eq (p.mean_const E)
  rw [← sub_div, norm_div, Complex.norm_real, Real.norm_of_nonneg hZ.le]
  exact div_le_div_of_nonneg_right ho hZ.le

theorem finiteComplexMean_sum {X T : Type*} [Fintype X] [Fintype T]
    (p : FiniteProbabilityWeights X) (f : T → X → ℂ) :
    p.complexMean (fun x => ∑ t, f t x) = ∑ t, p.complexMean (f t) := by
  unfold FiniteProbabilityWeights.complexMean
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

theorem finiteComplexMean_const_mul {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (c : ℂ) (f : X → ℂ) :
    p.complexMean (fun x => c * f x) = c * p.complexMean f := by
  unfold FiniteProbabilityWeights.complexMean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X R : Type*} [Fintype X] (p : FiniteProbabilityWeights X)

noncomputable def fiberMean (F : X → R) (r : R) (f : X → ℝ) : ℝ := by
  classical
  exact p.mean (fun x => if F x = r then f x else 0)

theorem fiberMean_nonneg (F : X → R) (r : R) (f : X → ℝ) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ p.fiberMean F r f := by
  classical
  apply p.mean_nonneg
  intro x
  split_ifs
  · exact hf x
  · exact le_rfl

theorem sum_fiberMean [Fintype R] (F : X → R) (f : X → ℝ) :
    (∑ r, p.fiberMean F r f) = p.mean f := by
  classical
  unfold fiberMean mean
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [← Finset.mul_sum]
  simp

noncomputable def fiberLaw [Fintype R] (F : X → R) : FiniteProbabilityWeights R where
  weight r := p.fiberMean F r (fun _ => 1)
  nonneg r := p.fiberMean_nonneg F r (fun _ => 1) (fun _ => zero_le_one)
  total := by rw [p.sum_fiberMean, p.mean_const]

theorem fiberLaw_weight [Fintype R] (F : X → R) (r : R) :
    (p.fiberLaw F).weight r = p.fiberMean F r (fun _ => 1) := rfl

theorem complexMean_fiber_factor [Fintype R] (F : X → R) (f : X → ℝ) (a : R → ℂ) :
    p.complexMean (fun x => (f x : ℂ) * a (F x)) =
      ∑ r, (p.fiberMean F r f : ℂ) * a r := by
  classical
  unfold complexMean fiberMean mean
  simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  have he (r : R) : ((if F x = r then f x else 0 : ℝ) : ℂ) =
      if F x = r then (f x : ℂ) else 0 := by split_ifs <;> rfl
  simp [he, mul_ite, ite_mul, mul_assoc]

theorem fiberMean_eq_mass_mul_condition [DecidableEq X] [DecidableEq R]
    (F : X → R) (r : R) (f : X → ℝ)
    (hr : 0 < p.mass (Finset.univ.filter (fun x => F x = r))) :
    p.fiberMean F r f = p.mass (Finset.univ.filter (fun x => F x = r)) *
      (p.condition (Finset.univ.filter (fun x => F x = r)) hr).mean f := by
  rw [p.mass_mul_condition_mean]
  simp only [fiberMean, Finset.mem_filter, Finset.mem_univ, true_and]
  congr 1
  funext x
  by_cases hx : F x = r <;> simp [hx]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open MeasureTheory
open scoped BigOperators

variable {X C : Type*} [Fintype X] [MeasurableSpace C] (p : FiniteProbabilityWeights X)

theorem mean_measurable (f : C → X → ℝ) (hf : ∀ x, Measurable (fun c => f c x)) :
    Measurable (fun c => p.mean (f c)) :=
  Finset.measurable_sum _ (fun x _ => (hf x).const_mul (p.weight x))

theorem mean_integrable (μ : Measure C) (f : C → X → ℝ)
    (hf : ∀ x, Integrable (fun c => f c x) μ) :
    Integrable (fun c => p.mean (f c)) μ :=
  integrable_finsetSum _ (fun x _ => (hf x).const_mul (p.weight x))

theorem integral_mean (μ : Measure C) (f : C → X → ℝ)
    (hf : ∀ x, Integrable (fun c => f c x) μ) :
    (∫ c, p.mean (f c) ∂μ) = p.mean (fun x => ∫ c, f c x ∂μ) := by
  unfold mean
  rw [integral_finsetSum _ (fun x _ => (hf x).const_mul (p.weight x))]
  simp only [integral_const_mul]

theorem complexMean_measurable (f : C → X → ℂ) (hf : ∀ x, Measurable (fun c => f c x)) :
    Measurable (fun c => p.complexMean (f c)) :=
  Finset.measurable_sum _ (fun x _ => (hf x).const_mul (p.weight x : ℂ))

theorem complexMean_integrable (μ : Measure C) (f : C → X → ℂ)
    (hf : ∀ x, Integrable (fun c => f c x) μ) :
    Integrable (fun c => p.complexMean (f c)) μ :=
  integrable_finsetSum _ (fun x _ => (hf x).const_mul (p.weight x : ℂ))

theorem integral_complexMean (μ : Measure C) (f : C → X → ℂ)
    (hf : ∀ x, Integrable (fun c => f c x) μ) :
    (∫ c, p.complexMean (f c) ∂μ) = p.complexMean (fun x => ∫ c, f c x ∂μ) := by
  unfold complexMean
  rw [integral_finsetSum _ (fun x _ => (hf x).const_mul (p.weight x : ℂ))]
  simp only [integral_const_mul]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights
open scoped BigOperators Classical

noncomputable def pointWeights {Y : Type*} [Fintype Y] (y : Y) : FiniteProbabilityWeights Y where
  weight z := if z = y then 1 else 0
  nonneg z := by split_ifs <;> norm_num
  total := by
    rw [Finset.sum_eq_single y]
    · simp
    · intro z _ hz
      simp [hz]
    · simp

theorem pointWeights_complexMean {Y : Type*} [Fintype Y] (y : Y) (f : Y → ℂ) :
    (pointWeights y).complexMean f = f y := by
  unfold complexMean pointWeights
  dsimp only
  rw [Finset.sum_eq_single y]
  · simp
  · intro z _ hz
    simp [hz]
  · simp

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {I : Type*} [Fintype I] (law : FiniteProbabilityWeights I)
variable (P : I → Prop) (hP : ∀ i, P i ↔ 0 < law.weight i)

noncomputable def positiveRestriction : FiniteProbabilityWeights {i // P i} where
  weight i := law.weight i.val
  nonneg i := law.nonneg i.val
  total := by
    have hsum := Fintype.sum_subtype_add_sum_subtype P law.weight
    have hz : (∑ i : {i // ¬P i}, law.weight i.val) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      exact le_antisymm (le_of_not_gt (fun h => i.property ((hP i.val).mpr h))) (law.nonneg _)
    rwa [hz, add_zero, law.total] at hsum

theorem positiveRestriction_mean (F : {i // P i} → ℝ) :
    (law.positiveRestriction P hP).mean F =
      law.mean (fun i => if h : P i then F ⟨i, h⟩ else 0) := by
  exact (Finset.sum_congr_set {i | P i}
    (fun i => law.weight i * (if h : P i then F ⟨i, h⟩ else 0))
    (fun i => law.weight i.val * F i)
    (fun i hi => by rw [dite_eq_left (show P i from hi)]; all_goals rfl)
    (fun i hi => by rw [dite_eq_right (show ¬P i from hi), mul_zero])).symm

theorem positiveRestriction_complexMean (F : {i // P i} → ℂ) :
    (law.positiveRestriction P hP).complexMean F =
      law.complexMean (fun i => if h : P i then F ⟨i, h⟩ else 0) := by
  exact (Finset.sum_congr_set {i | P i}
    (fun i => (law.weight i : ℂ) * (if h : P i then F ⟨i, h⟩ else 0))
    (fun i => (law.weight i.val : ℂ) * F i)
    (fun i hi => by rw [dite_eq_left (show P i from hi)]; all_goals rfl)
    (fun i hi => by rw [dite_eq_right (show ¬P i from hi), mul_zero])).symm

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

variable {Ω R : Type*} [Fintype Ω] (p : FiniteProbabilityWeights Ω) (F : Ω → R)

noncomputable def fiberTest (f : Ω → ℝ) (y : R) : ℝ :=
  p.fiberMean F y f / p.fiberMean F y (fun _ => 1)

theorem fiberMean_le_mul_mass (f : Ω → ℝ) (M : ℝ) (hf : ∀ z, f z ≤ M) (y : R) :
    p.fiberMean F y f ≤ M * p.fiberMean F y (fun _ => 1) := by
  classical
  unfold fiberMean
  rw [← p.mean_const_mul]
  apply p.mean_mono
  intro z
  by_cases hz : F z = y
  · simpa only [hz, ite_true, mul_one] using hf z
  · simp only [hz, ite_false, mul_zero, le_refl]

theorem fiberMean_zero_of_mass_zero (f : Ω → ℝ) (M : ℝ)
    (hf : ∀ z, 0 ≤ f z ∧ f z ≤ M) (y : R)
    (hy : p.fiberMean F y (fun _ => 1) = 0) : p.fiberMean F y f = 0 := by
  have h0 := p.fiberMean_nonneg F y f (fun z => (hf z).1)
  have h1 := p.fiberMean_le_mul_mass F f M (fun z => (hf z).2) y
  rw [hy, mul_zero] at h1
  exact le_antisymm h1 h0

theorem fiberTest_bounds (f : Ω → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ z, 0 ≤ f z ∧ f z ≤ M) (y : R) :
    0 ≤ p.fiberTest F f y ∧ p.fiberTest F f y ≤ M := by
  have hmass := p.fiberMean_nonneg F y (fun _ => 1) (fun _ => zero_le_one)
  constructor
  · exact div_nonneg (p.fiberMean_nonneg F y f (fun z => (hf z).1)) hmass
  · by_cases hy : p.fiberMean F y (fun _ => 1) = 0
    · simpa only [fiberTest, hy, div_zero] using hM
    · have hp : 0 < p.fiberMean F y (fun _ => 1) := lt_of_le_of_ne hmass (Ne.symm hy)
      exact (div_le_iff₀ hp).mpr (p.fiberMean_le_mul_mass F f M (fun z => (hf z).2) y)

theorem mass_mul_fiberTest (f : Ω → ℝ) (M : ℝ) (hf : ∀ z, 0 ≤ f z ∧ f z ≤ M) (y : R) :
    p.fiberMean F y (fun _ => 1) * p.fiberTest F f y = p.fiberMean F y f := by
  by_cases hy : p.fiberMean F y (fun _ => 1) = 0
  · rw [hy, zero_mul, p.fiberMean_zero_of_mass_zero F f M hf y hy]
  · unfold fiberTest
    field_simp

end Erdos3.FiniteProbabilityWeights

end

end OAI
