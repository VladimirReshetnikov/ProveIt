/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.Measurable
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import OAI.Combinatorics.Progressions.Probability.PMFPointMassMixture

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem normalized_complex_point_error (f g : ℂ) {N ε : ℝ} (hN : 0 < N)
    (he : ‖(N : ℂ) * f - g‖ ≤ ε) : ‖f - g / (N : ℂ)‖ ≤ ε / N := by
  have hn : (N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hN.ne'
  have hid : f - g / (N : ℂ) = ((N : ℂ) * f - g) / (N : ℂ) := by
    field_simp
  rw [hid, norm_div, Complex.norm_real, Real.norm_of_nonneg hN.le]
  exact div_le_div_of_nonneg_right he hN.le

theorem finite_window_normalized_l1_error {X : Type*} (W : Finset X) (f g : X → ℂ)
    {N C ε : ℝ} (hN : 0 < N) (hε : 0 ≤ ε) (hcard : (W.card : ℝ) ≤ C * N)
    (hzero : ∀ x ∉ W, f x = 0 ∧ g x = 0)
    (he : ∀ x, ‖(N : ℂ) * f x - g x‖ ≤ ε) :
    (∑' x, ‖f x - g x / (N : ℂ)‖) ≤ ε * C := by
  have hz (x) (hx : x ∉ W) : ‖f x - g x / (N : ℂ)‖ = 0 := by
    rw [(hzero x hx).1, (hzero x hx).2, zero_div, sub_self, norm_zero]
  rw [(hasSum_sum_of_ne_finset_zero hz).tsum_eq]
  calc
    _ ≤ ∑ _x ∈ W, ε / N := Finset.sum_le_sum (fun x _ => normalized_complex_point_error _ _ hN (he x))
    _ = (W.card : ℝ) * (ε / N) := by simp
    _ ≤ (C * N) * (ε / N) := mul_le_mul_of_nonneg_right hcard (div_nonneg hε hN.le)
    _ = ε * C := by field_simp

theorem finite_window_normalized_test_error {X : Type*} (W : Finset X) (f g test : X → ℂ)
    {N C ε : ℝ} (hN : 0 < N) (hε : 0 ≤ ε) (hcard : (W.card : ℝ) ≤ C * N)
    (hzero : ∀ x ∉ W, f x = 0 ∧ g x = 0)
    (he : ∀ x, ‖(N : ℂ) * f x - g x‖ ≤ ε) (htest : ∀ x, ‖test x‖ ≤ 1) :
    ‖∑' x, (f x - g x / (N : ℂ)) * test x‖ ≤ ε * C := by
  have hz (x) (hx : x ∉ W) : (f x - g x / (N : ℂ)) * test x = 0 := by
    rw [(hzero x hx).1, (hzero x hx).2, zero_div, sub_self, zero_mul]
  have hzn (x) (hx : x ∉ W) : ‖f x - g x / (N : ℂ)‖ = 0 := by
    rw [(hzero x hx).1, (hzero x hx).2, zero_div, sub_self, norm_zero]
  rw [(hasSum_sum_of_ne_finset_zero hz).tsum_eq]
  calc
    _ ≤ ∑ x ∈ W, ‖(f x - g x / (N : ℂ)) * test x‖ := norm_sum_le _ _
    _ ≤ ∑ x ∈ W, ‖f x - g x / (N : ℂ)‖ := Finset.sum_le_sum (fun x _ => by
      rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (htest x))
    _ = ∑' x, ‖f x - g x / (N : ℂ)‖ := (hasSum_sum_of_ne_finset_zero hzn).tsum_eq.symm
    _ ≤ ε * C := finite_window_normalized_l1_error W f g hN hε hcard hzero he

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

variable {X Y : Type*} [Countable X] [DecidableEq X] [MeasurableSpace X]
  [MeasurableSingletonClass X] [MeasurableSpace Y]

theorem finite_window_weighted_integrable (W : Finset X) (f : X → ℂ)
    (μ : Measure Y) (z : Y → X) (w : Y → ℂ)
    (hz : Measurable z) (hw : Measurable w)
    (hzero : ∀ x ∉ W, f x = 0)
    (hweight : Integrable (fun y => if z y ∈ W then ‖w y‖ else 0) μ) :
    Integrable (fun y => w y * f (z y)) μ := by
  let C : ℝ := ∑ x ∈ W, ‖f x‖
  apply (hweight.mul_const C).mono'
    (hw.mul ((measurable_of_countable f).comp hz)).aestronglyMeasurable
  apply ae_of_all
  intro y
  change ‖w y * f (z y)‖ ≤ (if z y ∈ W then ‖w y‖ else 0) * C
  by_cases hy : z y ∈ W
  · simp only [ite_eq_left hy, norm_mul]
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (fun x _ => norm_nonneg (f x)) hy) (norm_nonneg (w y))
  · simp only [ite_eq_right hy, hzero (z y) hy, mul_zero, norm_zero, zero_mul, le_refl]

theorem finite_window_weighted_integral_error (W : Finset X) (f g : X → ℂ)
    (μ : Measure Y) (z : Y → X) (w : Y → ℂ)
    (hz : Measurable z) (hw : Measurable w) {N ε : ℝ} (hN : 0 < N)
    (hzero : ∀ x ∉ W, f x = 0 ∧ g x = 0)
    (he : ∀ x, ‖(N : ℂ) * f x - g x‖ ≤ ε)
    (hweight : Integrable (fun y => if z y ∈ W then ‖w y‖ else 0) μ) :
    ‖(∫ y, w y * f (z y) ∂μ) - (∫ y, w y * g (z y) ∂μ) / (N : ℂ)‖ ≤
      (ε / N) * ∫ y, if z y ∈ W then ‖w y‖ else 0 ∂μ := by
  have hf := finite_window_weighted_integrable W f μ z w hz hw (fun x hx => (hzero x hx).1) hweight
  have hg := finite_window_weighted_integrable W g μ z w hz hw (fun x hx => (hzero x hx).2) hweight
  rw [← integral_div, ← integral_sub hf (hg.div_const (N : ℂ)), ← integral_const_mul]
  apply norm_integral_le_of_norm_le (hweight.const_mul (ε / N))
  apply ae_of_all
  intro y
  by_cases hy : z y ∈ W
  · simp only [ite_eq_left hy, mul_div_assoc, ← mul_sub, norm_mul]
    exact (mul_le_mul_of_nonneg_left
      (normalized_complex_point_error _ _ hN (he (z y))) (norm_nonneg (w y))).trans_eq
        (mul_comm _ _)
  · simp only [ite_eq_right hy, (hzero (z y) hy).1, (hzero (z y) hy).2,
      mul_zero, zero_div, sub_self, norm_zero, le_refl]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

variable {A : Type*} [Fintype A] {X : A → Type*}
variable (selected : A → Prop) [DecidablePred selected]

noncomputable def selectedProductExtension (p : ∀ a, X a → ℝ)
    (g : (∀ a : {a // selected a}, X a.val) → ℂ) (N : ℝ) (z : ∀ a, X a) : ℂ :=
  g (fun a => z a.val) / (N : ℂ) * ((∏ a : {a // ¬selected a}, p a.val (z a.val) : ℝ) : ℂ)

theorem selectedProductExtension_error (p : ∀ a, X a → ℝ)
    (hp : ∀ a z, 0 ≤ p a z)
    (W : ∀ a, Finset (X a))
    (g : (∀ a : {a // selected a}, X a.val) → ℂ)
    {N ε : ℝ} (hN : 0 < N)
    (hzero : ∀ z, (∃ a, z a ∉ W a.val) →
      (∏ a : {a // selected a}, p a.val (z a)) = 0 ∧ g z = 0)
    (he : ∀ z, ‖(N : ℂ) * ((∏ a : {a // selected a}, p a.val (z a) : ℝ) : ℂ) - g z‖ ≤ ε)
    (z : ∀ a, X a) :
    ‖((∏ a, p a (z a) : ℝ) : ℂ) - selectedProductExtension selected p g N z‖ ≤
      (ε / N) * ∏ a, if selected a then (W a : Set (X a)).indicator (fun _ => (1 : ℝ)) (z a)
        else p a (z a) := by
  have hc : 0 ≤ ∏ a : {a // ¬selected a}, p a.val (z a.val) :=
    Finset.prod_nonneg (fun a _ => hp a.val _)
  have hprod := Fintype.prod_subtype_mul_prod_subtype selected (fun a => p a (z a))
  have hweight := Fintype.prod_subtype_mul_prod_subtype selected
    (fun a => if selected a then (W a : Set (X a)).indicator (fun _ => (1 : ℝ)) (z a) else p a (z a))
  simp only [Subtype.property, ite_true] at hweight
  have hright (a : {a // ¬selected a}) :
      (if selected a.val then (W a.val : Set (X a.val)).indicator (fun _ => (1 : ℝ)) (z a.val)
        else p a.val (z a.val)) = p a.val (z a.val) := ite_eq_right a.property
  simp only [hright] at hweight
  rw [← hprod, Complex.ofReal_mul, selectedProductExtension, ← sub_mul, norm_mul,
    Complex.norm_real, Real.norm_of_nonneg hc, ← hweight]
  by_cases hz : ∀ a : {a // selected a}, z a.val ∈ W a.val
  · have hi : (∏ a : {a // selected a}, (W a.val : Set (X a.val)).indicator (fun _ => (1 : ℝ)) (z a.val)) = 1 := by
      apply Finset.prod_eq_one
      intro a _
      exact Set.indicator_of_mem (hz a) _
    rw [hi, one_mul]
    exact mul_le_mul_of_nonneg_right
      (normalized_complex_point_error _ _ hN (he (fun a => z a.val))) hc
  · obtain ⟨a, ha⟩ := not_forall.mp hz
    obtain ⟨htrue, hg⟩ := hzero (fun a : {a // selected a} => z a.val) ⟨a, ha⟩
    have hi : (∏ a : {a // selected a}, (W a.val : Set (X a.val)).indicator (fun _ => (1 : ℝ)) (z a.val)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ a) (Set.indicator_of_notMem ha _)
    rw [htrue, hg, Complex.ofReal_zero, zero_div, sub_zero, norm_zero, zero_mul, hi, zero_mul, mul_zero]

theorem selectedProductExtension_measurable [∀ a, MeasurableSpace (X a)]
    (p : ∀ a, X a → ℝ) (hp : ∀ a, Measurable (p a))
    (g : (∀ a : {a // selected a}, X a.val) → ℂ) (hg : Measurable g) (N : ℝ) :
    Measurable (selectedProductExtension selected p g N) := by
  have hr : Measurable (fun z : ∀ a, X a => fun a : {a // selected a} => z a.val) :=
    Measurable.of_eval (fun coordinate => measurable_pi_apply coordinate.val)
  have hc : Measurable (fun z : ∀ a, X a => ∏ a : {a // ¬selected a}, p a.val (z a.val)) :=
    Finset.measurable_prod _ (fun a _ => (hp a.val).comp (measurable_pi_apply a.val))
  exact ((hg.comp hr).div_const _).mul hc.complex_ofReal

theorem selectedWindow_volume_cancel {N ε V M : ℝ}
    (hN : 0 < N) (hε : 0 ≤ ε) (hM : 0 ≤ M) {C : ℝ} (hC : C ≤ V * N) :
    (ε / N) * (C * M) ≤ (ε * V) * M := by
  calc
    _ ≤ (ε / N) * ((V * N) * M) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hC hM) (div_nonneg hε hN.le)
    _ = _ := by field_simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem selectedProductExtension_windowIndicator {A : Type*} [Fintype A] {X : A → Type*}
    (selected : A → Prop) [DecidablePred selected]
    (p : ∀ a, X a → ℝ) (W : ∀ a, Finset (X a)) (N : ℝ) (z : ∀ a, X a) :
    selectedProductExtension selected p
        (fun x => if ∀ a : {a // selected a}, x a ∈ W a.val then 1 else 0) N z =
      ((∏ a, if selected a then (W a : Set (X a)).indicator (fun _ => (1 : ℝ)) (z a)
        else p a (z a) : ℝ) : ℂ) / (N : ℂ) := by
  have hweight := Fintype.prod_subtype_mul_prod_subtype selected
    (fun a => if selected a then (W a : Set (X a)).indicator (fun _ => (1 : ℝ)) (z a) else p a (z a))
  simp only [Subtype.property, ite_true] at hweight
  have hright (a : {a // ¬selected a}) :
      (if selected a.val then (W a.val : Set (X a.val)).indicator (fun _ => (1 : ℝ)) (z a.val)
        else p a.val (z a.val)) = p a.val (z a.val) := ite_eq_right a.property
  simp only [hright] at hweight
  rw [← hweight, Complex.ofReal_mul]
  unfold selectedProductExtension
  dsimp only
  by_cases hz : ∀ a : {a // selected a}, z a.val ∈ W a.val
  · have hi : (∏ a : {a // selected a}, (W a.val : Set (X a.val)).indicator (fun _ => (1 : ℝ)) (z a.val)) = 1 := by
      apply Finset.prod_eq_one
      intro a _
      exact Set.indicator_of_mem (hz a) _
    rw [ite_eq_left hz, hi, Complex.ofReal_one]
    ring
  · obtain ⟨a, ha⟩ := not_forall.mp hz
    have hi : (∏ a : {a // selected a}, (W a.val : Set (X a.val)).indicator (fun _ => (1 : ℝ)) (z a.val)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ a) (Set.indicator_of_notMem ha _)
    simp only [ite_eq_right hz, hi, Complex.ofReal_zero, zero_div, zero_mul]

end Erdos3

end

end OAI
