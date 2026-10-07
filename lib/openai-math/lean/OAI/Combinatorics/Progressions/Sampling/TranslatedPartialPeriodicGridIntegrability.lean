import Mathlib.MeasureTheory.Integral.Prod
import OAI.Combinatorics.Progressions.Estimates.PartialComplexScaledQuadrature

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

variable {C J : Type*} [Fintype C] [Fintype J]

theorem partialPeriodicIntegerGrid_integrable (q : ℕ) [NeZero q]
    (f : (J → ZMod q) → ((C → ℝ) × (J → ℝ)) → ℂ)
    (hf : ∀ r, Continuous (f r))
    (T : J → ℝ) (hT : ∀ j, 0 < T j) (R : ℝ)
    (hsupport : ∀ r x, R < ‖x‖ → f r x = 0) :
    Integrable (fun c : C → ℝ =>
      (∑' k : J → ℤ, f (fun j => (k j : ZMod q))
        (c, fun j => (k j : ℝ) / T j)) / ((∏ j, T j : ℝ) : ℂ)) := by
  have hzero (c : C → ℝ) (k : J → ℤ)
      (hk : k ∉ rectangularWeightIndices 0 T R) :
      f (fun j => (k j : ZMod q)) (c, fun j => (k j : ℝ) / T j) = 0 := by
    have h := rectangularWeight_zero_off_indices
      (fun z => ‖f (fun j => (k j : ZMod q)) (c, z)‖) 0 T hT
      (fun z hz => by
        rw [hsupport _ _ (hz.trans_le (norm_snd_le (c, z))), norm_zero]) k hk
    change ‖f (fun j => (k j : ZMod q))
      (c, fun j => ((k j : ℝ) - 0) / T j)‖ = 0 at h
    simpa only [sub_zero] using norm_eq_zero.mp h
  have hsection (k : J → ℤ) : Integrable (fun c : C → ℝ =>
      f (fun j => (k j : ZMod q)) (c, fun j => (k j : ℝ) / T j)) := by
    apply compactBox_complex_integrable _
      ((hf _).comp (continuous_id.prodMk continuous_const)) R
    intro c hc
    exact hsupport _ _ (hc.trans_le (norm_fst_le (c, fun j => (k j : ℝ) / T j)))
  have heq : (fun c : C → ℝ => ∑' k : J → ℤ,
      f (fun j => (k j : ZMod q)) (c, fun j => (k j : ℝ) / T j)) =
      (fun c => ∑ k ∈ rectangularWeightIndices 0 T R,
        f (fun j => (k j : ZMod q)) (c, fun j => (k j : ℝ) / T j)) := by
    funext c
    exact tsum_eq_sum (hzero c)
  have hsum := integrable_finsetSum (rectangularWeightIndices 0 T R)
    (fun k _ => hsection k)
  rw [← heq] at hsum
  exact hsum.div_const _

theorem partialPeriodicResidueIntegral_integrable (q : ℕ) [NeZero q]
    (f : (J → ZMod q) → ((C → ℝ) × (J → ℝ)) → ℂ)
    (hf : ∀ r, Continuous (f r)) (R : ℝ)
    (hsupport : ∀ r x, R < ‖x‖ → f r x = 0) :
    Integrable (fun c : C → ℝ => 𝔼 r : J → ZMod q, ∫ z, f r (c, z)) := by
  have hfull (r : J → ZMod q) :
      Integrable (f r) ((volume : Measure (C → ℝ)).prod volume) := by
    apply (hf r).integrable_of_hasCompactSupport
    apply HasCompactSupport.of_support_subset_isCompact
      (isCompact_closedBall (0 : (C → ℝ) × (J → ℝ)) R)
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra! hn
    exact hx (hsupport r x hn)
  simp only [Finset.expect_eq_sum_div_card]
  exact (integrable_finsetSum _ (fun r _ => (hfull r).integral_prod_left)).div_const _

theorem integral_partialPeriodicGrid_sub_reference (q : ℕ) [NeZero q]
    (f : (J → ZMod q) → ((C → ℝ) × (J → ℝ)) → ℂ)
    (hf : ∀ r, Continuous (f r))
    (T : J → ℝ) (hT : ∀ j, 0 < T j) (R : ℝ)
    (hsupport : ∀ r x, R < ‖x‖ → f r x = 0) :
    (∫ c : C → ℝ,
      (∑' k : J → ℤ, f (fun j => (k j : ZMod q))
        (c, fun j => (k j : ℝ) / T j)) / ((∏ j, T j : ℝ) : ℂ) -
      𝔼 r : J → ZMod q, ∫ z, f r (c, z)) =
    (∫ c : C → ℝ,
      (∑' k : J → ℤ, f (fun j => (k j : ZMod q))
        (c, fun j => (k j : ℝ) / T j)) / ((∏ j, T j : ℝ) : ℂ)) -
      ∫ c : C → ℝ, 𝔼 r : J → ZMod q, ∫ z, f r (c, z) :=
  integral_sub (partialPeriodicIntegerGrid_integrable q f hf T hT R hsupport)
    (partialPeriodicResidueIntegral_integrable q f hf R hsupport)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical

variable {C J : Type*} [Fintype C] [Fintype J]

theorem translatedPartialPeriodicIntegerGrid_integrable (q : ℕ) [NeZero q]
    (f : (J → ZMod q) → ((C → ℝ) × (J → ℝ)) → ℂ)
    (hf : ∀ r, Continuous (f r))
    (center T : J → ℝ) (hT : ∀ j, 0 < T j) (R : ℝ)
    (hsupport : ∀ r x, R < ‖x‖ → f r x = 0) :
    Integrable (fun c : C → ℝ =>
      (∑' k : J → ℤ, f (fun j => (k j : ZMod q))
        (c, fun j => ((k j : ℝ) - center j) / T j)) / ((∏ j, T j : ℝ) : ℂ)) := by
  have hzero (c : C → ℝ) (k : J → ℤ)
      (hk : k ∉ rectangularWeightIndices center T R) :
      f (fun j => (k j : ZMod q)) (c, fun j => ((k j : ℝ) - center j) / T j) = 0 := by
    have h := rectangularWeight_zero_off_indices
      (fun z => ‖f (fun j => (k j : ZMod q)) (c, z)‖) center T hT
      (fun z hz => by
        rw [hsupport _ _ (hz.trans_le (norm_snd_le (c, z))), norm_zero]) k hk
    change ‖f (fun j => (k j : ZMod q))
      (c, fun j => ((k j : ℝ) - center j) / T j)‖ = 0 at h
    exact norm_eq_zero.mp h
  have hsection (k : J → ℤ) : Integrable (fun c : C → ℝ =>
      f (fun j => (k j : ZMod q)) (c, fun j => ((k j : ℝ) - center j) / T j)) := by
    apply compactBox_complex_integrable _
      ((hf _).comp (continuous_id.prodMk continuous_const)) R
    intro c hc
    exact hsupport _ _ (hc.trans_le (norm_fst_le (c, fun j => ((k j : ℝ) - center j) / T j)))
  have heq : (fun c : C → ℝ => ∑' k : J → ℤ,
      f (fun j => (k j : ZMod q)) (c, fun j => ((k j : ℝ) - center j) / T j)) =
      (fun c => ∑ k ∈ rectangularWeightIndices center T R,
        f (fun j => (k j : ZMod q)) (c, fun j => ((k j : ℝ) - center j) / T j)) := by
    funext c
    exact tsum_eq_sum (hzero c)
  have hsum := integrable_finsetSum (rectangularWeightIndices center T R)
    (fun k _ => hsection k)
  rw [← heq] at hsum
  exact hsum.div_const _

theorem integral_translatedPartialPeriodicGrid_sub_reference (q : ℕ) [NeZero q]
    (f : (J → ZMod q) → ((C → ℝ) × (J → ℝ)) → ℂ)
    (hf : ∀ r, Continuous (f r))
    (center T : J → ℝ) (hT : ∀ j, 0 < T j) (R : ℝ)
    (hsupport : ∀ r x, R < ‖x‖ → f r x = 0) :
    (∫ c : C → ℝ,
      (∑' k : J → ℤ, f (fun j => (k j : ZMod q))
        (c, fun j => ((k j : ℝ) - center j) / T j)) / ((∏ j, T j : ℝ) : ℂ) -
      𝔼 r : J → ZMod q, ∫ z, f r (c, z)) =
    (∫ c : C → ℝ,
      (∑' k : J → ℤ, f (fun j => (k j : ZMod q))
        (c, fun j => ((k j : ℝ) - center j) / T j)) / ((∏ j, T j : ℝ) : ℂ)) -
      ∫ c : C → ℝ, 𝔼 r : J → ZMod q, ∫ z, f r (c, z) :=
  integral_sub (translatedPartialPeriodicIntegerGrid_integrable q f hf center T hT R hsupport)
    (partialPeriodicResidueIntegral_integrable q f hf R hsupport)

end Erdos3

end

end OAI
