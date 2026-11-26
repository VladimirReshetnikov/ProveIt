import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Small verified algebraic components of the accompanying research report.
This file does not formalize the Mellin-continuation theorem, the full
mean-to-pointwise theorem, the class-group census, or a new RH statement.
-/

namespace TransferSynthesis

theorem positive_filter_bezout {R : Type*} [CommRing R] (m n z : R) :
    (m ^ 2 + m * n * z + n ^ 2 * z ^ 2) - n * z * (m + n * z) = m ^ 2 := by
  ring

theorem positive_filters_no_common_zero {R : Type*} [Field R]
    (m n z : R) (hm : m ≠ 0) (hp : m + n * z = 0) :
    m ^ 2 + m * n * z + n ^ 2 * z ^ 2 ≠ 0 := by
  intro hq
  have hzero : m ^ 2 = 0 := by
    simpa only [hp, hq, mul_zero, sub_zero] using
      (positive_filter_bezout m n z).symm
  exact (pow_ne_zero 2 hm) hzero

theorem positive_filter_reconstruction (r₀ r₁ r₂ m n : ℝ) :
    (m ^ 2 * r₀ + m * n * r₁ + n ^ 2 * r₂) -
      n * (m * r₁ + n * r₂) = m ^ 2 * r₀ := by
  ring

theorem hinge_convex (c x y θ : ℝ) (hθ : 0 ≤ θ) (hθ' : θ ≤ 1) :
    max (c - ((1 - θ) * x + θ * y)) 0 ≤
      (1 - θ) * max (c - x) 0 + θ * max (c - y) 0 := by
  have hx := le_max_left (c - x) (0 : ℝ)
  have hy := le_max_left (c - y) (0 : ℝ)
  have hx₀ := le_max_right (c - x) (0 : ℝ)
  have hy₀ := le_max_right (c - y) (0 : ℝ)
  have h₁ : 0 ≤ 1 - θ := by linarith
  apply max_le
  · nlinarith [mul_nonneg h₁ (sub_nonneg.mpr hx),
      mul_nonneg hθ (sub_nonneg.mpr hy)]
  · exact add_nonneg (mul_nonneg h₁ hx₀) (mul_nonneg hθ hy₀)

theorem weighted_hinge_convex (a c x y θ : ℝ) (ha : 0 ≤ a)
    (hθ : 0 ≤ θ) (hθ' : θ ≤ 1) :
    a * max (c - ((1 - θ) * x + θ * y)) 0 ≤
      (1 - θ) * (a * max (c - x) 0) + θ * (a * max (c - y) 0) := by
  have h := mul_le_mul_of_nonneg_left (hinge_convex c x y θ hθ hθ') ha
  nlinarith only [h]

theorem finite_positive_ramp_convex {ι : Type*} (s : Finset ι)
    (a c : ι → ℝ) (ha : ∀ i ∈ s, 0 ≤ a i)
    (x y θ : ℝ) (hθ : 0 ≤ θ) (hθ' : θ ≤ 1) :
    (∑ i ∈ s, a i * max (c i - ((1 - θ) * x + θ * y)) 0) ≤
      ∑ i ∈ s, ((1 - θ) * (a i * max (c i - x) 0) +
        θ * (a i * max (c i - y) 0)) := by
  exact Finset.sum_le_sum fun i hi ↦
    weighted_hinge_convex (a i) (c i) x y θ (ha i hi) hθ hθ'

theorem rank_loss_cancellation (d n H L U I M V R : ℝ)
    (hlower : d * (H - L) ≤ V + 2 * d * I)
    (hupper : V ≤ n * (H - M * R + U)) :
    n * M * R ≤ d * L + n * U + 2 * d * I - (d - n) * H := by
  nlinarith

#print axioms positive_filter_bezout
#print axioms positive_filters_no_common_zero
#print axioms positive_filter_reconstruction
#print axioms hinge_convex
#print axioms weighted_hinge_convex
#print axioms finite_positive_ramp_convex
#print axioms rank_loss_cancellation

end TransferSynthesis
