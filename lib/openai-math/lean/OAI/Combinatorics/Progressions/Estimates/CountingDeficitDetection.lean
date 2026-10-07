import OAI.Combinatorics.Progressions.Linear.CountingKernelOuter

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def countingKernelAverage {X : Type*} [Fintype X]
    (b : ℝ) (w f g : X → ℝ) : ℝ := 𝔼 x, w x * countingKernel b (f x) (g x)

theorem countingKernelAverage_one {X : Type*} [Fintype X] (w f g : X → ℝ) :
    countingKernelAverage 1 w f g = 𝔼 x, w x * f x * g x := by
  simp only [countingKernelAverage, countingKernel_one, mul_assoc]

theorem countingKernelAverage_quarter {X : Type*} [Fintype X] (w f g : X → ℝ) :
    countingKernelAverage (1 / 4) w f g =
      (3 / 8) * (𝔼 x, w x) + (3 / 8) * (𝔼 x, w x * f x) +
      (3 / 8) * (𝔼 x, w x * g x) - (1 / 8) * (𝔼 x, w x * f x * g x) := by
  have hpoint (x) : w x * countingKernel (1 / 4) (f x) (g x) =
      (3 / 8) * w x + (3 / 8) * (w x * f x) +
      (3 / 8) * (w x * g x) - (1 / 8) * (w x * f x * g x) := by
    rw [countingKernel_quarter]
    ring
  simp only [countingKernelAverage, hpoint, Finset.expect_add_distrib,
    Finset.expect_sub_distrib, ← Finset.mul_expect]

theorem quarterKernel_deficit_surplus {A00 A10 A01 A11 tau : ℝ}
    (h00 : |A00 - 1| ≤ tau / 18) (h10 : |A10 - 1| ≤ tau / 18)
    (h01 : |A01 - 1| ≤ tau / 18) (h11 : A11 < 1 - tau) :
    1 + tau / 16 < (3 / 8) * A00 + (3 / 8) * A10 + (3 / 8) * A01 - (1 / 8) * A11 := by
  obtain ⟨h00l, _⟩ := abs_le.mp h00
  obtain ⟨h10l, _⟩ := abs_le.mp h10
  obtain ⟨h01l, _⟩ := abs_le.mp h01
  linarith

theorem exists_countingKernel_surplus {X : Type*} [Fintype X] {tau : ℝ} (htau : 0 < tau)
    (w f g : X → ℝ) (h00 : |(𝔼 x, w x) - 1| ≤ tau / 18)
    (h10 : |(𝔼 x, w x * f x) - 1| ≤ tau / 18)
    (h01 : |(𝔼 x, w x * g x) - 1| ≤ tau / 18)
    (hbad : tau < |(𝔼 x, w x * f x * g x) - 1|) :
    ∃ b : ℝ, (b = 1 ∨ b = 1 / 4) ∧ 1 + tau / 16 < countingKernelAverage b w f g := by
  rcases lt_abs.mp hbad with hsurplus | hdeficit
  · refine ⟨1, Or.inl rfl, ?_⟩
    rw [countingKernelAverage_one]
    linarith
  · refine ⟨1 / 4, Or.inr rfl, ?_⟩
    rw [countingKernelAverage_quarter]
    exact quarterKernel_deficit_surplus h00 h10 h01 (by linarith)

end Erdos3

end

end OAI
