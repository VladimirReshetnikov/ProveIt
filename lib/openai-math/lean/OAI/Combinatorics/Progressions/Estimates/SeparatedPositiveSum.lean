import Mathlib

namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem separated_tsum_lipschitz {ι X : Type*} [PseudoMetricSpace X]
    (f : ι → X → ℝ) {K : ℝ≥0} (hf : ∀ i, LipschitzWith K (f i))
    (hpos : ∀ i x, 0 ≤ f i x)
    (hsep : ∀ x i j, f i x ≠ 0 → f j x ≠ 0 → i = j) :
    LipschitzWith K (fun x => ∑' i, f i x) := by
  have hsingle (x : X) (i : ι) (hi : f i x ≠ 0) : (∑' j, f j x) = f i x := by
    apply tsum_eq_single i
    intro j hji
    by_contra hj
    exact hji (hsep x j i hj hi)
  have hdom (x : X) (i : ι) : f i x ≤ ∑' j, f j x := by
    by_cases hi : f i x = 0
    · rw [hi]
      exact tsum_nonneg (fun j => hpos j x)
    · rw [hsingle x i hi]
  have hsub (x y : X) : (∑' i, f i x) - (∑' i, f i y) ≤ K * dist x y := by
    by_cases hx : ∃ i, f i x ≠ 0
    · obtain ⟨i, hi⟩ := hx
      rw [hsingle x i hi]
      have h := (le_abs_self (f i x - f i y)).trans ((hf i).dist_le_mul x y)
      linarith [hdom y i]
    · have hz : ∀ i, f i x = 0 := fun i => not_ne_iff.mp (fun hi => hx ⟨i, hi⟩)
      simp only [hz, tsum_zero, zero_sub]
      exact le_trans (neg_nonpos.mpr (tsum_nonneg (fun i => hpos i y)))
        (mul_nonneg K.coe_nonneg dist_nonneg)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq, abs_le]
  have hxy := hsub x y
  have hyx := hsub y x
  rw [dist_comm y x] at hyx
  constructor <;> linarith

end Erdos3

end

end OAI
