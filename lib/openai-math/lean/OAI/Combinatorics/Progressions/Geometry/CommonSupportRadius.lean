import OAI.Combinatorics.Progressions.Lattices.AffineBlockScale

namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def commonSupportRadius {D : Type*} [Fintype D] (H : D → ℝ) : ℕ :=
  ⌈∑ d, H d⌉₊

theorem commonSupportRadius_le {D : Type*} [Fintype D] (H : D → ℝ)
    (hH : ∀ d, 0 ≤ H d) (d : D) : H d ≤ (commonSupportRadius H : ℝ) := by
  classical
  exact (Finset.single_le_sum (fun i _ => hH i) (Finset.mem_univ d)).trans (Nat.le_ceil _)

theorem commonSupportRadius_upper {D : Type*} [Fintype D] (H : D → ℝ)
    (hH : ∀ d, 0 ≤ H d) : (commonSupportRadius H : ℝ) ≤ (∑ d, H d) + 1 :=
  (Nat.ceil_lt_add_one (Finset.sum_nonneg (fun d _ => hH d))).le

theorem commonSupportRadius_uniform {D : Type*} [Fintype D] (H : D → ℝ)
    {C : ℝ} (hH : ∀ d, 0 ≤ H d) (hC : ∀ d, H d ≤ C) :
    (commonSupportRadius H : ℝ) ≤ Fintype.card D * C + 1 := by
  apply (commonSupportRadius_upper H hH).trans
  have hh := Finset.sum_le_sum (fun d (_ : d ∈ (Finset.univ : Finset D)) => hC d)
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using add_le_add hh le_rfl

theorem commonSupport_fundamental_boxes {D : Type*} [Fintype D] {J : D → Type*}
    (H : D → ℝ) (K : D → ℕ) (center y : ∀ d, J d → ℤ)
    (hH : ∀ d, 0 ≤ H d) (hK : ∀ d, 0 < K d)
    (hy : ∀ d j, |(y d j : ℝ) - center d j| ≤ H d * K d) :
    ∀ d, centeredFundamentalBox (commonSupportRadius H) (K d) (center d) (y d) := by
  intro d
  exact centeredFundamentalBox_of_support (center d) (y d) (hK d) (commonSupportRadius_le H hH d) (hy d)

end Erdos3

end

end OAI
