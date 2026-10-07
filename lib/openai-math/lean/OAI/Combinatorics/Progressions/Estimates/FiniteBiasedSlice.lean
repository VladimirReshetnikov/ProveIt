import OAI.Combinatorics.Progressions.Estimates.ComplexFiniteMeans

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_biased_finite_slice {A B : Type*} [Fintype A] [Fintype B] [Nonempty A]
    (F : A → B → ℂ) {δ : ℝ} (hδ : δ ≤ ‖𝔼 a, 𝔼 b, F a b‖) :
    ∃ a, δ ≤ ‖𝔼 b, F a b‖ := by
  have hmean : δ ≤ 𝔼 a, ‖𝔼 b, F a b‖ := hδ.trans (RCLike.norm_expect_le (K := ℂ))
  obtain ⟨a, _, ha⟩ := Finset.exists_le_of_le_expect Finset.univ_nonempty hmean
  exact ⟨a, ha⟩

end Erdos3

end

end OAI
