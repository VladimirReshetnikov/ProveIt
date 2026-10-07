import OAI.Combinatorics.Progressions.Polynomial.PolynomialPatchProductBudget

namespace OAI

section

namespace Erdos3

theorem monotone_weight_layer {d h : ℕ} (w : Fin d → ℕ)
    (hmono : Monotone w) (hmin : ∀ i, h ≤ w i) :
    ∃ D ≤ d, (∀ i : Fin d, i.val < D → w i = h) ∧
      ∀ i : Fin d, D ≤ i.val → h + 1 ≤ w i := by
  classical
  let test := fun n : ℕ => d ≤ n ∨ ∃ hn : n < d, h < w ⟨n, hn⟩
  have hex : ∃ n, test n := ⟨d, Or.inl le_rfl⟩
  let D := Nat.find hex
  have hD : D ≤ d := Nat.find_le (Or.inl le_rfl : test d)
  refine ⟨D, hD, ?_, ?_⟩
  · intro i hi
    have hn := Nat.find_min hex hi
    have hle : w i ≤ h := by
      by_contra hnle
      exact hn (Or.inr ⟨i.isLt, lt_of_not_ge hnle⟩)
    exact le_antisymm hle (hmin i)
  · intro i hi
    have hs : test D := Nat.find_spec hex
    rcases hs with hs | ⟨hDd, hs⟩
    · omega
    · have hwi := hmono (show (⟨D, hDd⟩ : Fin d) ≤ i from hi)
      omega

end Erdos3

end

end OAI
