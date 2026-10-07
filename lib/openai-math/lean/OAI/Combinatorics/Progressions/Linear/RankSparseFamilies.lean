import OAI.Combinatorics.Progressions.Estimates.AnchoredSparseFamilies
import OAI.Combinatorics.Progressions.Linear.RankIntervalFactorization

namespace OAI

section

namespace Erdos3

theorem exists_rank_sparse_family
    {ι κ σ : Type*} [Fintype ι] [Fintype κ] {N : ℕ}
    (S : Finset (ZMod N)) (h₀ : ZMod N) (hh₀ : h₀ ∈ S)
    (J : Submodule ℚ (Fin 4 → ι → ℚ)) (v : κ → Fin 4 → ι → ℚ)
    (hv : Submodule.span ℚ (Set.range v) = J)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l) (hvH : ∀ a k i, RationalHeightLE (v a k i) H)
    {p : ℝ} (hp : 0 ≤ p) (hfour : (Fintype.card (Σ _ : Fin 4, ι) : ℝ) ≤ p)
    (hcols : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (2 * (p + ((p + 2) ^ 3 + (p + 2) ^ 36))) ∧
      l ∣ m ∧ ∀ (α : σ →₀ ℕ), α ≠ 0 → ∀ (β : ZMod N → ι → ℝ) (a b c d : ZMod N) (M : ℝ),
        2 * M ≤ Real.exp p →
        (∀ h ∈ S, ∃ E Q : (Σ _ : Fin 4, ι) → ℝ,
          ‖E‖ ≤ M / monomialScale T α ∧ Q ∈ realDenominatorGrid l ∧
          rankCoordinateTuple β (b - h, b, a) - E - Q ∈ realFourCoordinateSpan J) →
        (∀ h ∈ S, ∃ E Q : (Σ _ : Fin 4, ι) → ℝ,
          ‖E‖ ≤ M / monomialScale T α ∧ Q ∈ realDenominatorGrid l ∧
          rankCoordinateTuple β (c - d, h + (c - d), c) - E - Q ∈ realFourCoordinateSpan J) →
        ∀ h ∈ S, ∃ e₁₂ q₁₂ e₁₃ q₁₃ : ι → ℝ,
          ‖e₁₂‖ ≤ (Real.exp p + Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18 + p)) / monomialScale T α ∧
          ‖e₁₃‖ ≤ (Real.exp p + Real.exp ((p + 2) ^ 3 + (p + 2) ^ 18 + p)) / monomialScale T α ∧
          q₁₂ ∈ realDenominatorGrid m ∧ q₁₃ ∈ realDenominatorGrid m ∧
          β h - β h₀ - e₁₂ - q₁₂ ∈ realRationalCoordinateSpan (fourSparseFirstProjection J {1, 2}) ∧
          β h - β h₀ - e₁₃ - q₁₃ ∈ realRationalCoordinateSpan (fourSparseFirstProjection J {1, 3}) := by
  have hselected (K : Finset (Fin 4)) : (Fintype.card (Σ _ : K, ι) : ℝ) ≤ p :=
    (Nat.cast_le.mpr (card_selected_four_le K)).trans hfour
  obtain ⟨m₁₂, hm₁₂, hmp₁₂, hlm₁₂, hsolve₁₂⟩ :=
    exists_anchored_sparse_family (η := S) J {1, 2} v hv hH hl hvH hp hfour
      (hselected _) hcols hHp hlp T hT
  obtain ⟨m₁₃, hm₁₃, hmp₁₃, _, hsolve₁₃⟩ :=
    exists_anchored_sparse_family (η := S) J {1, 3} v hv hH hl hvH hp hfour
      (hselected _) hcols hHp hlp T hT
  refine ⟨m₁₂ * m₁₃, Nat.mul_pos hm₁₂ hm₁₃, ?_,
    hlm₁₂.trans (dvd_mul_right m₁₂ m₁₃), ?_⟩
  · rw [Nat.cast_mul]
    calc
      (m₁₂ : ℝ) * m₁₃ ≤ Real.exp (p + ((p + 2) ^ 3 + (p + 2) ^ 36)) *
          Real.exp (p + ((p + 2) ^ 3 + (p + 2) ^ 36)) :=
        mul_le_mul hmp₁₂ hmp₁₃ (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  · intro α hα β a b c d M hM hcorrect₁₂ hcorrect₁₃ h hh
    obtain ⟨e₁₂, q₁₂, he₁₂, hq₁₂, hrem₁₂⟩ := hsolve₁₂ α hα
      (fun h : S => rankCoordinateTuple β (b - h, b, a)) (fun h : S => β h)
      ⟨h₀, hh₀⟩ M hM (fun h i => rankCoordinateTuple_first12 β a b h i)
      (fun h j => rankCoordinateTuple_fixed12 β a b h h₀ j)
      (fun h => hcorrect₁₂ h h.property) ⟨h, hh⟩
    obtain ⟨e₁₃, q₁₃, he₁₃, hq₁₃, hrem₁₃⟩ := hsolve₁₃ α hα
      (fun h : S => rankCoordinateTuple β (c - d, h + (c - d), c)) (fun h : S => β h)
      ⟨h₀, hh₀⟩ M hM (fun h i => rankCoordinateTuple_first13 β c d h i)
      (fun h j => rankCoordinateTuple_fixed13 β c d h h₀ j)
      (fun h => hcorrect₁₃ h h.property) ⟨h, hh⟩
    exact ⟨e₁₂, q₁₂, e₁₃, q₁₃, he₁₂, he₁₃,
      realDenominatorGrid_subset_of_dvd hm₁₂ (dvd_mul_right m₁₂ m₁₃) hq₁₂,
      realDenominatorGrid_subset_of_dvd hm₁₃ (dvd_mul_left m₁₃ m₁₂) hq₁₃, hrem₁₂, hrem₁₃⟩

end Erdos3

end

end OAI
