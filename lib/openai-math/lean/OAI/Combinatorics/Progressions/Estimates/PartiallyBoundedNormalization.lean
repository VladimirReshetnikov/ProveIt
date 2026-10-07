import OAI.Combinatorics.Progressions.Sampling.GridNormalizationDenominator

namespace OAI

section

namespace Erdos3

theorem exists_partially_bounded_grid_normalization {ι κ : Type*} {k : ℕ}
    (B : Matrix ι (Fin k) ℝ) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ j, B.col j ∈ realDenominatorGrid l)
    (e : κ → ι) (p : Fin k → κ)
    (hp : (B.submatrix (e ∘ p) id).det ≠ 0)
    (C : ℝ) (hminor : ∀ q : Fin k → κ, |(B.submatrix (e ∘ q) id).det| ≤ C) :
    ∃ D : ℕ, 0 < D ∧ D ≤ Nat.ceil (C * (l : ℝ) ^ k) ∧
      ∃ Q : Matrix ι (Fin k) ℚ,
        (∀ j, Q.col j ∈ denominatorGrid D) ∧
        Q.map (Rat.castHom ℝ) = B * (B.submatrix (e ∘ p) id)⁻¹ ∧
        Q.submatrix (e ∘ p) id = 1 ∧
        (∀ i j, RationalHeightLE (Q (e i) j) (Nat.ceil (C * (l : ℝ) ^ k))) := by
  obtain ⟨D, hD, hDle, Q, hQgrid, hQ, hQid⟩ :=
    exists_grid_row_normalization B l hl hgrid (e ∘ p) hp C (hminor p)
  let H := B.submatrix e id
  have hHgrid (j) : H.col j ∈ realDenominatorGrid l := by
    obtain ⟨z, hz⟩ := hgrid j
    refine ⟨fun i => z (e i), ?_⟩
    funext i
    exact congrFun hz (e i)
  obtain ⟨QH, hQH, hheight, _⟩ :=
    exists_bounded_rational_row_normalization H l hl hHgrid p hp C hminor
  have heq : Q.submatrix e id = QH := by
    ext i j
    apply Rat.cast_injective (α := ℝ)
    change (Q (e i) j : ℝ) = (QH i j : ℝ)
    calc
      _ = (B * (B.submatrix (e ∘ p) id)⁻¹) (e i) j :=
        congrArg (fun M : Matrix ι (Fin k) ℝ => M (e i) j) hQ
      _ = (H * (H.submatrix p id)⁻¹) i j := rfl
      _ = _ := (congrArg (fun M : Matrix κ (Fin k) ℝ => M i j) hQH).symm
  refine ⟨D, hD, hDle, Q, hQgrid, hQ, hQid, ?_⟩
  intro i j
  have h := congrArg (fun M : Matrix κ (Fin k) ℚ => M i j) heq
  change Q (e i) j = QH i j at h
  rw [h]
  exact hheight i j

end Erdos3

end

end OAI
