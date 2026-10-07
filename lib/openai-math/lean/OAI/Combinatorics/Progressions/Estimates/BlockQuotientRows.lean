import OAI.Combinatorics.Progressions.Linear.QuotientProjectionCoordinates

namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem exists_block_quotient_rows {ι δ : Type*} [Fintype ι]
    (c : ι → δ) (Q : Matrix ι ι ℚ) (hblock : ∀ i j, c i ≠ c j → Q i j = 0)
    {H : ℕ} (hH : 1 ≤ H) (hQ : ∀ i j, RationalHeightLE (Q i j) H) :
    ∃ r : ℕ, r ≤ Fintype.card ι ∧ ∃ rows : Fin r → ι, Function.Injective rows ∧
      Function.Surjective (Q.submatrix rows id).mulVec ∧
      LinearMap.ker (Q.submatrix rows id).mulVecLin = LinearMap.ker Q.mulVecLin ∧
      ∃ S : Matrix ι (Fin r) ℚ, Q.submatrix rows id * S = 1 ∧
        (∀ i j, c i ≠ c (rows j) → S i j = 0) ∧
        ∀ i j, RationalHeightLE (S i j) (rationalKernelHeight r H) := by
  classical
  obtain ⟨r, hr, rows, hinj, hsurj, hker⟩ := exists_independent_defining_rows Q
  let D := Q.submatrix rows id
  have hD : ∀ i j, c (rows i) ≠ c j → D i j = 0 := fun i j h => hblock (rows i) j h
  obtain ⟨S, hS, hSb, hSH⟩ := exists_bounded_block_image_section (fun i => c (rows i)) c D hD hH
    (fun i j => hQ (rows i) j)
  have hDS : D * S = 1 := by
    apply Matrix.ext_iff_mulVec.mpr
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    change (D * S) *ᵥ (D *ᵥ x) = 1 *ᵥ (D *ᵥ x)
    rw [Matrix.mulVec_mulVec, hS, Matrix.one_mulVec]
  exact ⟨r, hr, rows, hinj, hsurj, hker, S, hDS, hSb, by simpa only [Fintype.card_fin] using hSH⟩

end Erdos3

end

end OAI
