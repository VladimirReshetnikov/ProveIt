import OAI.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles

namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

theorem allocatedGrid_modulus_cardinality (j : Fin m) (i : Fin (n j))
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    {C : ℝ} {M : ℕ} (hC : 0 ≤ C) (hM : (M : ℝ) ≤ C * basisAxisScale (basis j) i)
    (d : ℕ) :
    (M : ℝ) ^ d ≤ C ^ d * (S.value : ℝ) ^ ((layerTailDegree m + 1) * d) := by
  change basisAxisScale (basis j) i ≤ S.value ^ (layerTailDegree m + 1) at hgrid
  have hK : (basisAxisScale (basis j) i : ℝ) ≤
      (S.value : ℝ) ^ (layerTailDegree m + 1) := by exact_mod_cast hgrid
  calc
    (M : ℝ) ^ d ≤ (C * (S.value : ℝ) ^ (layerTailDegree m + 1)) ^ d :=
      pow_le_pow_left₀ (Nat.cast_nonneg M)
        (hM.trans (mul_le_mul_of_nonneg_left hK hC)) d
    _ = C ^ d * (S.value : ℝ) ^ ((layerTailDegree m + 1) * d) := by
      rw [mul_pow, ← pow_mul]

end Erdos3.VectorPolynomial

end

end OAI
