import OAI.Combinatorics.Progressions.Lattices.FixedAffineResidueDescent

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

theorem scalarAffineOrbitHom_physical_rebase {σ L : Type*}
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (g : F.PolynomialOrbit (fun _ : σ => 1))
    (u v : σ → ℤ) {M N : ℕ} (hM : 0 < M) (hMN : M ∣ N)
    (hv : ∀ i, v i ≡ u i [ZMOD (M : ℤ)]) :
    F.scalarAffineOrbitHom (N : ℚ) (fun i => (v i : ℚ))
      (F.scalarAffineOrbitHom (1 / (M : ℚ)) (fun i => -(u i : ℚ) / M) g) =
      F.scalarAffineOrbitHom (N / M : ℕ) (fun i => (commonStrideIndex u M v i : ℚ)) g := by
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  rw [scalarAffineOrbitHom_comp]
  have hscale : (1 / (M : ℚ)) * N = (N / M : ℕ) := by
    calc
      (1 / (M : ℚ)) * N = (N : ℚ) / M := by ring
      _ = (N / M : ℕ) := (div_eq_iff hMq).mpr (by
        exact_mod_cast (show N / M * M = N by rw [mul_comm]; exact Nat.mul_div_cancel' hMN).symm)
  have hshift : (fun i => (1 / (M : ℚ)) * (v i : ℚ) + -(u i : ℚ) / M) =
      (fun i => (commonStrideIndex u M v i : ℚ)) := by
    funext i
    have hi := residue_refinement_offset_identity u v M hv i
    calc
      (1 / (M : ℚ)) * (v i : ℚ) + -(u i : ℚ) / M = ((v i : ℚ) - (u i : ℚ)) / M := by ring
      _ = (commonStrideIndex u M v i : ℚ) := (div_eq_iff hMq).mpr (by nlinarith)
  rw [hscale, hshift]

end Erdos3.NilpotentLieFiltration

end

end OAI
