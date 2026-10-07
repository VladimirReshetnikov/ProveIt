import OAI.Combinatorics.Progressions.Estimates.EuclideanGraphNorm

namespace OAI

section

namespace Erdos3

theorem divided_basisFun_eq_smul {σ : Type*} [Fintype σ] [DecidableEq σ]
    (T : σ → ℝ) (i : σ) :
    (fun j => (Pi.basisFun ℝ σ i) j / T j) = (1 / T i) • Pi.basisFun ℝ σ i := by
  funext j
  by_cases hij : i = j
  · subst j
    simp
  · simp [Pi.basisFun_apply, Ne.symm hij]

theorem linearMap_divided_basis_norm_le {E σ : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [Fintype σ] [DecidableEq σ]
    (G : (σ → ℝ) →ₗ[ℝ] E) (T : σ → ℝ) (i : σ) (hTi : 0 < T i)
    (B : ℝ) (hB : ‖G (Pi.basisFun ℝ σ i)‖ ≤ B) :
    ‖G (fun j => (Pi.basisFun ℝ σ i) j / T j)‖ ≤ B / T i := by
  rw [divided_basisFun_eq_smul, map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_pos (one_div_pos.mpr hTi)]
  calc
    _ ≤ (1 / T i) * B := mul_le_mul_of_nonneg_left hB (one_div_pos.mpr hTi).le
    _ = B / T i := by ring

end Erdos3

end

end OAI
