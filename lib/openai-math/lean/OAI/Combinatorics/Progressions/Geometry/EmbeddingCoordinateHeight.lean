import OAI.Combinatorics.Progressions.Estimates.RationalPowerHeight

namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

theorem embedding_basis_coordinate_height {ι κ L M : Type*} [Fintype ι] [Fintype κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    (b : Basis κ ℚ M) (e : Basis ι ℚ L) (φ : M →ₗ[ℚ] L) (hφ : Function.Injective φ)
    {H : ℕ} (hH : 1 ≤ H) (hB : ∀ i j, RationalHeightLE (e.repr (φ (b j)) i) H)
    (x : M) {K : ℕ} (hx : ∀ i, RationalHeightLE (e.repr (φ x) i) K) (j : κ) :
    RationalHeightLE (b.repr x j)
      ((Fintype.card ι + 1) * (rationalSolveHeight (Fintype.card κ) H * K) ^ Fintype.card ι) := by
  classical
  let B := LinearMap.toMatrix b e φ
  obtain ⟨P, hPB, hP⟩ := exists_bounded_rational_left_inverse B
    (Matrix.mulVec_injective_iff.mp (basisMatrix_injective b e φ hφ)) hH
    (by simpa only [B, LinearMap.toMatrix_apply] using hB)
  have hretract : P *ᵥ e.repr (φ x) = b.repr x := by
    rw [← LinearMap.toMatrix_mulVec_repr b e φ x, Matrix.mulVec_mulVec, hPB, Matrix.one_mulVec]
  rw [← congrFun hretract j]
  exact rationalHeightLE_sum (fun i => P j i * e.repr (φ x) i)
    (fun i => (hP j i).mul (hx i))

theorem embedding_coordinate_height_budget (n d H K : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hd : (d : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hK : (K : ℝ) ≤ Real.exp p) :
    (((n + 1) * (rationalSolveHeight d H * K) ^ n : ℕ) : ℝ) ≤
      Real.exp ((p + 2) ^ 8) := by
  have hproduct : ((rationalSolveHeight d H * K : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 6) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp ((p + 2) ^ 5) * Real.exp p :=
        mul_le_mul (rationalSolveHeight_le_budget d H hp hd hH) hK (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = Real.exp ((p + 2) ^ 5 + p) := (Real.exp_add _ _).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hpp : p ≤ (p + 2) ^ 5 := le_power_budget hp (by decide)
        calc
          _ ≤ 2 * (p + 2) ^ 5 := by linarith
          _ ≤ (p + 2) * (p + 2) ^ 5 := by gcongr; linarith
          _ = (p + 2) ^ 6 := by ring
  exact rational_sum_cost_le_exp n _ hp 6 1 hproduct (by simpa only [pow_one] using hn.trans (by linarith))

end Erdos3

end

end OAI
