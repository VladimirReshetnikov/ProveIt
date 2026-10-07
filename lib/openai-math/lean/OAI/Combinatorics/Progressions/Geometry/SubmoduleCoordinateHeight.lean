import Mathlib.LinearAlgebra.Matrix.ToLin
import OAI.Combinatorics.Progressions.Sampling.RationalSpanGrid

namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

theorem submodule_basis_coordinate_height {ν κ L : Type*} [Fintype ν] [Fintype κ]
    [AddCommGroup L] [Module ℚ L] (U : Submodule ℚ L)
    (b : Basis κ ℚ U) (e : Basis ν ℚ L) {H : ℕ} (hH : 1 ≤ H)
    (hB : ∀ i j, RationalHeightLE (e.repr (b j).val i) H)
    (x : U) {K : ℕ} (hx : ∀ i, RationalHeightLE (e.repr x.val i) K) (j : κ) :
    RationalHeightLE (b.repr x j)
      ((Fintype.card ν + 1) * (rationalSolveHeight (Fintype.card κ) H * K) ^ Fintype.card ν) := by
  classical
  let B := LinearMap.toMatrix b e U.subtype
  have hBmul (w : κ → ℚ) : B *ᵥ w = e.equivFun (b.equivFun.symm w).val := by
    have h := LinearMap.toMatrix_mulVec_repr b e U.subtype (b.equivFun.symm w)
    simp only [← b.equivFun_apply, LinearEquiv.apply_symm_apply, ← e.equivFun_apply] at h
    exact h
  have hBi : Function.Injective B.mulVec := by
    intro u v huv
    rw [hBmul, hBmul] at huv
    exact b.equivFun.symm.injective (Subtype.ext (e.equivFun.injective huv))
  obtain ⟨P, hPB, hP⟩ := exists_bounded_rational_left_inverse B
    (Matrix.mulVec_injective_iff.mp hBi) hH
    (by
      intro i j
      dsimp only [B]
      rw [LinearMap.toMatrix_apply]
      exact hB i j)
  have hretract : P *ᵥ e.repr x.val = b.repr x := by
    have hrepr : B *ᵥ b.repr x = e.repr x.val :=
      LinearMap.toMatrix_mulVec_repr b e U.subtype x
    rw [← hrepr, Matrix.mulVec_mulVec, hPB, Matrix.one_mulVec]
  rw [← congrFun hretract j]
  exact rationalHeightLE_sum (fun i => P j i * e.repr x.val i)
    (fun i => (hP j i).mul (hx i))

end Erdos3

end

end OAI
