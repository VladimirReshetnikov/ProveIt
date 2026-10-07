/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Lattices.CubeResidueSupport

namespace OAI

section

namespace Erdos3

open scoped BigOperators

def scalarCubeGrid {I J : Type*} {N L : ℕ} (e : J × Option I ≃ Fin N)
    (x : J → IntegerScalarCubeBox I L) : Fin N → ℤ :=
  fun i => (x (e.symm i).1 (e.symm i).2 : ℤ)

theorem scalarCubeGrid_injective {I J : Type*} {N L : ℕ} (e : J × Option I ≃ Fin N) :
    Function.Injective (scalarCubeGrid (L := L) e) := by
  intro x y h
  funext j i
  apply Subtype.ext
  have hi := congrFun h (e (j, i))
  simpa only [scalarCubeGrid, e.symm_apply_apply] using hi

theorem scalarCubeGrid_bounds {I J : Type*} {N L : ℕ} (e : J × Option I ≃ Fin N)
    (x : J → IntegerScalarCubeBox I L) (i : Fin N) :
    -(L : ℤ) ≤ scalarCubeGrid e x i ∧ scalarCubeGrid e x i < L :=
  Finset.mem_Ico.mp (x (e.symm i).1 (e.symm i).2).property

theorem scalarCubeGrid_weight_le {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] {N : ℕ}
    (e : J × Option I ≃ Fin N) (L : ℕ) (hL : 0 < L) (hsize : Fintype.card I + 1 ≤ L)
    (x : J → IntegerScalarCubeBox I L) :
    (FiniteProbabilityWeights.pi (fun _ : J => integerScalarCubeWeights I L hL)).weight x ≤
      (integerScalarCubeDensityCap I) ^ Fintype.card J * ((L : ℝ) ^ N)⁻¹ := by
  have hN : (Fintype.card I + 1) * Fintype.card J = N := by
    simpa only [Fintype.card_prod, Fintype.card_option, Fintype.card_fin, Nat.mul_comm] using
      Fintype.card_congr e
  have hs (j : J) : (integerScalarCubeWeights I L hL).weight (x j) ≤
      integerScalarCubeDensityCap I * ((L : ℝ) ^ (Fintype.card I + 1))⁻¹ := by
    have h := integerScalarCubeWeights_weight_le I L hL hsize (x j)
    rw [integerScalarCubeBox_card] at h
    push_cast at h
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ (integerScalarCubeDensityCap_pos I).le
    apply inv_anti₀ (by positivity)
    apply pow_le_pow_left₀ (Nat.cast_nonneg L)
    nlinarith [show (0 : ℝ) ≤ L from Nat.cast_nonneg L]
  change (∏ j, (integerScalarCubeWeights I L hL).weight (x j)) ≤ _
  calc
    _ ≤ ∏ _j : J, integerScalarCubeDensityCap I * ((L : ℝ) ^ (Fintype.card I + 1))⁻¹ :=
      Finset.prod_le_prod₀ (fun j _ => (integerScalarCubeWeights I L hL).nonneg (x j))
        (fun j _ => hs j)
    _ = _ := by
      simp only [Finset.prod_const, Finset.card_univ, mul_pow, ← inv_pow, ← pow_mul, hN]

end Erdos3

end

end OAI
