/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.AllocatedPrincipalSourceScale
import OAI.Combinatorics.Progressions.Fourier.AllocatedGridSpectrumSize

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem dense_slice_product_ratio {n : ℕ} {δ S C M V : ℝ} (H : Fin n → ℝ)
    (hδ : 0 < δ) (hS : 0 < S) (hC : 0 < C) (hM : 0 ≤ M)
    (hH : ∀ j, δ * S ≤ H j)
    (hbase : M / (C * S ^ n) ≤ V) :
    M / (C * ∏ j, H j) ≤ V / δ ^ n := by
  have hp : δ ^ n * S ^ n ≤ ∏ j, H j := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow] using
      Finset.prod_le_prod₀ (s := Finset.univ) (f := fun _ : Fin n => δ * S) (g := H)
        (fun _ _ => (mul_pos hδ hS).le) (fun j _ => hH j)
  have hd : 0 < δ ^ n * (C * S ^ n) := by positivity
  have hden : δ ^ n * (C * S ^ n) ≤ C * ∏ j, H j := by
    simpa only [mul_left_comm, mul_assoc] using mul_le_mul_of_nonneg_left hp hC.le
  calc
    M / (C * ∏ j, H j) ≤ M / (δ ^ n * (C * S ^ n)) :=
      div_le_div_of_nonneg_left hM hd hden
    _ = (M / (C * S ^ n)) / δ ^ n := by ring
    _ ≤ V / δ ^ n := div_le_div_of_nonneg_right hbase (pow_pos hδ _).le

theorem dense_slice_grid_cardinality {M C S δ : ℝ} (d t : ℕ)
    (hδ : 0 < δ) (hbase : M ^ d ≤ C ^ d * S ^ t) :
    M ^ d ≤ (C ^ d / δ ^ t) * (δ * S) ^ t := by
  calc
    M ^ d ≤ C ^ d * S ^ t := hbase
    _ = _ := by rw [mul_pow]; field_simp

end Erdos3

end

end OAI
