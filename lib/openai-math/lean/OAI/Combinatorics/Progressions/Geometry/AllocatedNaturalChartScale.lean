import OAI.Combinatorics.Progressions.Sampling.CeilGridScaleRatio
import OAI.Combinatorics.Progressions.Sampling.GridNormalizationTransport

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*}
variable {I : Fin m → Type*} {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R : Fin m → ℝ} (hR : ∀ j, 0 < R j) (j : Fin m) (i : Fin (n j))

local notation "scale" => allocatedPrincipalGridScale (G := G) B U basis (R := R) j i
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

include hR in
theorem allocatedPrincipalGridScale_pos_of_radius : 0 < scale := by
  apply Nat.ceil_pos.mpr
  exact mul_pos (principalProfileSize_pos (hR j) _)
    (Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i))

noncomputable def allocatedPrincipalChartRatio : ℝ :=
  (basisAxisScale (basis j) i : ℝ) / scale

include hR in
theorem allocatedPrincipalChartRatio_pos :
    0 < allocatedPrincipalChartRatio (G := G) B U basis (R := R) j i := by
  exact div_pos (Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i))
    (Nat.cast_pos.mpr (allocatedPrincipalGridScale_pos_of_radius B U basis hR j i))

include hR in
theorem allocatedPrincipalChartRatio_le :
    allocatedPrincipalChartRatio (G := G) B U basis (R := R) j i ≤
      8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B j i) : ℝ) + 1) / R j := by
  have hN : (0 : ℝ) < scale :=
    Nat.cast_pos.mpr (allocatedPrincipalGridScale_pos_of_radius B U basis hR j i)
  have hg : 0 < gamma := principalProfileSize_pos (hR j) _
  have hlow : gamma * (basisAxisScale (basis j) i : ℝ) ≤ scale := Nat.le_ceil _
  calc
    _ ≤ 1 / gamma := (div_le_div_iff₀ hN hg).mpr (by nlinarith)
    _ = _ := by
      unfold principalProfileSize
      field_simp

theorem allocatedPrincipalChartRatio_coordinate (z : ℝ) :
    allocatedPrincipalChartRatio (G := G) B U basis (R := R) j i *
        (z / basisAxisScale (basis j) i) = z / scale :=
  grid_rescale_coordinate (Nat.cast_ne_zero.mpr (basisAxisScale_pos (basis j) i).ne') _ _

include hR in
theorem allocatedPrincipalChartRatio_density_error (d : ℕ) (f g : ℂ) {ε : ℝ}
    (he : ‖(scale : ℂ) ^ d * f - g‖ ≤ ε) :
    ‖(basisAxisScale (basis j) i : ℂ) ^ d * f -
        (allocatedPrincipalChartRatio (G := G) B U basis (R := R) j i : ℂ) ^ d * g‖ ≤
      allocatedPrincipalChartRatio (G := G) B U basis (R := R) j i ^ d * ε := by
  exact grid_normalization_error (Nat.cast_nonneg _)
    (Nat.cast_pos.mpr (allocatedPrincipalGridScale_pos_of_radius B U basis hR j i)) d f g he

end Erdos3.VectorPolynomial

end

end OAI
