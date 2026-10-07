import OAI.Combinatorics.Progressions.Estimates.AllocatedEnormousProfiles
import OAI.Combinatorics.Progressions.Geometry.PrincipalCoefficientPositiveSupport

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j)
variable (S : LayerSamplerScale (G := G) B U basis R σ) (j : Fin m) (i : Fin (n j))
variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)

local notation "csource" => allocatedPrincipalNormalizedSource B U basis hR S j i hactive
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

theorem allocatedPrincipalNormalizedSource_scale_bounds :
    2 * gamma * (basisAxisScale (basis j) i : ℝ) ≤
        ((csource).length : ℝ) * (S.value : ℝ) ^ (j.val + 1) ∧
      ((csource).length : ℝ) * (S.value : ℝ) ^ (j.val + 1) ≤
        4 * gamma * (basisAxisScale (basis j) i : ℝ) := by
  change 2 * gamma * (basisAxisScale (basis j) i : ℝ) ≤
      (principalIntervalLength (basisAxisScale (basis j) i) ((S.value : ℝ) ^ (j.val + 1)) gamma : ℝ) *
        (S.value : ℝ) ^ (j.val + 1) ∧ _
  exact principalIntervalLength_mul_scale_bounds
    (by exact_mod_cast basisAxisScale_pos (basis j) i)
    (pow_pos (by exact_mod_cast S.positive) _) (principalProfileSize_pos (hR j) _)
    (integerAxisPrincipal_width (Nat.zero_lt_succ _) S.positive
      (principalProfileSize_pos (hR j) _) (S.gap j i hactive))

theorem allocatedPrincipalNormalizedSource_grid_ratio {M : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (hM : (M : ℝ) ≤ C * basisAxisScale (basis j) i) :
    (M : ℝ) / (((csource).length : ℝ) * (S.value : ℝ) ^ (j.val + 1)) ≤
      C / (2 * gamma) := by
  have hgamma : 0 < gamma := principalProfileSize_pos (hR j) _
  have hlength : 0 < ((csource).length : ℝ) := Nat.cast_pos.mpr (csource).length_pos
  have hscale : 0 < (S.value : ℝ) ^ (j.val + 1) :=
    pow_pos (by exact_mod_cast S.positive) _
  apply (div_le_iff₀ (mul_pos hlength hscale)).mpr
  calc
    (M : ℝ) ≤ C * basisAxisScale (basis j) i := hM
    _ = (C / (2 * gamma)) * (2 * gamma * basisAxisScale (basis j) i) := by field_simp
    _ ≤ (C / (2 * gamma)) * (((csource).length : ℝ) * (S.value : ℝ) ^ (j.val + 1)) :=
      mul_le_mul_of_nonneg_left
        (allocatedPrincipalNormalizedSource_scale_bounds B U basis hR S j i hactive).1
        (div_nonneg hC (by positivity))

end Erdos3.VectorPolynomial

end

end OAI
