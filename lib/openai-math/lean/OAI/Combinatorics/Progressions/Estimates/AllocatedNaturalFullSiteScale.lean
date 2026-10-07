import OAI.Combinatorics.Progressions.Geometry.AllocatedFullSiteSupport

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*}
variable {I : Fin m → Type*} {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R : Fin m → ℝ} (hR : ∀ j, 0 < R j) (j : Fin m) (i : Fin (n j))

local notation "slots" => Finset.card (layerIntegerPrincipalSlots (G := G) B j i)
local notation "scale" => allocatedPrincipalGridScale (G := G) B U b (R := R) j i

noncomputable def allocatedNaturalFullSiteRatio : ℝ :=
  R j * allocatedPrincipalChartRatio (G := G) B U b (R := R) j i

include hR in
theorem allocatedNaturalFullSiteRatio_pos :
    0 < allocatedNaturalFullSiteRatio (G := G) B U b (R := R) j i :=
  mul_pos (hR j) (allocatedPrincipalChartRatio_pos B U b hR j i)

include hR in
theorem allocatedNaturalFullSiteRatio_le :
    allocatedNaturalFullSiteRatio (G := G) B U b (R := R) j i ≤ 8 * ((slots : ℝ) + 1) := by
  have h := mul_le_mul_of_nonneg_left (allocatedPrincipalChartRatio_le (G := G) B U b hR j i) (hR j).le
  calc
    _ ≤ R j * (8 * ((slots : ℝ) + 1) / R j) := h
    _ = _ := by field_simp [(hR j).ne']

include hR in
theorem allocatedNaturalFullSiteRatio_coordinate (z : ℝ) :
    allocatedNaturalFullSiteRatio (G := G) B U b (R := R) j i *
      (z / basisAxisScale (b j) i / R j) = z / scale := by
  rw [allocatedNaturalFullSiteRatio]
  calc
    _ = allocatedPrincipalChartRatio (G := G) B U b (R := R) j i *
        (z / basisAxisScale (b j) i) := by field_simp [(hR j).ne']
    _ = _ := allocatedPrincipalChartRatio_coordinate B U b j i z

variable [Fintype G] [∀ j, Fintype (I j)] {σ : Fin m → ℝ}
variable (S : LayerSamplerScale (G := G) B U b R σ)

include hR in
theorem allocatedNaturalFullSiteRatio_lower
    (hactive : S.value ^ (j.val + 1) < basisAxisScale (b j) i) :
    4 * ((slots : ℝ) + 1) ≤ allocatedNaturalFullSiteRatio (G := G) B U b (R := R) j i := by
  have hN := (allocatedPrincipalGridScale_bounds B U b hR S j i hactive).2
  have hNpos : (0 : ℝ) < scale := Nat.cast_pos.mpr
    (allocatedPrincipalGridScale_pos_of_radius B U b hR j i)
  have hslots : (0 : ℝ) < (slots : ℝ) + 1 := by positivity
  change 4 * ((slots : ℝ) + 1) ≤ R j * ((basisAxisScale (b j) i : ℝ) / scale)
  rw [← mul_div_assoc, le_div_iff₀ hNpos]
  unfold principalProfileSize at hN
  have hc := mul_le_mul_of_nonneg_left hN (show 0 ≤ 4 * ((slots : ℝ) + 1) by positivity)
  convert hc using 1
  field_simp
  ring

end Erdos3.VectorPolynomial

end

end OAI
