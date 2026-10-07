import OAI.Combinatorics.Progressions.Estimates.AllocatedPhysicalLongIdealCap

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} {I : Fin m → Type*} {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] (rowSets : Fin m → Finset (Finset α))

variable [Fintype G] [∀ j, Fintype (I j)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "activeAxes" => {a : gridAxes // allocatedActiveGrid B U b S a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "axisN" => allocatedGridNaturalScale B U b S
local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})

theorem allocatedGridSiteWindow_nonempty (a : gridAxes) :
    (allocatedGridSiteWindow B rowSets U b S a).Nonempty := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · refine ⟨(fun _ => 0), ?_⟩
    apply allocatedGridSiteWindow_mem
    intro t
    change |((0 : ℤ) : ℝ)| ≤ _
    rw [Int.cast_zero, abs_zero]
    exact mul_nonneg (allocatedSiteCoefficientRadius_nonneg (G := G) B rowSets ⟨j, i⟩)
      (Nat.cast_nonneg _)

theorem allocatedActiveSiteWindow_error_budget (hR : ∀ j, 0 < R j)
    {δ : ℝ} (hδ : 0 < δ) :
    (allocatedSitePointTolerance (G := G) B rowSets δ /
      allocatedActiveNaturalVolume B U b S rowSets) *
      (∏ a : gridAxes, if allocatedActiveGrid B U b S a then
        ((allocatedGridSiteWindow B rowSets U b S a).card : ℝ) else 1) ≤ δ := by
  have hn := allocatedActiveNaturalVolume_pos B U b hR S rowSets
  have ht := allocatedSitePointTolerance_spec (G := G) B rowSets hδ
  calc
    _ ≤ (allocatedSitePointTolerance (G := G) B rowSets δ /
          allocatedActiveNaturalVolume B U b S rowSets) *
        (allocatedSiteFamilyWindowVolume (G := G) B rowSets *
          allocatedActiveNaturalVolume B U b S rowSets) :=
      mul_le_mul_of_nonneg_left (allocatedActiveSiteWindow_volume B rowSets U b S hR)
        (div_nonneg ht.1.le hn.le)
    _ = allocatedSitePointTolerance (G := G) B rowSets δ *
        allocatedSiteFamilyWindowVolume (G := G) B rowSets := by field_simp
    _ ≤ δ := ht.2

end Erdos3.VectorPolynomial

end

end OAI
