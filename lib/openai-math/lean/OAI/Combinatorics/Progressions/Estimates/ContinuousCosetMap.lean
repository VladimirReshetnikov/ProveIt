import OAI.Combinatorics.Progressions.Geometry.RightCosetMetricMap

namespace OAI

section

namespace Erdos3

variable {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]

theorem continuous_cosetMap (Γ : Subgroup G) (Λ : Subgroup H) (φ : G →* H)
    (hφ : Γ ≤ Λ.comap φ) (hcont : Continuous φ) : Continuous (cosetMap Γ Λ φ hφ) := by
  apply (QuotientGroup.isQuotientMap_mk Γ).continuous_iff.mpr
  exact QuotientGroup.continuous_mk.comp hcont

theorem compactSpace_quotient_of_surjective_hom (Λ : Subgroup H) (φ : G →* H)
    (hcont : Continuous φ) (hsurj : Function.Surjective φ)
    [CompactSpace (G ⧸ Λ.comap φ)] : CompactSpace (H ⧸ Λ) :=
  Function.Surjective.compactSpace (continuous_cosetMap (Λ.comap φ) Λ φ le_rfl hcont)
    (cosetMap_surjective (Λ.comap φ) Λ φ le_rfl hsurj)

end Erdos3

end

end OAI
