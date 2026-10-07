import OAI.Combinatorics.Progressions.Geometry.RightCosetMetricMap

namespace OAI

section

namespace Erdos3

variable {G H K : Type*} [Group G] [Group H] [Group K]

theorem cosetPairMap_injective (Γ : Subgroup G) (Λ : Subgroup H) (Ω : Subgroup K)
    (φ : G →* H) (ψ : G →* K) (hφ : Γ ≤ Λ.comap φ) (hψ : Γ ≤ Ω.comap ψ)
    (hdetect : ∀ g : G, φ g ∈ Λ → ψ g ∈ Ω → g ∈ Γ) :
    Function.Injective (fun x : G ⧸ Γ => (cosetMap Γ Λ φ hφ x, cosetMap Γ Ω ψ hψ x)) := by
  intro x y h
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      apply Quotient.sound
      apply QuotientGroup.leftRel_apply.mpr
      apply hdetect
      · have he : (QuotientGroup.mk (φ x) : H ⧸ Λ) = QuotientGroup.mk (φ y) := congrArg Prod.fst h
        have hr := QuotientGroup.leftRel_apply.mp (Quotient.exact he)
        simpa only [map_mul, map_inv] using hr
      · have he : (QuotientGroup.mk (ψ x) : K ⧸ Ω) = QuotientGroup.mk (ψ y) := congrArg Prod.snd h
        have hr := QuotientGroup.leftRel_apply.mp (Quotient.exact he)
        simpa only [map_mul, map_inv] using hr

end Erdos3

end

end OAI
