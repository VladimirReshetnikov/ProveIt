import Surreal.HahnSeries.IdealMultipliers

/-!
# Transferring multiplier identities through normal forms

For `odg:def:thm:multiplier`, only individual negative monomials need
preimages. Surjectivity onto the entire Hahn field is not required.
-/

namespace Surreal.HahnSeries

open _root_.HahnSeries

noncomputable section

variable {Γ K F : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [Field K] [Field F]

/-- A normal-form image containing the negative monomials detects every forbidden coefficient. -/
theorem multiplier_pullback_iff (φ : F →+* K⟦Γ⟧)
    (hmonomial : ∀ g : Γ, g < 0 → ∃ x : F, φ x = single g 1) (f : F) :
    (∀ x : F, PurelyInfiniteSeries (φ x) → PurelyInfiniteSeries (φ (f * x))) ↔
      φ f ∈ nonpositiveSupportSubring Γ K := by
  constructor
  · intro hf a ha
    obtain ⟨x, hx⟩ := hmonomial (-a) (neg_neg_of_pos ha)
    have hp : PurelyInfiniteSeries (φ x) := hx ▸ purelyInfiniteSeries_single (-a) (neg_neg_of_pos ha) 1
    have h := hf x hp 0 le_rfl
    simpa only [map_mul, hx, coeff_mul_single, zero_sub, neg_neg, mul_one] using h
  · intro hf x hx
    rw [map_mul]
    exact (purelyInfiniteMultiplier_iff _).mpr hf _ hx

/-- Constants are recovered in an injective normal-form image containing the coefficient field. -/
theorem coefficient_pullback_iff (φ : F →+* K⟦Γ⟧) (c : K →+* F)
    (hc : ∀ a, φ (c a) = C a) (f : F) :
    (∃ a : K, f = c a) ↔ f = 0 ∨
      (f ≠ 0 ∧ φ f ∈ nonpositiveSupportSubring Γ K ∧ φ f⁻¹ ∈ nonpositiveSupportSubring Γ K) := by
  have hconst : (∃ a : K, f = c a) ↔ ∃ a : K, φ f = C a := by
    constructor
    · rintro ⟨a, rfl⟩; exact ⟨a, hc a⟩
    · rintro ⟨a, ha⟩; exact ⟨a, φ.injective (ha.trans (hc a).symm)⟩
  rw [hconst, coefficient_iff_multiplier_and_inverse, purelyInfiniteMultiplier_iff,
    purelyInfiniteMultiplier_iff, ← map_inv₀]
  simp only [ne_eq, map_eq_zero_iff φ φ.injective]

end
end Surreal.HahnSeries
