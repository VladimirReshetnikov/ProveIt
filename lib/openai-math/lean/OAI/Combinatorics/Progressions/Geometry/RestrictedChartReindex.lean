import OAI.Combinatorics.Progressions.Probability.RestrictedComplexChartDensityComparison

namespace OAI

section

namespace Erdos3
open Set

theorem restrictedChartDensity_reindex {X X' Y Y' : Type*}
    (e : X ≃ X') (E : Y ≃ Y') (q : X → Y) (q' : X' → Y')
    (S : Set X) (S' : Set X') (c : ℝ) (f : X → ℝ) (f' : X' → ℝ)
    (hq : Set.InjOn q S) (hq' : Set.InjOn q' S')
    (hcomm : ∀ x, q' (e x) = E (q x)) (hS : ∀ x, e x ∈ S' ↔ x ∈ S)
    (hf : ∀ x, f' (e x) = f x) (y : Y) :
    restrictedChartDensity q' S' c f' (E y) = restrictedChartDensity q S c f y := by
  by_cases hy : y ∈ q '' S
  · obtain ⟨x, hx, rfl⟩ := hy
    rw [← hcomm, restrictedChartDensity_apply q' S' c f' hq' ((hS x).mpr hx),
      restrictedChartDensity_apply q S c f hq hx, hf]
  · rw [restrictedChartDensity_zero q S c f hy]
    apply restrictedChartDensity_zero
    rintro ⟨x', hx', he⟩
    obtain ⟨x, rfl⟩ := e.surjective x'
    apply hy
    exact ⟨x, (hS x).mp hx', E.injective ((hcomm x).symm.trans he)⟩

end Erdos3

end

end OAI
