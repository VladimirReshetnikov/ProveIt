import OAI.Combinatorics.Progressions.Estimates.FiniteCellRefinement

namespace OAI

section

namespace Erdos3

open scoped BigOperators Pointwise

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

theorem matched_potential_contraction
    (L S C : Finset G) (hL : L.Nonempty) (hLsymm : -L = L)
    (hS : S.Nonempty) (hC : C.Nonempty) (f g : G → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupport : ∀ x, x ∉ L → f x = 0) (hgsupport : ∀ x, x ∉ L → g x = 0)
    {u v M K c eta : ℝ} (hu : 0 < u) (hv : 0 < v) (heta : 0 ≤ eta)
    (hmeanf : (𝔼 x ∈ L, f x) ≤ u) (hmeang : (𝔼 x ∈ L, g x) ≤ v)
    (hcapg : ∀ x, g x / v ≤ M)
    (hcellf : ∀ x, cellAverage C f x / u ≤ K)
    (hcellg : ∀ x, cellAverage C g x / v ≤ K)
    (hTV : ∀ s ∈ S, ∀ t ∈ S,
      (∑ x, |realUniformMass L (x - (s + t)) - realUniformMass L x|) ≤ eta)
    (hsecond :
      (1 + c + M ^ 2 * eta ≤ 𝔼 x ∈ L, cellAverage C (fun y => f y / u) x ^ 2) ∨
      (1 + c + M ^ 2 * eta ≤ 𝔼 x ∈ L, cellAverage C (fun y => g y / v) x ^ 2)) :
    (𝔼 z ∈ matchedCellSpace L S,
      (matchedFirstCell C f z * matchedSecondCell C g z) ^ (1 / 4 : ℝ)) ≤
      (1 - c / (4 * (1 + Real.sqrt K) ^ 2)) * (u * v) ^ (1 / 4 : ℝ) := by
  apply normalized_quarter_potential_contraction_either (matchedCellSpace L S)
    (matchedCellSpace_nonempty hL hS) (matchedFirstCell C f) (matchedSecondCell C g) hu hv
    (fun z => cellAverage_nonneg C f hf z.1)
    (fun z => cellAverage_nonneg C g hg (-z.1 + z.2.1 + z.2.2))
    ((mean_matchedFirstCell_le L S C hS hC f hf hfsupport).trans hmeanf)
    ((mean_matchedSecondCell_le L S C hS hC g hg hgsupport).trans hmeang)
    (fun z => hcellf z.1) (fun z => hcellg (-z.1 + z.2.1 + z.2.2))
  rcases hsecond with hsecond | hsecond
  · left
    have heq :
        (𝔼 z ∈ matchedCellSpace L S, (matchedFirstCell C f z / u) ^ 2) =
          𝔼 x ∈ L, cellAverage C (fun y => f y / u) x ^ 2 := by
      simp only [matchedCellSpace, Finset.expect_product, matchedFirstCell,
        cellAverage_div, Finset.expect_const hS]
    rw [heq]
    linarith [mul_nonneg (sq_nonneg M) heta]
  · right
    have hnormg : ∀ x, 0 ≤ g x / v ∧ g x / v ≤ M :=
      fun x => ⟨div_nonneg (hg x) hv.le, hcapg x⟩
    have hshift := matchedSecondCell_second_moment_ge L S C hLsymm hS hC
      (fun y => g y / v) hnormg hTV
    have heq :
        (𝔼 z ∈ matchedCellSpace L S, matchedSecondCell C (fun y => g y / v) z ^ 2) =
          𝔼 z ∈ matchedCellSpace L S, (matchedSecondCell C g z / v) ^ 2 := by
      simp only [matchedSecondCell, cellAverage_div]
    rw [heq] at hshift
    linarith

end Erdos3

end

end OAI
