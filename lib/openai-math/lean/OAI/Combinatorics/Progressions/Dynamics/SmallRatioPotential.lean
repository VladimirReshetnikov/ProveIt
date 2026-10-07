import OAI.Combinatorics.Progressions.Estimates.FiniteCellRefinement

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem small_ratio_quarter_potential_le_either {a b u v c₀ K : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hc₀ : 0 ≤ c₀) (hK : 0 ≤ K) (hau : a ≤ K * u) (hbv : b ≤ K * v)
    (hsmall : a ≤ c₀ * u ∨ b ≤ c₀ * v)
    (hfactor : (c₀ * K) ^ (1 / 4 : ℝ) ≤ 1 / 2) :
    (a * b) ^ (1 / 4 : ℝ) ≤ (u * v) ^ (1 / 4 : ℝ) / 2 := by
  rcases hsmall with hsmall | hsmall
  · exact small_ratio_quarter_potential_le ha hb hu hv hc₀ hK hsmall hbv hfactor
  · simpa only [mul_comm] using
      small_ratio_quarter_potential_le hb ha hv hu hc₀ hK hsmall hau hfactor

variable {G : Type*} [AddCommGroup G]

noncomputable def smallRatioCenterPotential (L : Finset G) (f g : G → ℝ)
    (u v c₀ : ℝ) (x y : G) : ℝ := by
  classical
  exact if cellAverage L f x < c₀ * u ∨ cellAverage L g y < c₀ * v then
    (cellAverage L f x * cellAverage L g y) ^ (1 / 4 : ℝ) else 0

theorem smallRatioCenterPotential_le (L : Finset G) (f g : G → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    {u v c₀ K : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hc₀ : 0 ≤ c₀) (hK : 0 ≤ K)
    (hcapf : ∀ x, cellAverage L f x ≤ K * u)
    (hcapg : ∀ y, cellAverage L g y ≤ K * v)
    (hfactor : (c₀ * K) ^ (1 / 4 : ℝ) ≤ 1 / 2) (x y : G) :
    smallRatioCenterPotential L f g u v c₀ x y ≤ (u * v) ^ (1 / 4 : ℝ) / 2 := by
  classical
  unfold smallRatioCenterPotential
  split_ifs with hsmall
  · apply small_ratio_quarter_potential_le_either
      (cellAverage_nonneg L f hf x) (cellAverage_nonneg L g hg y)
      hu hv hc₀ hK (hcapf x) (hcapg y) _ hfactor
    exact hsmall.imp le_of_lt le_of_lt
  · positivity

theorem expect_smallRatioCenterPotential_le (B L : Finset G) (hB : B.Nonempty)
    (f g : G → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    {u v c₀ K : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hc₀ : 0 ≤ c₀) (hK : 0 ≤ K)
    (hcapf : ∀ x, cellAverage L f x ≤ K * u)
    (hcapg : ∀ y, cellAverage L g y ≤ K * v)
    (hfactor : (c₀ * K) ^ (1 / 4 : ℝ) ≤ 1 / 2) :
    (𝔼 x ∈ B, 𝔼 y ∈ B, smallRatioCenterPotential L f g u v c₀ x y) ≤
      (u * v) ^ (1 / 4 : ℝ) / 2 := by
  calc
    _ ≤ 𝔼 _x ∈ B, 𝔼 _y ∈ B, (u * v) ^ (1 / 4 : ℝ) / 2 := by
      apply Finset.expect_le_expect
      intro x _
      apply Finset.expect_le_expect
      intro y _
      exact smallRatioCenterPotential_le L f g hf hg hu hv hc₀ hK hcapf hcapg hfactor x y
    _ = _ := by rw [Finset.expect_const hB, Finset.expect_const hB]

theorem small_ratio_matched_potential [Fintype G] [DecidableEq G]
    (L S C : Finset G) (hL : L.Nonempty) (hS : S.Nonempty) (hC : C.Nonempty)
    (f g : G → ℝ) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupport : ∀ x, x ∉ L → f x = 0) (hgsupport : ∀ x, x ∉ L → g x = 0)
    {u v c₀ K : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hc₀ : 0 ≤ c₀) (hK : 0 ≤ K)
    (hcapf : (𝔼 x ∈ L, f x) ≤ K * u) (hcapg : (𝔼 x ∈ L, g x) ≤ K * v)
    (hsmall : (𝔼 x ∈ L, f x) ≤ c₀ * u ∨ (𝔼 x ∈ L, g x) ≤ c₀ * v)
    (hfactor : (c₀ * K) ^ (1 / 4 : ℝ) ≤ 1 / 2) :
    (𝔼 z ∈ matchedCellSpace L S,
        (matchedFirstCell C f z * matchedSecondCell C g z) ^ (1 / 4 : ℝ)) ≤
      ((𝔼 x ∈ L, f x) * (𝔼 x ∈ L, g x)) ^ (1 / 4 : ℝ) ∧
    (𝔼 z ∈ matchedCellSpace L S,
        (matchedFirstCell C f z * matchedSecondCell C g z) ^ (1 / 4 : ℝ)) ≤
      (u * v) ^ (1 / 4 : ℝ) / 2 := by
  have hbase := matched_cell_potential_le L S C hL hS hC f g hf hg hfsupport hgsupport
  have hlocal := small_ratio_quarter_potential_le_either
    (Finset.expect_nonneg (fun x _ => hf x)) (Finset.expect_nonneg (fun x _ => hg x))
    hu hv hc₀ hK hcapf hcapg hsmall hfactor
  exact ⟨hbase, hbase.trans hlocal⟩

end Erdos3

end

end OAI
