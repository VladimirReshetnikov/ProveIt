import OAI.Combinatorics.Progressions.Dynamics.PeelingReplacementPotential

namespace OAI

section

namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [Fintype G] [DecidableEq G]

theorem exists_terminal_pair (B : Finset G) (Admissible : Finset G → Prop)
    {K kappa : ℝ} (hK : 0 < K) (hkappa : 0 < kappa) (f g : G → ℝ) :
    ∃ f' g' cs ds, Chain B Admissible K kappa f f' cs ∧ Chain B Admissible K kappa g g' ds ∧
      ((𝔼 x ∈ B, f' x) < kappa ∨ (𝔼 x ∈ B, g' x) < kappa ∨
        ((∀ C, Admissible C → (𝔼 x ∈ C, f' x) ≤ K * (𝔼 x ∈ B, f' x)) ∧
         (∀ C, Admissible C → (𝔼 x ∈ C, g' x) ≤ K * (𝔼 x ∈ B, g' x)))) := by
  classical
  by_cases hgsmall : (𝔼 x ∈ B, g x) < kappa
  · exact ⟨f, g, [], [], Chain.nil f, Chain.nil g, Or.inr (Or.inl hgsmall)⟩
  obtain ⟨f', cs, hF, hfstop⟩ := exists_terminal_chain B Admissible hK hkappa f
  by_cases hfsmall : (𝔼 x ∈ B, f' x) < kappa
  · exact ⟨f', g, cs, [], hF, Chain.nil g, Or.inl hfsmall⟩
  have hffree := hfstop.resolve_left hfsmall
  obtain ⟨g', ds, hG, hgstop⟩ := exists_terminal_chain B Admissible hK hkappa g
  refine ⟨f', g', cs, ds, hF, hG, Or.inr ?_⟩
  rcases hgstop with hgsmall | hgfree
  · exact Or.inl hgsmall
  · exact Or.inr ⟨hffree, hgfree⟩

theorem exists_budgeted_terminal_pair (B : Finset G) (Admissible : Finset G → Prop)
    {K kappa : ℝ} (hK : 0 < K) (hkappa : 0 < kappa) (f g : G → ℝ)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupport : ∀ x, x ∉ B → f x = 0) (hgsupport : ∀ x, x ∉ B → g x = 0) :
    ∃ f' g' cs ds, Chain B Admissible K kappa f f' cs ∧ Chain B Admissible K kappa g g' ds ∧
      cs.length + ds.length ≤ (positiveSupport f).card + (positiveSupport g).card ∧
      (∀ x, 0 ≤ f' x ∧ f' x ≤ f x) ∧ (∀ x, 0 ≤ g' x ∧ g' x ≤ g x) ∧
      (∀ x, x ∉ B → f' x = 0) ∧ (∀ x, x ∉ B → g' x = 0) ∧
      (1 / 4 : ℝ) * K ^ (3 / 4 : ℝ) *
          (potentialCost B (𝔼 x ∈ B, g x) f cs + potentialCost B (𝔼 x ∈ B, f' x) g ds) ≤
        ((𝔼 x ∈ B, f x) * (𝔼 x ∈ B, g x)) ^ (1 / 4 : ℝ) -
          ((𝔼 x ∈ B, f' x) * (𝔼 x ∈ B, g' x)) ^ (1 / 4 : ℝ) ∧
      (K * kappa) * (coefficientCost B cs + coefficientCost B ds) ≤
        ((𝔼 x ∈ B, f x) - 𝔼 x ∈ B, f' x) + ((𝔼 x ∈ B, g x) - 𝔼 x ∈ B, g' x) ∧
      ((𝔼 x ∈ B, f' x) < kappa ∨ (𝔼 x ∈ B, g' x) < kappa ∨
        ((∀ C, Admissible C → (𝔼 x ∈ C, f' x) ≤ K * (𝔼 x ∈ B, f' x)) ∧
         (∀ C, Admissible C → (𝔼 x ∈ C, g' x) ≤ K * (𝔼 x ∈ B, g' x)))) := by
  obtain ⟨f', g', cs, ds, hF, hG, hterminal⟩ := exists_terminal_pair B Admissible hK hkappa f g
  exact ⟨f', g', cs, ds, hF, hG,
    Nat.add_le_add (hF.length_le_support hK hkappa) (hG.length_le_support hK hkappa),
    hF.bounds hf, hG.bounds hg, hF.supported hf hfsupport, hG.supported hg hgsupport,
    pair_potential_budget hF hG hK hkappa hf hg hfsupport hgsupport,
    pair_coefficient_budget hF hG hK.le hfsupport hgsupport, hterminal⟩

end Erdos3.Peeling

end

section

namespace Erdos3.Peeling

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

def translatedCellFamily (Shape : Finset G → Prop) (A : Finset G) : Prop :=
  ∃ C, Shape C ∧ ∃ z : G, A = C.image (fun t => z + t)

omit [Fintype G] in
theorem cap_of_translated_terminal (B : Finset G) (Shape : Finset G → Prop)
    (f : G → ℝ) {K : ℝ}
    (hflat : ∀ A, translatedCellFamily Shape A → (𝔼 x ∈ A, f x) ≤ K * (𝔼 x ∈ B, f x)) :
    ∀ C, Shape C → ∀ z, cellAverage C f z ≤ K * (𝔼 x ∈ B, f x) := by
  intro C hC z
  have h := hflat (C.image (fun t => z + t)) ⟨C, hC, z, rfl⟩
  rw [Finset.expect_image (fun _ _ _ _ h => add_left_cancel h)] at h
  exact h

theorem exists_terminal_pair_with_cell_caps (B : Finset G) (Shape : Finset G → Prop)
    {K kappa : ℝ} (hK : 0 < K) (hkappa : 0 < kappa) (f g : G → ℝ) :
    ∃ f' g' cs ds,
      Chain B (translatedCellFamily Shape) K kappa f f' cs ∧
      Chain B (translatedCellFamily Shape) K kappa g g' ds ∧
      ((𝔼 x ∈ B, f' x) < kappa ∨ (𝔼 x ∈ B, g' x) < kappa ∨
        ((∀ C, Shape C → ∀ z, cellAverage C f' z ≤ K * (𝔼 x ∈ B, f' x)) ∧
         (∀ C, Shape C → ∀ z, cellAverage C g' z ≤ K * (𝔼 x ∈ B, g' x)))) := by
  obtain ⟨f', g', cs, ds, hF, hG, hterminal⟩ :=
    exists_terminal_pair B (translatedCellFamily Shape) hK hkappa f g
  refine ⟨f', g', cs, ds, hF, hG, ?_⟩
  rcases hterminal with hfsmall | hgsmall | ⟨hfflat, hgflat⟩
  · exact Or.inl hfsmall
  · exact Or.inr (Or.inl hgsmall)
  · exact Or.inr (Or.inr ⟨cap_of_translated_terminal B Shape f' hfflat,
      cap_of_translated_terminal B Shape g' hgflat⟩)

end Erdos3.Peeling

end

end OAI
