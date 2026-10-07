import OAI.Combinatorics.Progressions.Linear.RankQuotientHeightBudget

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem exists_squarefree_coefficient_basis (a : SquarefreeIndex (ReplicatedIndex bound))
    {p : ℝ} (hM : M.ComplexityLE p) :
    ∃ b : Basis (Fin (finrank ℚ
        (M.filtration.squarefreeCoefficientLayer (fun j : ReplicatedIndex bound => j.1) a))) ℚ
        (M.filtration.squarefreeCoefficientLayer (fun j : ReplicatedIndex bound => j.1) a),
      ∀ j k, RationalHeightLE (D.basis.repr (b j).val k) ⌈Real.exp p⌉₊ := by
  classical
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  by_cases ha : a.val = 0
  · have hU : M.filtration.squarefreeCoefficientLayer (fun j : ReplicatedIndex bound => j.1) a = ⊥ := by
      simp only [MultidegreeLieFiltration.squarefreeCoefficientLayer, ha, ite_true]
    rw [hU]
    refine ⟨Module.finBasis ℚ (⊥ : Submodule ℚ L), ?_⟩
    intro j k
    have hz : (Module.finBasis ℚ (⊥ : Submodule ℚ L) j).val = 0 :=
      (Module.finBasis ℚ (⊥ : Submodule ℚ L) j).property
    rw [hz, map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero (one_le_ceil_exp p)
  · have hU : M.filtration.squarefreeCoefficientLayer (fun j : ReplicatedIndex bound => j.1) a =
        M.filtration.layer (blockDegree (fun j : ReplicatedIndex bound => j.1) a.val) := by
      simp only [MultidegreeLieFiltration.squarefreeCoefficientLayer, ha, ite_false]
    rw [hU]
    obtain ⟨b, hb⟩ := M.exists_layer_basis _ (replicated_blockDegree_le bound a) hM
    exact ⟨b, fun j k => rationalHeightLE_ceil_exp (hb j k)⟩

noncomputable def squarefreeCoefficientBasis (p : ℝ) (a : SquarefreeIndex (ReplicatedIndex bound)) :
    Basis (Fin (finrank ℚ
      (M.filtration.squarefreeCoefficientLayer (fun j : ReplicatedIndex bound => j.1) a))) ℚ
      (M.filtration.squarefreeCoefficientLayer (fun j : ReplicatedIndex bound => j.1) a) := by
  letI : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  exact chosenBoundedSubmoduleBasis D.basis ⌈Real.exp p⌉₊ _

theorem squarefreeCoefficientBasis_height {p : ℝ} (hM : M.ComplexityLE p)
    (a : SquarefreeIndex (ReplicatedIndex bound)) (j k) :
    RationalHeightLE (D.basis.repr (M.squarefreeCoefficientBasis p a j).val k) ⌈Real.exp p⌉₊ := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  exact chosenBoundedSubmoduleBasis_height D.basis ⌈Real.exp p⌉₊ _
    (M.exists_squarefree_coefficient_basis a hM) j k

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
