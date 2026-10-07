import OAI.Combinatorics.Progressions.Polynomial.PositivePolynomialLayerBases

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem exists_positive_coefficient_basis (a : BoxedDegreeIndex bound) {p : ℝ}
    (hM : M.ComplexityLE p) :
    ∃ b : Basis (Fin (finrank ℚ (M.filtration.positiveCoefficientLayer a))) ℚ
        (M.filtration.positiveCoefficientLayer a),
      ∀ j k, RationalHeightLE (D.basis.repr (b j).val k) ⌈Real.exp p⌉₊ := by
  classical
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  by_cases ha : boxedDegreeMonomial a = 0
  · have hU : M.filtration.positiveCoefficientLayer a = ⊥ := by
      simp only [MultidegreeLieFiltration.positiveCoefficientLayer, ha, ite_true]
    rw [hU]
    refine ⟨Module.finBasis ℚ (⊥ : Submodule ℚ L), ?_⟩
    intro j k
    have hz : (Module.finBasis ℚ (⊥ : Submodule ℚ L) j).val = 0 :=
      (Module.finBasis ℚ (⊥ : Submodule ℚ L) j).property
    rw [hz, map_zero, Finsupp.zero_apply]
    exact rationalHeightLE_zero (one_le_ceil_exp p)
  · have hU : M.filtration.positiveCoefficientLayer a = M.filtration.layer (fun i => (a i).val) := by
      simp only [MultidegreeLieFiltration.positiveCoefficientLayer, ha, ite_false]
    rw [hU]
    obtain ⟨b, hb⟩ := M.exists_layer_basis (fun i => (a i).val)
      (fun i => Nat.le_of_lt_succ (a i).isLt) hM
    exact ⟨b, fun j k => rationalHeightLE_ceil_exp (hb j k)⟩

noncomputable def positiveCoefficientBasis (p : ℝ) (a : BoxedDegreeIndex bound) :
    Basis (Fin (finrank ℚ (M.filtration.positiveCoefficientLayer a))) ℚ
      (M.filtration.positiveCoefficientLayer a) := by
  letI : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  exact chosenBoundedSubmoduleBasis D.basis ⌈Real.exp p⌉₊ _

theorem positiveCoefficientBasis_height {p : ℝ} (hM : M.ComplexityLE p)
    (a : BoxedDegreeIndex bound) (j k) :
    RationalHeightLE (D.basis.repr (M.positiveCoefficientBasis p a j).val k) ⌈Real.exp p⌉₊ := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  exact chosenBoundedSubmoduleBasis_height D.basis ⌈Real.exp p⌉₊ _
    (M.exists_positive_coefficient_basis a hM) j k

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
