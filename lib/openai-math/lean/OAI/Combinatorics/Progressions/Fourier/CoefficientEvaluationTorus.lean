import OAI.Combinatorics.Progressions.Estimates.CoefficientRowEvaluation

namespace OAI

section

namespace Erdos3.VectorPolynomial

noncomputable def constantCoefficientTorusMap {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) :
    CoefficientTorus (K := Empty) U →+ CoefficientTorus (K := K) U :=
  QuotientAddGroup.map (coefficientIntegerLattice U) (coefficientIntegerLattice U)
    (constantCoefficientArray U).toAddMonoidHom
    (constantCoefficientArray_preserves_lattice U)

noncomputable def coefficientEvaluationTorus {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ) :
    CoefficientTorus (K := K) U →+ CoefficientTorus (K := Empty) U :=
  QuotientAddGroup.map (coefficientIntegerLattice U) (coefficientIntegerLattice U)
    (coefficientEvaluationArray U t).toAddMonoidHom
    (coefficientEvaluationArray_preserves_lattice U t)

theorem constantCoefficientTorusMap_mk {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (x : CoefficientArray (K := Empty) U) :
    constantCoefficientTorusMap (K := K) U (QuotientAddGroup.mk' (coefficientIntegerLattice U) x) =
      QuotientAddGroup.mk' (coefficientIntegerLattice U) (constantCoefficientArray U x) := rfl

theorem coefficientEvaluationTorus_mk {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ) (x : CoefficientArray (K := K) U) :
    coefficientEvaluationTorus U t (QuotientAddGroup.mk' (coefficientIntegerLattice U) x) =
      QuotientAddGroup.mk' (coefficientIntegerLattice U) (coefficientEvaluationArray U t x) := rfl

theorem coefficientEvaluationTorus_constant {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ)
    (y : CoefficientTorus (K := Empty) U) :
    coefficientEvaluationTorus U t (constantCoefficientTorusMap U y) = y := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) y
  rw [constantCoefficientTorusMap_mk, coefficientEvaluationTorus_mk,
    coefficientEvaluationArray_constant]

theorem constantCoefficientTorusMap_continuous {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ)) :
    Continuous (constantCoefficientTorusMap (K := K) U) := by
  apply (QuotientAddGroup.isQuotientMap_mk (coefficientIntegerLattice U)).continuous_iff.mpr
  exact QuotientAddGroup.continuous_mk.comp (constantCoefficientArray U).continuous_of_finiteDimensional

theorem coefficientEvaluationTorus_continuous {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ)) (t : K → ℤ) :
    Continuous (coefficientEvaluationTorus U t) := by
  apply (QuotientAddGroup.isQuotientMap_mk (coefficientIntegerLattice U)).continuous_iff.mpr
  exact QuotientAddGroup.continuous_mk.comp (coefficientEvaluationArray U t).continuous_of_finiteDimensional

theorem constantCoefficientTorusMap_nonconstant {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (y : CoefficientTorus (K := Empty) U)
    (s : CoefficientSlot K m) (hs : s.2.val ≠ 0) :
    coefficientCoordinateTorus U (constantCoefficientTorusMap U y) s = 0 := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) y
  rw [constantCoefficientTorusMap_mk, coefficientCoordinateTorus_mk]
  have hzero : (fun _ : Unit => constantCoefficientArray (K := K) U x s) = 0 := by
    funext u
    simp [constantCoefficientArray, hs]
  rw [hzero, map_zero]

end Erdos3.VectorPolynomial

end

end OAI
