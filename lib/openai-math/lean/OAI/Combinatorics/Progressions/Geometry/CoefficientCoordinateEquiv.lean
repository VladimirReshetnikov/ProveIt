import OAI.Combinatorics.Progressions.Fourier.EuclideanJetTorus

namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {K : Type*} {m : ℕ} {J : Fin m → Type*}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

theorem coefficientCoordinateTorus_injective :
    Function.Injective (coefficientCoordinateTorus (K := K) U) := by
  intro x y h
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) x
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) y
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  intro s i
  have hs := QuotientAddGroup.eq_iff_sub_mem.mp (congrFun h s)
  exact hs () i

noncomputable def coefficientCoordinateEquiv :
    CoefficientTorus (K := K) U ≃+ CoefficientCoordinateTori (K := K) U :=
  AddEquiv.ofBijective (coefficientCoordinateTorus U)
    ⟨coefficientCoordinateTorus_injective U, coefficientCoordinateTorus_surjective U⟩

theorem coefficientCoordinateEquiv_apply (x : CoefficientTorus (K := K) U) :
    coefficientCoordinateEquiv U x = coefficientCoordinateTorus U x := rfl

end Erdos3.VectorPolynomial

end

end OAI
