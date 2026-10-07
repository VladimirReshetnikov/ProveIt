import OAI.Combinatorics.Progressions.Estimates.MixedBooleanSiteValues
import OAI.Combinatorics.Progressions.Fourier.EuclideanCoefficientTorus

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem arrayCoordinateTorus_integerMatrix {I S J : Type*} [Fintype I]
    (U : Submodule ℝ (J → ℝ)) (A : Matrix S I ℤ) (x : SubspaceArrayTorus I U) (s : S) :
    arrayCoordinateTorus U (integerMatrixTorusMap U A x) s =
      ∑ i, A s i • arrayCoordinateTorus U x i := by
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective (subspaceArrayIntegerLattice I U) x
  simp only [integerMatrixTorusMap_mk, arrayCoordinateTorus_mk]
  let a : S → I → ℤ := A
  let q := QuotientAddGroup.mk' (subspaceArrayIntegerLattice Unit U)
  change q (fun _ => matrixModuleAction (fun s i => (a s i : ℝ)) v s) =
    ∑ i, a s i • q (fun _ => v i)
  have he : (fun _ : Unit => matrixModuleAction (fun s i => (a s i : ℝ)) v s) =
      ∑ i, a s i • (fun _ : Unit => v i) := by
    funext u
    simp only [Finset.sum_apply, Pi.smul_apply]
    change (∑ i, (a s i : ℝ) • v i) = ∑ i, a s i • v i
    exact Finset.sum_congr rfl (fun i _ => Int.cast_smul_eq_zsmul ℝ (a s i) (v i))
  rw [he, map_sum]
  exact Finset.sum_congr rfl (fun i _ => map_zsmul q _ _)

namespace VectorPolynomial

theorem arrayCoordinateTorus_coefficientLayer {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (x : CoefficientTorus (K := K) U)
    (j : Fin m) (e : BoundedCoefficientExponent K (j.val + 1)) :
    arrayCoordinateTorus (U j) (coefficientLayerTorus U j x) e =
      coefficientCoordinateTorus U x ⟨j, e⟩ := by
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) x
  rfl

theorem coefficientBooleanJetTorusMap_layer {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {O J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (D : Matrix α K ℤ)
    (rows : ∀ j, O j → Finset α) (x : CoefficientTorus (K := K) U) (j : Fin m) :
    coefficientBooleanJetTorusMap U root D rows x j =
      integerMatrixTorusMap (U j) (boundedCoefficientJetMatrix root D (j.val + 1) (rows j))
        (coefficientLayerTorus U j x) := by
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) x
  rw [coefficientBooleanJetTorusMap_mk]
  rfl

theorem euclideanCoefficientJetMap_apply {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] {m : ℕ} {O J : Fin m → Type*}
    [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (D : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)
    (x : CoefficientTorus (K := K) U) (j : Fin m) (o : O j) :
    euclideanCoefficientJetMap U root D rows x j o =
      ∑ e, boundedCoefficientJetMatrix root D (j.val + 1) (rows j) o e •
        euclideanCoefficientEquiv U x j e := by
  change (euclideanSubspaceTorusEquiv (U j)).symm
    (arrayCoordinateTorus (U j) (coefficientBooleanJetTorusMap U root D rows x j) o) = _
  rw [coefficientBooleanJetTorusMap_layer, arrayCoordinateTorus_integerMatrix, map_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [map_zsmul, arrayCoordinateTorus_coefficientLayer]
  rfl

end VectorPolynomial
end Erdos3

end

end OAI
