import OAI.Combinatorics.Progressions.Fourier.CoefficientAmbientFourier
import OAI.Combinatorics.Progressions.Sampling.AllocatedCoefficientSampler

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

noncomputable def allocatedCoefficientAmbientDensity :
    (CoefficientAmbientIndex (LayerSamplerVariables G I n B) J → UnitAddCircle) → ℝ :=
  coefficientAmbientDensity U b o (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
    (allocatedLayerIntegerInterpolation B U b S)

theorem allocatedCoefficientAmbientDensity_eq (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
    (hsmall : ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    (x : CoefficientTorus (K := LayerSamplerVariables G I n B) U) :
    allocatedCoefficientAmbientDensity B U b o S (coefficientAmbientTorus U x) =
      allocatedCoefficientDensity B U b hb o hR hσ S x := by
  exact coefficientAmbientDensity_eq U b hb o _ _ _ _
    (fun j i d => (allocatedLayerIntegerInterpolation_spec B U b S hR hσ j i d).1)
    (allocatedLayerColumns_quarter_support B U b hR hσ S o hσ1 C hC hchart hsmall) x

end Erdos3.VectorPolynomial

end

end OAI
