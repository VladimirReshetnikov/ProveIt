import OAI.Combinatorics.Progressions.Geometry.ActualFixedSpatialSlicedAnalyticIdentification

namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {X : Type} [Fintype X] [decX : DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp))
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv (allocatedPhysicalRootBudget B U b S (fun _ => 0)) (S.value : ℝ) physicalN τ δslice P Pbad Ppres)

omit [Fintype Tsp] in
theorem analyticKernelDetFalse (ξ : ℝ) :
    let M := fixedSpatialKernelBlock spatialEquiv (allocatedPhysicalRootBudget B U b S (fun _ => 0))
      (S.value : ℝ) (allocatedFixedPathKernelFrame B U b S τ ξ physicalN slice.path.noise) false
    let := Classical.decEq X
    M.det ≠ 0 := by
  cases Subsingleton.elim decX (Classical.decEq X)
  let := Classical.decEq X
  rw [← slice.normalizedNoise_eq_kernelFrame ξ]
  exact slice.path.detFalse

omit [Fintype Tsp] in
theorem analyticKernelDetTrue (ξ : ℝ) :
    let M := fixedSpatialKernelBlock spatialEquiv (allocatedPhysicalRootBudget B U b S (fun _ => 0))
      (S.value : ℝ) (allocatedFixedPathKernelFrame B U b S τ ξ physicalN slice.path.noise) true
    let := Classical.decEq X
    M.det ≠ 0 := by
  cases Subsingleton.elim decX (Classical.decEq X)
  let := Classical.decEq X
  rw [← slice.normalizedNoise_eq_kernelFrame ξ]
  exact slice.path.detTrue

theorem density_eq_allocatedSlicedPhysicalForecastDensity
    (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
      4 ≤ Fintype.card (B a.val)) (hδ : 0 < δslice) (ξ : ℝ) :
    slice.density hB = allocatedSlicedPhysicalForecastDensity B U b S τ ξ physicalN
      slice.path.noise slice.kernelLength slice.kernelLength_two slice.kernelStart slice.step
      slice.step_pos spatialEquiv (slice.analyticKernelDetFalse ξ) (slice.analyticKernelDetTrue ξ)
      hB slice.path.sample
      (fun j => slice.principalLength ⟨j.1.val,j.2⟩)
      (fun j => slice.principalStart ⟨j.1.val,j.2⟩) := by
  cases Subsingleton.elim decX (Classical.decEq X)
  let := Classical.decEq X
  have hl : slice.path.lower = fun a p => (slice.principalStart ⟨a.val,p⟩ : ℝ) / S.value :=
    funext (fun a => funext (slice.activeLower_eq a))
  have hw : slice.path.width = fun a p =>
      (slice.step : ℝ) * ((slice.principalLength ⟨a.val,p⟩ : ℝ) - 1) / S.value :=
    funext (fun a => funext (slice.activeWidth_eq hδ a))
  unfold density allocatedSlicedPhysicalForecastDensity
  dsimp only
  simp only [hl, hw]
  congr 1
  exact slice.normalizedNoise_eq_kernelFrame ξ

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
