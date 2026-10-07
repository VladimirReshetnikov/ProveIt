import OAI.Combinatorics.Progressions.Dynamics.AllocatedFixedPathSlicedNativeAmbientComparison
import OAI.Combinatorics.Progressions.Sampling.ActualFixedSpatialSlicedForecastSourceLaw

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
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable (Dmod : ℕ) {Lrank : ℕ}
variable (spatial : Fin Lrank ↪ G)
variable (kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G)
variable (block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j,a.val⟩)
variable {Tsp : Type} [Fintype Tsp]
variable (spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)) (Wsp Lsp : ℝ)
variable (physicalN : X → ℕ) (τ δslice P Pbad Ppres : ℝ)

namespace ActualFixedSpatialSlicedForecastPath
variable {B U b S hR hσ Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres}
variable (slice : ActualFixedSpatialSlicedForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

local notation "Active" => {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a}

omit [Fintype Tsp] in
theorem kernelSupport (g : G) :
    integerProgressionSupport (slice.kernelStart g) (slice.step : ℤ) (slice.kernelLength g) ⊆
      Finset.Ico (0 : ℤ) (S.value : ℤ) :=
  integerProgressionSupport_subset_of_fin _ _ _ _ (slice.kernelInside g)

omit [Fintype Tsp] in
theorem activeSide (a : Active) (p : B a.val × Fin (layerSamplerDegree I n a.val)) :
    allocatedPrincipalSides B U b S ⟨a.val,p⟩ = S.value :=
  allocatedPrincipalSides_long_of_not_short B U b S a.val a.property p.1 p.2

omit [Fintype Tsp] in
theorem activeLength_two (hδ : 0 < δslice)
    (a : Active) (p : B a.val × Fin (layerSamplerDegree I n a.val)) :
    2 ≤ slice.principalLength ⟨a.val,p⟩ := by
  by_contra h
  have hlen : slice.principalLength ⟨a.val,p⟩ - 1 = 0 := by omega
  have hw := slice.path.hwidth a p
  rw [slice.width_eq a p, hlen, Nat.cast_zero, mul_zero, zero_div] at hw
  exact (not_le_of_gt hδ) hw

omit [Fintype Tsp] in
theorem activeSupport (a : Active) (p : B a.val × Fin (layerSamplerDegree I n a.val)) :
    integerProgressionSupport (slice.principalStart ⟨a.val,p⟩) (slice.step : ℤ)
      (slice.principalLength ⟨a.val,p⟩) ⊆ Finset.Ico (0 : ℤ) (S.value : ℤ) := by
  simpa only [slice.principalStep_active a p, activeSide (B := B) (U := U) (b := b) (S := S) a p] using
    slice.principalSupport ⟨a.val,p⟩

omit [Fintype Tsp] in
theorem activeLower_eq (a : Active) (p : B a.val × Fin (layerSamplerDegree I n a.val)) :
    slice.path.lower a p = (slice.principalStart ⟨a.val,p⟩ : ℝ) / S.value := by
  rw [slice.lower_eq a p, activeSide (B := B) (U := U) (b := b) (S := S) a p]

omit [Fintype Tsp] in
theorem activeWidth_eq (hδ : 0 < δslice)
    (a : Active) (p : B a.val × Fin (layerSamplerDegree I n a.val)) :
    slice.path.width a p = (slice.step : ℝ) * ((slice.principalLength ⟨a.val,p⟩ : ℝ) - 1) /
      S.value := by
  have hlen : 1 ≤ slice.principalLength ⟨a.val,p⟩ :=
    le_trans (by decide : 1 ≤ 2) (slice.activeLength_two hδ a p)
  rw [slice.width_eq a p, slice.principalStep_active a p, activeSide (B := B) (U := U) (b := b) (S := S) a p,
    Nat.cast_sub hlen, Nat.cast_one]

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

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
variable {X : Type} [Fintype X] [DecidableEq X]
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
theorem normalizedNoise_eq_kernelFrame (ξ : ℝ) :
    slice.path.normalizedNoise =
      allocatedFixedPathKernelFrame B U b S τ ξ physicalN slice.path.noise := by
  funext k
  rcases k with ⟨_ | g, x⟩ <;>
    rfl

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
