import OAI.Combinatorics.Progressions.Geometry.ActualFixedSpatialSlicedTargetReal

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

local instance slicedReferenceModulusNeZero : NeZero slice.path.referenceModulus :=
  ⟨slice.path.referenceModulus_pos.ne'⟩

noncomputable def stepInputLaw : FiniteProbabilityWeights
    (LayerSamplerLongVariables (allocatedShortAxis (I := I) U b S.value) G B →
      ZMod slice.path.referenceModulus) := by
  letI := slice.path.primeNeZero
  exact crtPolynomialInputLaw (fun p : slice.path.primes => p.val)
    (fun p : slice.path.primes => slice.path.exponent p.val)
    (fun p : slice.path.primes => padicValNat p.val slice.step)
    (primePower_crt_coprime (fun p : slice.path.primes => p.val)
      (fun p : slice.path.primes => slice.path.exponent p.val)
      (fun p => slice.path.prime p.val p.property) Subtype.val_injective)
    (fun p v => ((Sum.elim slice.kernelStart
      (fun a => slice.principalStart ⟨a.1.val,a.2⟩) v : ℤ) :
        ZMod (p.val ^ slice.path.exponent p.val)))

omit [Fintype Tsp] in
theorem referenceInputLaw_eq_step : slice.path.referenceInputLaw = slice.stepInputLaw := by
  have hp : (fun p : slice.path.primes => slice.path.prescribed p.val) =
      (fun p : slice.path.primes => padicValNat p.val slice.step) :=
    funext fun p => slice.prescribed_eq p.val
  have ho : slice.path.origin = (fun (p : slice.path.primes)
      (v : LayerSamplerLongVariables (allocatedShortAxis (I := I) U b S.value) G B) => ((Sum.elim slice.kernelStart
      (fun a => slice.principalStart ⟨a.1.val,a.2⟩) v : ℤ) :
        ZMod (p.val ^ slice.path.exponent p.val))) :=
    funext fun p => funext fun v => slice.origin_eq p v
  simp only [ActualFixedSpatialForecastPath.referenceInputLaw, stepInputLaw, hp, ho]
  congr 1

omit [Fintype Tsp] in
theorem referencePolynomial_eq_sample : slice.path.referencePolynomial =
    allocatedForecastPolynomial (allocatedShortAxis (I := I) U b S.value)
      slice.path.base slice.path.noise (allocatedReadDeck slice.path.read)
      (allocatedOriginalSampleCongruenceProjection B U b S slice.path.sample) := by
  have h := allocatedRecoveredForecastPolynomial_eq B U b S slice.path.base slice.path.noise
    slice.path.read slice.path.readNoise slice.path.sample slice.path.readProjection
  rw [slice.path.readNoise] at h
  exact h.symm

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
