import OAI.Combinatorics.Progressions.Sampling.AllocatedExternalLocalGoodForecastPath

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {Dmod : ℕ} {Lrank : ℕ}
variable {spatial : Fin Lrank ↪ G}
variable {kernel : ∀ j : Fin m, Fin Lrank × Fin (j.val + 1) ↪ G}
variable {block : ∀ j, ∀ a : AllocatedDegreeActiveAxis
  (allocatedShortAxis (I := I) U b S.value) j, Fin Lrank ↪ B ⟨j, a.val⟩}
variable {Tsp : Type} [Fintype Tsp]
variable {spatialEquiv : G ≃ X ⊕ (X ⊕ Tsp)} {Wsp Lsp : ℝ}
variable {physicalN : X → ℕ} {τ δslice P Pbad Ppres : ℝ}

namespace ActualFixedSpatialForecastPath

variable (path : ActualFixedSpatialForecastPath (Eout := Eout) B U b S hR hσ
  Dmod spatial kernel block spatialEquiv Wsp Lsp physicalN τ δslice P Pbad Ppres)

omit [Fintype Tsp] in
theorem physicalPolynomial_uncenter
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) :
    path.physicalPolynomial (fun j => subtractConstant (-(path.center j).val) (poly j)) = poly := by
  funext j
  change subtractConstant (path.center j).val
    (subtractConstant (-(path.center j).val) (poly j)) = poly j
  simpa only [neg_neg] using subtractConstant_neg_cancel (-(path.center j).val) (poly j)

omit [Fintype Tsp] in
theorem forall_physicalPolynomial_of_universal
    (Ptest : (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) →
      (∀ j d, coefficients (poly j) d ∈ U j) → Prop)
    (h : ∀ (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (hp : ∀ j d, coefficients (poly j) d ∈ U j),
      Ptest (path.physicalPolynomial poly) (path.physicalPolynomial_mem poly hp))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j d, coefficients (poly j) d ∈ U j) : Ptest poly hp := by
  let uncentered := fun j => subtractConstant (-(path.center j).val) (poly j)
  have hu : ∀ j d, coefficients (uncentered j) d ∈ U j :=
    fun j => coefficients_subtractConstant_mem (U j) (-path.center j) (poly j) (hp j)
  have hh := h uncentered hu
  have he : path.physicalPolynomial uncentered = poly := path.physicalPolynomial_uncenter poly
  simpa only [he] using hh

end ActualFixedSpatialForecastPath
end Erdos3.VectorPolynomial

end

end OAI
