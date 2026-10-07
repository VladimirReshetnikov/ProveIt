import OAI.Combinatorics.Progressions.Geometry.ActualFixedSpatialRetainedPatchEndpoint

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

variable {A : Type} [Fintype A]
variable (selected : A → Σ j : Fin m, Fin (n j))
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis U b S.value a},
  4 ≤ Fintype.card (B a.val))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))

variable {d : ℕ} (e : Fin d ≃ Σ j, J j)

private theorem lipschitzWith_nnreal_mul {Y : Type*} [PseudoMetricSpace Y]
    {F : Y → ℝ} {L : ℝ≥0} (hF : LipschitzWith L F) (κ : ℝ≥0) :
    LipschitzWith (κ * L) (fun y => (κ : ℝ) * F y) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    dist ((κ : ℝ) * F x) ((κ : ℝ) * F y) = (κ : ℝ) * dist (F x) (F y) := by
      simp only [Real.dist_eq, ← mul_sub, abs_mul, abs_of_nonneg κ.coe_nonneg]
    _ ≤ (κ : ℝ) * ((L : ℝ) * dist x y) :=
      mul_le_mul_of_nonneg_left (hF.dist_le_mul x y) κ.coe_nonneg
    _ = ((κ * L : ℝ≥0) : ℝ) * dist x y := by rw [NNReal.coe_mul, mul_assoc]

variable (cutoff : ℕ) (κ : ℝ≥0)

theorem scaledRetainedRecoveredG_mem_Icc {Dcap Rcap : ℝ≥0}
    (hdensity : ∀ y, slice.density hB y ∈ Set.Icc (0 : ℝ) Dcap)
    (hcap : ∀ residue β,
      |slice.retainedRecoveredRationalFactor selected bW hb e cutoff residue β| ≤ Rcap)
    (v : X → ℝ) (residue : X → ZMod (slice.path.referenceRetainedCRTModulus cutoff))
    (β : Fin d → ℤ) (y : Fin d → ℝ) :
    slice.scaledRetainedRecoveredG selected hB o bW hb e cutoff κ v residue β y ∈
      Set.Icc (0 : ℝ) (κ * (Dcap * Rcap) : ℝ≥0) := by
  have h := slice.retainedRecoveredG_mem_Icc selected hB o bW hb e cutoff hdensity hcap
    v residue β y
  refine ⟨mul_nonneg κ.coe_nonneg h.1, ?_⟩
  exact mul_le_mul_of_nonneg_left h.2 κ.coe_nonneg

theorem scaledRetainedRecoveredG_spatial_lipschitz
    (hτ : 0 < τ) {Dlip Rcap : ℝ≥0}
    (hdensity : LipschitzWith Dlip (slice.density hB))
    (hcap : ∀ residue β,
      |slice.retainedRecoveredRationalFactor selected bW hb e cutoff residue β| ≤ Rcap)
    (residue : X → ZMod (slice.path.referenceRetainedCRTModulus cutoff))
    (β : Fin d → ℤ) (y : Fin d → ℝ) :
    LipschitzWith (κ * (Rcap * (Dlip * ⟨8 / τ, by positivity⟩)))
      (fun v => slice.scaledRetainedRecoveredG selected hB o bW hb e cutoff κ v residue β y) :=
  lipschitzWith_nnreal_mul
    (slice.retainedRecoveredG_spatial_lipschitz selected hB o bW hb e cutoff hτ
      hdensity hcap residue β y) κ

theorem scaledRetainedRecoveredG_lift_lipschitz
    (C : Fin m → ℝ≥0)
    (hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ C j * ‖z‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    {Dlip Rcap : ℝ≥0} (hdensity : LipschitzWith Dlip (slice.density hB))
    (hcap : ∀ residue β,
      |slice.retainedRecoveredRationalFactor selected bW hb e cutoff residue β| ≤ Rcap)
    (v : X → ℝ) (residue : X → ZMod (slice.path.referenceRetainedCRTModulus cutoff))
    (β : Fin d → ℤ) :
    LipschitzWith (κ * (Rcap * (Dlip * (K * ∑ j, C j * Fintype.card (J j)))))
      (slice.scaledRetainedRecoveredG selected hB o bW hb e cutoff κ v residue β) :=
  lipschitzWith_nnreal_mul
    (slice.retainedRecoveredG_lift_lipschitz selected hB o bW hb e cutoff C hC K hK
      hdensity hcap v residue β) κ

theorem scaledRetainedRecoveredG_recovered_invariant {r : ℕ}
    (M : Fin d → Fin r → ℤ)
    (hcol : ∀ j a, (standardEuclideanPoint (J j)
      (fun i => M (e.symm ⟨j,i⟩) a)).val ∈ euclideanSubspace (U j))
    (hdiv : ∀ i a, (slice.path.referenceRetainedCRTModulus cutoff : ℤ) ∣ M i a)
    (v : X → ℝ) (residue : X → ZMod (slice.path.referenceRetainedCRTModulus cutoff))
    (β : Fin d → ℤ) (k : Fin r → ℤ) :
    slice.scaledRetainedRecoveredG selected hB o bW hb e cutoff κ v residue
      (recoveredIntegerLift M β k) =
    slice.scaledRetainedRecoveredG selected hB o bW hb e cutoff κ v residue β := by
  funext y
  exact congrArg (fun t : ℝ => (κ : ℝ) * t)
    (congrFun (slice.retainedRecoveredG_recovered_invariant selected hB o bW hb e cutoff
      M hcol hdiv v residue β k) y)

end ActualFixedSpatialSlicedForecastPath
end Erdos3.VectorPolynomial

end

end OAI
