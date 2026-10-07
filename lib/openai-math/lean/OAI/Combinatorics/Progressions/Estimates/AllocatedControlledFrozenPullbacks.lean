import OAI.Combinatorics.Progressions.Geometry.AllocatedRecoveredChartSlow

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial BooleanCubeKernel
open scoped TensorProduct Classical

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
variable {I Deck J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hbtag : ∀ j, Submodule.span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (otag : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Rad σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U btag Rad σ)
variable (hRad : ∀ j, 0 < Rad j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)
variable {L ι : Type} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
variable (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem FullChartControlledFactors.exists_allocated_frozen_pullbacks
    (left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (N : X → ℕ) (hN : ∀ i, 0 < N i) {budget allowance : ℝ}
    (hcontrol : FullChartControlledFactors F b ω hF J poly N left right budget)
    (hallowance :
      (((s : ℝ) + 1) * ((Fintype.card (X ⊕ (Σ j, J j)) : ℝ) + 1) ^ s *
        Real.exp budget *
        (((m + 1 : ℕ) : ℝ) * ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m) ^ s)
        ≤ allowance) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.exp budget ∧
      ∀ (c : ∀ j, U j) (origin : X → ℤ)
        (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
        (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
        (read : AllocatedActualCoefficientIndex G X I Deck n B → ℤ),
      AllocatedCenteredFramedRecoveredSampleAt B U btag hbtag otag S hRad hσ
        poly hm c origin v sample read →
      ∀ (keep : LayerSamplerVariables G I n B → Prop)
        (fixed : {i // ¬keep i} → ℤ),
      let β := allocatedFrozenIntegerFullChart B U btag otag poly hm c origin v sample keep fixed
      let pull := F.realSymbolHomogeneousPullbackHom b ω hF (fullTaggedVariableWeight J)
        (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)
        (fun i => homogeneousComponent (fullTaggedVariableWeight J i) (integerSampledRealChart β i))
        (fun i => sampledTopPhase_coordinate_homogeneous (fullTaggedVariableWeight J i) (integerSampledRealChart β i))
      (∀ l : ℕ, q ∣ l → F.SymbolRationalGrid b ω hF
        (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1) l (pull right)) ∧
      ∀ {τ ξ : ℝ}, 0 < τ → τ ≤ 1 → ξ ≤ 1 →
      v ∈ rectangularWeightIndices 0
        (narrowTrimmedSpatialWidths
          (allocatedPhysicalRootBudget B U btag S (fun _ => 0)) τ ξ N) 1 →
      (∀ j, σ j ≤ 1) →
      (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j)) →
      ∀ Cgeo : Fin m → ℝ, (∀ j, 0 ≤ Cgeo j) →
      (∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖) →
      (∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ 1) →
      F.SymbolSlowBound b ω hF
        (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)
        (fun i => ((Sum.elim (fun _ : G => S.value)
          (allocatedPrincipalSides B U btag S) i.val : ℕ) : ℝ)) allowance (pull left) := by
  have hc := hcontrol
  obtain ⟨q, hq, hqB, Echart, hchart, hbound, hgrid⟩ := hc
  refine ⟨q, hq, hqB, ?_⟩
  intro c origin v sample read hread keep fixed
  dsimp only
  constructor
  · intro l hql
    apply F.symbolRationalGrid_mono b ω hF _ hq hql
    exact F.symbolRationalGrid_integerTopPullback_of_coefficientGrid b ω hF
      (fullTaggedVariableWeight J) (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)
      (allocatedFrozenIntegerFullChart B U btag otag poly hm c origin v sample keep fixed)
      q right hgrid
  · intro τ ξ hτ hτ1 hξ hv hσ1 hpoly Cgeo hCgeo hgeo hsmall
    have hs := hread.integerFullChart_frozen_pulled_slow B U btag hbtag otag S hRad hσ
      poly hm F b ω hF left right hpoly c origin N hN hcontrol hτ hτ1 hξ
      v hv sample read hσ1 Cgeo hCgeo hgeo hsmall keep fixed
    have hs' := F.symbolSlowBound_mono b ω hF
      (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)
      (fun i : {i // keep i} => layerSamplerBox B U btag S i.val)
      (fun i => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U btag S i.val))
      hallowance _ hs
    simp_rw [allocatedParameterBox_side_eq] at hs'
    unfold allocatedFrozenIntegerFullChart
    exact hs'

end Erdos3.NilpotentLieFiltration

end

end OAI
