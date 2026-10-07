import OAI.Combinatorics.Progressions.Estimates.AllocatedCandidateZeroRestrictedNativeCommonTerminal
import OAI.Combinatorics.Progressions.Lattices.AllocatedCertifiedAffinePhysicalSlowBound

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration
open scoped BigOperators Classical TensorProduct

attribute [local irreducible] integerProgressionSupport

noncomputable def certifiedAffineLongSideBound (p : ℝ) : ℝ :=
  Real.exp ((p + 2) ^ 9) ^ 2 * Real.exp p

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)

structure CertifiedThresholdAffineRefinement
    (K : Set ((X ⊕ (Σ j, J j)) → ℝ)) (p separation : ℝ) where
  freezing : P.AxisFreezing (P.realThresholdKeep separation) (candidateSideCutoffCost separation)
  affine : freezing.problem.CertifiedAffineRefinement K p

namespace CertifiedThresholdAffineRefinement

variable {P} {K : Set ((X ⊕ (Σ j, J j)) → ℝ)} {p separation : ℝ}
    (selected : P.CertifiedThresholdAffineRefinement K p separation)

noncomputable abbrev problem := selected.affine.refinement.problem

theorem long (z : selected.problem.productive) (i : LayerSamplerVariables G I n B)
    (hi : (selected.problem.chart z).keep i) :
    separation < layerSamplerBox B U b S i :=
  selected.freezing.realThreshold_strict_long
    ⟨z.val, selected.affine.refinement.subset z.property⟩ i hi

noncomputable def conclusion {outputCost outputMass outputScore : ℝ}
    (out : selected.problem.Conclusion outputCost outputMass outputScore) :
    P.Conclusion (max outputCost (candidateSideCutoffCost separation)) outputMass outputScore :=
  selected.freezing.conclusion (selected.affine.refinement.conclusion out)

end CertifiedThresholdAffineRefinement

theorem exists_certifiedThresholdAffineRefinement
    (hσone : ∀ j, σ j ≤ 1)
    (K : Set ((X ⊕ (Σ j, J j)) → ℝ)) {p : ℝ} {blocks : ℕ}
    (hcertificate : RationalTaggedConstraintCertificate J Set.univ K p blocks)
    (hretained : ∀ t, (∀ j, (fun i => t (Sum.inr ⟨j, i⟩)) ∈ U j) → t ∈ K)
    (hp : 0 ≤ p) (hdim : (Fintype.card (Σ j, J j) : ℝ) ≤ p)
    (hblocks : (blocks : ℝ) ≤ p)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hcap : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ Real.exp p)
    (separation : ℝ) (hseparation : certifiedAffineLongSideBound p ≤ separation)
    (hmass : 0 < massThreshold) :
    Nonempty (P.CertifiedThresholdAffineRefinement K p separation) := by
  obtain ⟨freezing, hlong, _⟩ := P.exists_realThresholdAxisFreezing separation
  have hthreshold : Real.exp ((p + 2) ^ 9) ^ 2 * Real.exp p <
      (candidateSideCutoff separation : ℝ) :=
    hseparation.trans_lt (lt_candidateSideCutoff separation)
  obtain ⟨affine⟩ := freezing.problem.exists_certifiedAffineRefinement
    hσone K hcertificate hretained hp hdim hblocks Cgeo hCgeo hchart hpoly hcap
    hlong hthreshold hmass
  exact ⟨⟨freezing, affine⟩⟩

theorem exists_certifiedAffineRefinement_after_freezing
    (hσone : ∀ j, σ j ≤ 1)
    (K : Set ((X ⊕ (Σ j, J j)) → ℝ)) {p : ℝ} {blocks : ℕ}
    (hcertificate : RationalTaggedConstraintCertificate J Set.univ K p blocks)
    (hretained : ∀ t, (∀ j, (fun i => t (Sum.inr ⟨j, i⟩)) ∈ U j) → t ∈ K)
    (hp : 0 ≤ p) (hdim : (Fintype.card (Σ j, J j) : ℝ) ≤ p)
    (hblocks : (blocks : ℝ) ≤ p)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hcap : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ Real.exp p)
    (hmass : 0 < massThreshold) :
    Nonempty (P.CertifiedThresholdAffineRefinement K p (certifiedAffineLongSideBound p)) :=
  P.exists_certifiedThresholdAffineRefinement hσone K hcertificate hretained hp hdim hblocks
    Cgeo hCgeo hchart hpoly hcap (certifiedAffineLongSideBound p) le_rfl hmass

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem.CertifiedThresholdAffineRefinement

variable {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {K : Set ((X ⊕ (Σ j, J j)) → ℝ)} {p separation : ℝ}

theorem common_keep (selected : P.CertifiedThresholdAffineRefinement K p separation)
    (hcost : Real.exp cost ≤ separation) (z : selected.problem.productive) :
    (selected.problem.chart z).keep =
      fun i => candidateSideCutoff separation ≤ A.sides i := by
  funext i
  apply propext
  change ((P.chart ⟨z.val, selected.affine.refinement.subset z.property⟩).keep i ∧
    candidateSideCutoff separation ≤ A.sides i) ↔ _
  constructor
  · exact fun hi => hi.2
  · intro hi
    refine ⟨?_, hi⟩
    by_contra hnot
    have hfrozen := P.frozen_side
      ⟨z.val, selected.affine.refinement.subset z.property⟩ ⟨i, hnot⟩
    have hside : (candidateSideCutoff separation : ℝ) ≤ (A.sides i : ℝ) :=
      Nat.cast_le.mpr hi
    exact (not_lt_of_ge (hfrozen.trans hcost))
      ((lt_candidateSideCutoff separation).trans_le hside)

end AllocatedExternalCandidateProblem.CertifiedThresholdAffineRefinement
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration
open scoped BigOperators Classical TensorProduct

attribute [local irreducible] HasCommonRefilteredOrbitFactors polynomialOrbitCoordinates
  weightedAdaptedRealChartHom

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}

namespace Refinement

variable {newCost newMass newScore : ℝ}
    (refinement : P.Refinement newCost newMass newScore)

theorem nativeFactors
    {ι : Type*} [Fintype ι] (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = Submodule.span ℚ (bD '' {i | j ≤ ω i}))
    (q : ℝ) (l : ℕ) (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (hOriginal : ∀ z : P.productive,
      D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
        (fun i : (P.chart z).Variables => (A.sides i.val : ℝ)) q l W
        (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
          (P.candidate z).orbit))
    (z : refinement.problem.productive) :
    D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : (refinement.problem.chart z).Variables => (A.sides i.val : ℝ)) q l W
      (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
        (refinement.problem.candidate z).orbit) :=
  hOriginal ⟨z.val, refinement.subset z.property⟩

end Refinement

namespace CertifiedThresholdAffineRefinement

variable {K : Set ((X ⊕ (Σ j, J j)) → ℝ)} {p separation : ℝ}
    (selected : P.CertifiedThresholdAffineRefinement K p separation)

theorem nativeFactors
    {ι : Type*} [Fintype ι] (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = Submodule.span ℚ (bD '' {i | j ≤ ω i}))
    (q : ℝ) (l : ℕ) (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (hOriginal : ∀ z : P.productive,
      D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
        (fun i : (P.chart z).Variables => (A.sides i.val : ℝ)) q l W
        (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
          (P.candidate z).orbit))
    (z : selected.problem.productive) :
    D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : (selected.problem.chart z).Variables => (A.sides i.val : ℝ)) q l W
      (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
        (selected.problem.candidate z).orbit) :=
  selected.affine.refinement.nativeFactors bD ω hD q l W
    (fun a => selected.freezing.problem_nativeFactors bD ω hD q l W a (hOriginal a)) z

theorem withKeep_nativeFactors
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : selected.problem.productive, (selected.problem.chart z).keep = keep)
    {ι : Type*} [Fintype ι] (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = Submodule.span ℚ (bD '' {i | j ≤ ω i}))
    (q : ℝ) (l : ℕ) (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (hOriginal : ∀ z : P.productive,
      D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
        (fun i : (P.chart z).Variables => (A.sides i.val : ℝ)) q l W
        (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
          (P.candidate z).orbit))
    (z : selected.problem.productive) :
    D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : {i // keep i} => (A.sides i.val : ℝ)) q l W
      (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
        ((selected.problem.withKeep keep hkeep).candidate z).orbit) :=
  (selected.problem.candidate z).hasCommonRefilteredOrbitFactors_withKeep
    keep (hkeep z) bD ω hD q l W (selected.nativeFactors bD ω hD q l W hOriginal z)

end CertifiedThresholdAffineRefinement
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem.CertifiedThresholdAffineRefinement

variable {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {K : Set ((X ⊕ (Σ j, J j)) → ℝ)} {p separation : ℝ}

theorem original_dense (selected : P.CertifiedThresholdAffineRefinement K p separation)
    (z : selected.problem.productive) :
    IsDenseCommonStrideBox
      (fun i : (selected.problem.chart z).Variables => A.sides i.val) cost
      (selected.problem.chart z).slice.integerPoints := by
  rw [selected.affine.slice_points z]
  exact selected.freezing.problem_slice_dense
    ⟨z.val, selected.affine.refinement.subset z.property⟩

theorem slice_length_gt (selected : P.CertifiedThresholdAffineRefinement K p separation)
    (degree : ℕ)
    (hseparation : Real.exp cost * ((degree + 1 : ℕ) : ℝ) ≤ separation)
    (z : selected.problem.productive) (i : (selected.problem.chart z).Variables) :
    degree < (selected.problem.chart z).slice.length i :=
  (selected.problem.chart z).slice_length_gt_of_dense_cutoff
    (selected.original_dense z) degree hseparation
    (fun a ha => (selected.long z a ha).le) i

end AllocatedExternalCandidateProblem.CertifiedThresholdAffineRefinement
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration
open scoped BigOperators Classical TensorProduct

attribute [local irreducible] HasCommonRefilteredOrbitFactors polynomialOrbitCoordinates
  weightedAdaptedRealChartHom

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem
variable {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}

namespace CertifiedThresholdAffineRefinement

variable {K : Set ((X ⊕ (Σ j, J j)) → ℝ)} {p separation : ℝ}
    (selected : P.CertifiedThresholdAffineRefinement K p separation)

theorem nativeFactors_of_zero_restriction
    (initialLong : LayerSamplerVariables G I n B → Prop)
    (hsub : ∀ z i, P.realThresholdKeep separation z i → initialLong i)
    {ι : Type*} [Fintype ι] (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = Submodule.span ℚ (bD '' {i | j ≤ ω i}))
    (q : ℝ) (l : ℕ) (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (hzero : ∀ z : P.productive,
      D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
        (fun i : {i // initialLong i} => (A.sides i.val : ℝ)) q l W
        (D.filtration.weightedAdaptedRealChartHom (fun _ : (P.chart z).Variables => 1)
          (fun _ : {i // initialLong i} => 1)
          ((P.chart z).axisPolynomial initialLong (fun _ => 0))
          ((P.chart z).axisPolynomial_support initialLong (fun _ => 0))
          (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
            (P.candidate z).orbit)))
    (z : selected.problem.productive) :
    D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : (selected.problem.chart z).Variables => (A.sides i.val : ℝ)) q l W
      (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
        (selected.problem.candidate z).orbit) :=
  selected.affine.refinement.nativeFactors bD ω hD q l W
    (fun a => selected.freezing.problem_nativeFactors_of_zero_restriction
      initialLong hsub bD ω hD q l W a (hzero a)) z

theorem withKeep_nativeFactors_of_zero_restriction
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : selected.problem.productive, (selected.problem.chart z).keep = keep)
    (initialLong : LayerSamplerVariables G I n B → Prop)
    (hsub : ∀ z i, P.realThresholdKeep separation z i → initialLong i)
    {ι : Type*} [Fintype ι] (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = Submodule.span ℚ (bD '' {i | j ≤ ω i}))
    (q : ℝ) (l : ℕ) (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (hzero : ∀ z : P.productive,
      D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
        (fun i : {i // initialLong i} => (A.sides i.val : ℝ)) q l W
        (D.filtration.weightedAdaptedRealChartHom (fun _ : (P.chart z).Variables => 1)
          (fun _ : {i // initialLong i} => 1)
          ((P.chart z).axisPolynomial initialLong (fun _ => 0))
          ((P.chart z).axisPolynomial_support initialLong (fun _ => 0))
          (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
            (P.candidate z).orbit)))
    (z : selected.problem.productive) :
    D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : {i // keep i} => (A.sides i.val : ℝ)) q l W
      (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
        ((selected.problem.withKeep keep hkeep).candidate z).orbit) :=
  (selected.problem.candidate z).hasCommonRefilteredOrbitFactors_withKeep
    keep (hkeep z) bD ω hD q l W (selected.nativeFactors_of_zero_restriction initialLong hsub bD ω hD q l W hzero z)

end CertifiedThresholdAffineRefinement
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical TensorProduct
attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  symbolPointwiseSubalgebra realificationLieSubalgebra PolynomialRationalGrid PolynomialSlowBound
  HasCommonRefilteredOrbitFactors polynomialOrbitCoordinates associatedGradedMap realPolynomialGroupMap
  AllocatedExternalCandidateProblem.Refinement.problem

theorem exists_allocatedThresholdAffineFamilyReset (s a : ℕ) :
    ∃ Ccompare Cf Cnative : ℕ, 2 ≤ Ccompare ∧ 2 ≤ Cf ∧ 2 ≤ Cnative ∧
    ∀ {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
      {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
      {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ i, Fintype (B i)]
      {U : ∀ j, Submodule ℝ (J j → ℝ)}
      {btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
      {Rad σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U btag Rad σ}
      {hb : ∀ j, span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (U j))}
      {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
      {hRad : ∀ j, 0 < Rad j} {hσ : ∀ j, 0 < σ j}
      {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
      {hm : ∀ j e, coefficients (poly j) e ∈ U j}
      {τ narrow : ℝ} {stride : X → ℕ}
      {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
      {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
      [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
      {sampler : AllocatedExternalCandidateSampler B U btag S hb o hRad hσ N poly hm τ narrow stride cells center}
      {L M κ ξ μ χ : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      [Fintype κ] [Fintype ξ] [Fintype μ] [Fintype χ]
      {d f : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
      (Fmark : RationalFilteredNilmanifold M (s + 1) f)
      (φ : L →ₗ⁅ℚ⁆ M)
      (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
      (ω : Fin d → ℕ)
      (hD : ∀ j, D.filtration.layer j = span ℚ (D.basis '' {i | j ≤ ω i}))
      (bF : Basis κ ℚ M) (ν : κ → ℕ)
      (hF : ∀ j, Fmark.filtration.layer j = span ℚ (bF '' {i | j ≤ ν i})),
      (∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y) →
    ∀ (separation : ℝ),
      let keep : LayerSamplerVariables G I n B → Prop :=
        fun i => candidateSideCutoff separation ≤ sampler.sides i;
    ∀ (bk : Basis ξ ℚ (LinearMap.ker φ.toLinearMap))
      (W : LieSubalgebra ℚ D.filtration.AssociatedGraded) (v : μ → D.filtration.AssociatedGraded),
      BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis ω hD) ω W.toSubmodule →
      Submodule.span ℚ (Set.range v) = W.toSubmodule →
    ∀ (vg : χ → Fmark.filtration.PolynomialSymbol (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)),
      Submodule.span ℚ (Set.range vg) =
        (Fmark.filtration.symbolPointwiseSubalgebra bF ν hF (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)
          (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))).toSubmodule →
    ∀ [Fintype (SymbolBasisIndex (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1) ω)]
      [Fintype (SymbolBasisIndex (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1) ν)]
      (H l nFinal : ℕ) (pMap pNative : ℝ),
      1 ≤ H → 0 < l → 0 < nFinal → 0 ≤ pMap → 0 ≤ pNative →
      (Fintype.card (SymbolBasisIndex (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1) ω) : ℝ) ≤ pMap →
      (Fintype.card (SymbolBasisIndex (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1) ν) : ℝ) ≤ pMap →
      (H : ℝ) ≤ Real.exp pMap → ((l * nFinal : ℕ) : ℝ) ≤ Real.exp pMap →
      Real.exp ((pMap + 2) ^ 4) ≤ Real.exp pNative →
      (d : ℝ) ≤ pNative → (Fintype.card κ : ℝ) ≤ pNative →
      (Fintype.card ξ : ℝ) ≤ pNative → (Fintype.card μ : ℝ) ≤ pNative →
      (Fintype.card χ : ℝ) ≤ pNative → (Fintype.card {i : LayerSamplerVariables G I n B // keep i} : ℝ) ≤ pNative →
      (H : ℝ) ≤ Real.exp pNative →
      (∀ i j k, RationalHeightLE (D.basis.repr ⁅D.basis i, D.basis j⁆ k) H) →
      (∀ i j k, RationalHeightLE (bF.repr ⁅bF i, bF j⁆ k) H) →
      (∀ i j, RationalHeightLE (D.basis.repr (bk j : L) i) H) →
      (∀ k i, RationalHeightLE (bF.repr (φ (D.basis i)) k) H) →
      (∀ j i, RationalHeightLE ((D.filtration.associatedGradedBasis D.basis ω hD).repr (v j) i) H) →
      (∀ i z, RationalHeightLE
        ((Fmark.filtration.polynomialSymbolBasis bF ν hF (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)).repr (vg i) z) H) →
    ∃ mMap mReset : ℕ, 0 < mMap ∧ (mMap : ℝ) ≤ Real.exp ((pMap + 2) ^ 4) ∧
      l * nFinal ∣ mMap ∧ 0 < mReset ∧
      (mReset : ℝ) ≤ Real.exp ((markedNativeLiftInput
        (fullMarkedNativeInput (s + 1) a Cf pNative) + Cnative) ^ Cnative) ∧ mMap ∣ mReset ∧
    ∀ (marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
      (observable : (X → ℤ) → D.Space → ℂ) (weight : (X → ℤ) → ℂ)
      {cost massThreshold scoreThreshold : ℝ}
      (P : AllocatedExternalCandidateProblem (E := E) sampler D Fmark.filtration φ marked
        observable weight cost massThreshold scoreThreshold)
      {K : Set ((X ⊕ (Σ j, J j)) → ℝ)} {pAffine : ℝ}
      (selected : P.CertifiedThresholdAffineRefinement K pAffine separation)
      (hcost : Real.exp cost ≤ separation)
      (EF RF : Fmark.filtration.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
      (factors : GlobalMarkedNativeFactors Fmark.filtration bF ν hF
        (fullTaggedVariableWeight J)
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))
        (Fmark.filtration.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
          (fullTaggedVariableWeight J) selected.affine.globalChart selected.affine.globalChart_support
          (Fmark.filtration.realification.polynomialOrbitCoordinates _ marked)) EF RF),
      Fmark.filtration.PolynomialRationalGrid bF (fullTaggedVariableWeight J) nFinal factors.right →
      (∀ z : selected.problem.productive,
        let C := selected.problem.chart z
        Fmark.filtration.PolynomialSlowBound bF (fun _ : C.Variables => 1)
          (fun i => (sampler.sides i.val : ℝ)) (Real.exp ((pNative + 2) ^ a))
          (Fmark.filtration.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
            (fun _ : C.Variables => 1) (integerSampledRealChart C.integerChart)
            C.integerChart_support factors.left)) →
      Real.exp ((pNative + Ccompare) ^ Ccompare) ≤ separation →
    ∀ (q : ℝ),
      Real.exp q ≤ Real.exp ((pNative + 2) ^ a) →
      Real.exp ((pMap + 2) ^ 3 + q) ≤ Real.exp ((pNative + 2) ^ a) →
      Real.exp cost * ((s + 1 + 1 : ℕ) : ℝ) ≤ separation →
      (∀ z : P.productive,
        D.filtration.HasCommonRefilteredOrbitFactors D.basis ω hD
          (fun i : (P.chart z).Variables => (sampler.sides i.val : ℝ)) q l W
          (D.filtration.realification.polynomialOrbitCoordinates _ (P.candidate z).orbit)) →
      Nonempty (AllocatedExternalGlobalNativeResetFamily Fmark φ hφ
        selected.problem keep (selected.common_keep hcost) W factors
        (Real.exp ((markedNativeLiftInput (fullMarkedNativeInput (s + 1) a Cf pNative)
          + Cnative) ^ Cnative)) mReset) := by
  classical
  obtain ⟨Ccompare, Cf, Cnative, hCcompare, hCf, hCnative, hreset⟩ :=
    exists_allocatedCertifiedAffineFamilyReset s a
  refine ⟨Ccompare, Cf, Cnative, hCcompare, hCf, hCnative, ?_⟩
  intro m G X _ _ I E J _ _ n B _ U btag Rad σ S hb o hRad hσ N poly hm
    τ narrow stride cells center _ sampler L M κ ξ μ χ _ _ _ _ _ _ _ _ d f
    D Fmark φ hφ ω hD bF ν hF hsurj separation keep bk W v hW hvspan vg hvgspan _ _
    H l nFinal pMap pNative hH hl hnFinal hpMap hpNative hsrc htgt hHmap hlmap hmabsorb
    hd hκ hξ hμ hχ hvars hHp hbracketD hbracketF hkernel hentries hv hvg
  obtain ⟨mMap, mReset, hmMap, hmMapBound, hdiv, hmReset, hmResetBound, hmMapReset, hrun⟩ :=
    hreset (sampler := sampler) (E := E) D Fmark φ hφ ω hD bF ν hF hsurj keep
      bk W v hW hvspan vg hvgspan H l nFinal pMap pNative hH hl hnFinal hpMap hpNative
      hsrc htgt hHmap hlmap hmabsorb hd hκ hξ hμ hχ (by
        convert hvars using 1
        simp only [Fintype.card_eq_nat_card]) hHp
      hbracketD hbracketF hkernel hentries hv hvg
  refine ⟨mMap, mReset, hmMap, hmMapBound, hdiv, hmReset, hmResetBound, hmMapReset, ?_⟩
  intro marked observable weight cost massThreshold scoreThreshold P K pAffine selected hcost
    EF RF factors hgrid hslow hsideBound q hq hqmap hcutoff hOriginal
  have hside (i : {i : LayerSamplerVariables G I n B // keep i}) :
      Real.exp ((pNative + Ccompare) ^ Ccompare) ≤ (sampler.sides i.val : ℝ) := by
    exact hsideBound.trans ((lt_candidateSideCutoff separation).le.trans
      (Nat.cast_le.mpr i.property))
  have hlong (i : LayerSamplerVariables G I n B) (hi : keep i) :
      separation ≤ layerSamplerBox B U btag S i := by
    rw [allocatedParameterBox_side_eq B U btag S i]
    exact (lt_candidateSideCutoff separation).le.trans (Nat.cast_le.mpr hi)
  exact hrun marked observable weight selected.freezing.problem selected.affine
    (selected.common_keep hcost) EF RF factors hgrid hslow hside q cost separation hq hqmap
    selected.original_dense hcutoff hlong
    (selected.withKeep_nativeFactors keep (selected.common_keep hcost)
      D.basis ω hD q l W hOriginal)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

private theorem affine_selection_budget_arithmetic {p l loss c cutoff R : ℝ}
    (_hp : 0 ≤ p) (hl : 0 ≤ l) (hloss : 0 ≤ loss)
    (hpc : p ≤ c) (hcut : cutoff ≤ c) (hR : l+loss+c ≤ R) :
    max p cutoff ≤ R ∧
      Real.exp (-R) ≤ Real.exp (-loss) * Real.exp (-p) ∧
      Real.exp (-R) ≤ Real.exp (-p) := by
  have hpR : p ≤ R := by linarith only [_hp, hl, hloss, hpc, hR]
  refine ⟨max_le hpR (by linarith only [_hp, hl, hloss, hpc, hcut, hR]), ?_,
    Real.exp_le_exp.mpr (neg_le_neg hpR)⟩
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith only [hl, hpc, hR]

theorem exists_certified_affine_normalized_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      max p (candidateSideCutoffCost (certifiedAffineLongSideBound p)) ≤ (p+C)^C ∧
      Real.exp (-(p+C)^C) ≤
        Real.exp (-((2*certifiedAffineCenterBudget p+3)^3)) * Real.exp (-p) ∧
      Real.exp (-(p+C)^C) ≤ Real.exp (-p) := by
  obtain ⟨C,hC,hbudget⟩ := exists_certifiedAffineCenterBudget_power
  refine ⟨C,hC,?_⟩
  intro p hp
  have hL : 0 ≤ certifiedAffineCenterBudget p := by
    unfold certifiedAffineCenterBudget
    positivity
  apply affine_selection_budget_arithmetic hp hL (by positivity)
    (show p ≤ 2*(p+2)^9+p+2 by
      have h := show 0 ≤ 2*(p+2)^9 from by positivity
      linarith only [h])
    (candidateSideCutoffCost_canonical_affine hp) (hbudget p hp)

end Erdos3.VectorPolynomial

end

end OAI
