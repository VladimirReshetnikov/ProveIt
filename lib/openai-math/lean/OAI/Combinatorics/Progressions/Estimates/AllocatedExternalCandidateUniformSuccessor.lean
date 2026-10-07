import OAI.Combinatorics.Progressions.Dynamics.AllocatedExternalCandidateCoveredBudget
import OAI.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateRefilteredSupportedStep

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

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
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateProblem

variable {L M ι κ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF nQ nQF : ℕ}
    {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (hDref : Dref.filtration = D.filtration.gradedRefiltration W)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (hFref : Fref.filtration = Fmark.filtration.gradedRefiltration
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))

    (markedMiddle : Fref.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (middle : ∀ z : P.productive,
      AllocatedExternalLocalCandidate (P.chart z) Dref Fref.filtration (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) markedMiddle)

variable (sectionMap : M →ₗ[ℚ] L)
    (hSectionFilt : ∀ j, ∀ y ∈ Fmark.filtration.layer j, sectionMap y ∈ D.filtration.layer j)
    (hsection : Function.RightInverse sectionMap φ)
    (leftMark rightMark : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (kE kR : D.RealGroup)
    (hkE : realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ kE = 1)
    (hkR : realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ kR = 1)
    (localLeft localRight : ∀ z : P.productive,
      (D.filtration.realification.adaptedPolynomialFiltration
        (fun _ : (P.chart z).Variables => 1)).Group)
    (localLeftMark localRightMark : ∀ z : P.productive,
      (Fmark.filtration.realification.adaptedPolynomialFiltration
        (fun _ : (P.chart z).Variables => 1)).Group)
    (hfactor : ∀ z : P.productive,
      localLeft z * P.refilteredLocalCoordinates A Fmark φ hφ W Dref hDref Fref
        markedMiddle middle z * localRight z =
      D.filtration.realification.polynomialOrbitCoordinates _ (P.candidate z).orbit)
    (hleft : ∀ z : P.productive, ∀ u ∈ (P.chart z).slice.integerPoints,
      Fmark.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ))
        (localLeftMark z) =
      Fmark.filtration.realification.polynomialOrbitRealEval (fullTaggedVariableWeight (X := X) J)
        (fun i => ((P.chart z).chartValues u i : ℝ)) leftMark)
    (hright : ∀ z : P.productive, ∀ u ∈ (P.chart z).slice.integerPoints,
      Fmark.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ))
        (localRightMark z) =
      Fmark.filtration.realification.polynomialOrbitRealEval (fullTaggedVariableWeight (X := X) J)
        (fun i => ((P.chart z).chartValues u i : ℝ)) rightMark)

namespace Refinement

variable {A Fmark φ P} {newCost newMass newScore : ℝ}
    (refinement : P.Refinement newCost newMass newScore)

include hsection hkE hkR hfactor hleft hright

theorem nativeFrozen_mark_on_slice
    (hprojLeft : ∀ z, D.filtration.realPolynomialGroupMap Fmark.filtration φ hφ
      (fun _ => 1) (localLeft z) = localLeftMark z)
    (hprojRight : ∀ z, D.filtration.realPolynomialGroupMap Fmark.filtration φ hφ
      (fun _ => 1) (localRight z) = localRightMark z)
    (z : refinement.problem.productive) (u : (refinement.problem.chart z).Variables → ℤ)
    (hu : u ∈ (refinement.problem.chart z).slice.integerPoints) :
    realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ
      (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
          ((refinement.problem.chart z).chartValues u)
          (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J)
            sectionMap hSectionFilt leftMark kE) *
        realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
          (hM := D.filtration.lowerCentralSeries_eq_bot)
          (D.filtration.gradedRefiltrationSubalgebra W).incl
          (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u
            ((refinement.refilteredMiddle hφ W Dref Fref markedMiddle middle) z).orbit) *
        D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
          ((refinement.problem.chart z).chartValues u)
          (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J)
            sectionMap hSectionFilt rightMark kR)) =
      Fmark.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
        ((refinement.problem.chart z).chartValues u) marked := by
  apply refinement.refiltered_mark_on_slice hφ W Dref Fref markedMiddle middle
    (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J)
      sectionMap hSectionFilt leftMark kE)
    (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J)
      sectionMap hSectionFilt rightMark kR) ?_ z u hu
  exact P.refilteredFrozen_mark_on_slice A Fmark φ hφ W Dref hDref Fref markedMiddle middle
    sectionMap hSectionFilt hsection leftMark rightMark kE kR hkE hkR
    localLeft localRight localLeftMark localRightMark hfactor hleft hright hprojLeft hprojRight

end Refinement
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

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

namespace AllocatedExternalCandidateProblem

variable {L M κ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P₀ : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P₀.productive, (P₀.chart z).keep = keep)

variable (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (hDref : Dref.filtration = D.filtration.gradedRefiltration W)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (markedMiddle : Fref.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (middle : ∀ z : (P₀.withKeep keep hkeep).productive,
      AllocatedExternalLocalCandidate ((P₀.withKeep keep hkeep).chart z) Dref Fref.filtration
        (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) markedMiddle)
    (sectionMap : M →ₗ[ℚ] L)
    (hSectionFilt : ∀ j, ∀ y ∈ Fmark.filtration.layer j, sectionMap y ∈ D.filtration.layer j)
    (c : Basis κ ℚ M)
    (leftMark rightMark : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (localLeft localRight : (P₀.withKeep keep hkeep).productive →
      (D.filtration.realification.adaptedPolynomialFiltration (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1)).Group)
    (localLeftMark localRightMark : (P₀.withKeep keep hkeep).productive →
      (Fmark.filtration.realification.adaptedPolynomialFiltration (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1)).Group)
    (hfactor : ∀ z : (P₀.withKeep keep hkeep).productive,
      (show (D.filtration.realification.adaptedPolynomialFiltration
          (fun _ : ((P₀.withKeep keep hkeep).chart z).Variables => 1)).Group from localLeft z) *
        (P₀.withKeep keep hkeep).refilteredLocalCoordinates A Fmark φ hφ W Dref hDref Fref
          markedMiddle middle z *
        (show (D.filtration.realification.adaptedPolynomialFiltration
          (fun _ : ((P₀.withKeep keep hkeep).chart z).Variables => 1)).Group from localRight z) =
      D.filtration.realification.polynomialOrbitCoordinates _ ((P₀.withKeep keep hkeep).candidate z).orbit)
    (hprojLeft : ∀ z, D.filtration.realPolynomialGroupMap Fmark.filtration φ hφ
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) (localLeft z) = localLeftMark z)
    (hprojRight : ∀ z, D.filtration.realPolynomialGroupMap Fmark.filtration φ hφ
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) (localRight z) = localRightMark z)
    (hleft : ∀ z : (P₀.withKeep keep hkeep).productive, ∀ u ∈ ((P₀.withKeep keep hkeep).chart z).slice.integerPoints,
      Fmark.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ))
        (localLeftMark z) =
      Fmark.filtration.realification.polynomialOrbitRealEval (fullTaggedVariableWeight (X := X) J)
        (fun i => (((P₀.withKeep keep hkeep).chart z).chartValues u i : ℝ)) leftMark)
    (hright : ∀ z : (P₀.withKeep keep hkeep).productive, ∀ u ∈ ((P₀.withKeep keep hkeep).chart z).slice.integerPoints,
      Fmark.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ))
        (localRightMark z) =
      Fmark.filtration.realification.polynomialOrbitRealEval (fullTaggedVariableWeight (X := X) J)
        (fun i => (((P₀.withKeep keep hkeep).chart z).chartValues u i : ℝ)) rightMark)
    (tests : (X → ℤ) → D.Niltest (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1))
    (htests : ∀ x, (tests x).observable = observable x)
    (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))

variable (hFref : Fref.filtration = Fmark.filtration.gradedRefiltration
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))
    {nQ nQF : ℕ}
    (Qquot : RationalFilteredNilmanifold
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)) s nQ)
    (hQquot : Qquot.filtration = Dref.filtration.quotientTop)
    (Fquot : RationalFilteredNilmanifold
      ((Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) ⧸
        Fref.filtration.layerIdeal (s + 1)) s nQF)
    (hFquot : Fquot.filtration = Fref.filtration.quotientTop)
    [PseudoMetricSpace Qquot.Space] [PseudoMetricSpace Fref.Space]
    (K : ℝ≥0)

include hQquot hDref hfactor hprojLeft hprojRight hleft hright htests hσ1 H hH hchart hsmall hp

theorem conclusion_of_dictionary_successor
    {l : ℕ} {slow ε budget Bweight Bobs Lip frozenThreshold θ densityCost : ℝ}
    (dictionary : RationalFilteredNilmanifold.ExternalMarkedAffineSliceFreezing.Dictionary
      (X := X → ℤ) D Fmark.filtration c φ hφ
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) sectionMap hSectionFilt l
      (fun i : { i : LayerSamplerVariables G I n B // keep i } => (A.sides i.val : ℝ)) slow ε budget)
    (hslowLeft : ∀ z, D.filtration.PolynomialSlowBound D.basis (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1)
      (fun i : { i : LayerSamplerVariables G I n B // keep i } => (A.sides i.val : ℝ)) slow (localLeft z))
    (hslowMark : ∀ z, Fmark.filtration.PolynomialSlowBound c (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1)
      (fun i : { i : LayerSamplerVariables G I n B // keep i } => (A.sides i.val : ℝ)) slow (localLeftMark z))
    (hrationalRight : ∀ z, D.filtration.PolynomialRationalGrid D.basis
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) l (localRight z))
    (hrationalMark : ∀ z, Fmark.filtration.PolynomialRationalGrid c
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) l (localRightMark z))
    (hdensity : ∀ z : (P₀.withKeep keep hkeep).productive,
      IsDenseCommonStrideBox
        (fun i : ((P₀.withKeep keep hkeep).chart z).Variables => A.sides i.val)
        densityCost ((P₀.withKeep keep hkeep).chart z).slice.integerPoints)
    (hfloor : ∀ i : { i : LayerSamplerVariables G I n B // keep i },
      Real.exp densityCost * max 2 (2 * budget * max 1 budget) ≤ (A.sides i.val : ℝ))
    (hBweight : 0 ≤ Bweight) (hBobs : 0 ≤ Bobs) (hLip : 0 ≤ Lip) (hε : 0 ≤ ε)
    (hweight : ∀ x, ‖weight x‖ ≤ Bweight)
    (hnorm : ∀ x, ((tests x).normBound : ℝ) ≤ Bobs)
    (hlip : ∀ x, ((tests x).lipBound : ℝ) ≤ Lip)
    (hthreshold : 0 ≤ frozenThreshold) (hθ : 0 < θ)
    (hbudget : frozenThreshold + Bweight * (Lip * ε) + (Bweight * Bobs) * θ < scoreThreshold)
    (hsection : Function.RightInverse sectionMap φ)
    (hmass : 0 ≤ massThreshold)
    (dw : Fin d → ℕ)
    (hdb : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ dw i}))
    (fw : κ → ℕ)
    (hfb : ∀ j, Fmark.filtration.layer j = Submodule.span ℚ (c '' {i | j ≤ fw i}))
    (hW : BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis dw hdb) dw W.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (hξ1 : ξ ≤ 1)
    (hrecovery : ∀ ij : (Fin d → Fin (dictionary.grid + 1)) × Fin dictionary.rightCount, ∀ x, x ∈ integerBox N → ∀ source,
      positiveImageSlice
        (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Qquot) K
        ((P₀.withKeep keep hkeep).refilteredFrozenObservable A Fmark φ W Dref (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt leftMark (dictionary.left ij.1)) (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt rightMark (dictionary.right ij.2)) x)
        (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Qquot source).2
        (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Qquot source).1 =
        (P₀.withKeep keep hkeep).refilteredFrozenObservable A Fmark φ W Dref (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt leftMark (dictionary.left ij.1)) (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt rightMark (dictionary.right ij.2)) x source)
    (recursionParameter : ℝ)
    (hcostRec : (max cost (densityCost + Real.log ((4 * budget * max 1 budget * (Fintype.card { i : LayerSamplerVariables G I n B // keep i } + 1 : ℝ)) / θ))) ≤ recursionParameter)
    (hmassRec : Real.exp (-recursionParameter) ≤ massThreshold / budget ^ 2)
    (hscoreRec : Real.exp (-recursionParameter) ≤ frozenThreshold)
    {outputCost outputMass outputScore : ℝ}
    (recurse : ∀ ij : (Fin d → Fin (dictionary.grid + 1)) × Fin dictionary.rightCount,
      ∀ lowerProblem : AllocatedExternalCandidateProblem (E := E) A Qquot Fquot.filtration
        (Dref.topQuotientMarkedMap Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) (D.refilteredMarkedMap_mem_layer Fmark φ hφ W Dref hDref Fref hFref)) (Fref.topQuotientOrbit Fquot hFquot markedMiddle)
        ((P₀.withKeep keep hkeep).refilteredQuotientObservable A Fmark φ hφ W Dref Fref Qquot (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt leftMark (dictionary.left ij.1)) (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt rightMark (dictionary.right ij.2)) markedMiddle K)
        weight recursionParameter (Real.exp (-recursionParameter)) (Real.exp (-recursionParameter)),
        Nonempty (lowerProblem.Conclusion outputCost outputMass outputScore)) :
    Nonempty (P₀.Conclusion outputCost outputMass outputScore) := by
  obtain ⟨chosen, refinement, hfrozen⟩ :=
    P₀.exists_finite_freezing_refinement_of_dictionary Fmark φ hφ keep hkeep W Dref hDref Fref
      markedMiddle middle sectionMap hSectionFilt c leftMark rightMark
      localLeft localRight localLeftMark localRightMark hfactor hprojLeft hprojRight
      hleft hright tests htests hσ1 H hH hchart hsmall hp
      dictionary hslowLeft hslowMark hrationalRight hrationalMark hdensity hfloor
      hBweight hBobs hLip hε hweight hnorm hlip hthreshold hθ hbudget
  let : Nonempty (Fin dictionary.rightCount) := ⟨⟨0, dictionary.rightCount_pos⟩⟩
  have hcostBound := finiteFreezing_cost_le_uniform
    (cost := cost) (densityCost := densityCost)
    (k := Fintype.card { i : LayerSamplerVariables G I n B // keep i })
    hθ dictionary.modulus_pos dictionary.Q_pos dictionary.modulus_bound dictionary.Q_bound
  have hmassBound : massThreshold / budget ^ 2 ≤
      massThreshold / (Fintype.card ((Fin d → Fin (dictionary.grid + 1)) × Fin dictionary.rightCount) : ℝ) :=
    div_le_div_of_nonneg_left hmass (by exact_mod_cast Fintype.card_pos) dictionary.pairCard_bound
  let uniform := refinement.mono (hcostBound.trans hcostRec) (hmassRec.trans hmassBound) le_rfl
  let leftOrbit := D.filtration.frozenMarkedLeftOrbit Fmark.filtration
    (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt leftMark (dictionary.left chosen.1)
  let rightOrbit := D.filtration.frozenMarkedRightOrbit Fmark.filtration
    (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt rightMark (dictionary.right chosen.2)
  have hscoreUniform : ∀ z : uniform.problem.productive, Real.exp (-recursionParameter) ≤
      uniform.problem.refilteredFrozenScore A Fmark φ hφ W Dref Fref leftOrbit rightOrbit
        markedMiddle (uniform.refilteredMiddle hφ W Dref Fref markedMiddle middle) z := by
    intro z
    exact hscoreRec.trans (hfrozen z)
  have hphysical := fun (z : uniform.problem.productive) u hu =>
    (uniform.problem.chart z).physical_mem_integerBox hξ1 u hu
  have hrec := hrecovery chosen
  let lowerProblem := uniform.problem.refilteredQuotientScoredProblem_on A Fmark φ hφ W
    Dref hDref Fref hFref Qquot hQquot Fquot hFquot leftOrbit rightOrbit markedMiddle K
    hσ1 H hH hchart hsmall hp
    (uniform.refilteredMiddle hφ W Dref Fref markedMiddle middle)
    (fun x => x ∈ integerBox N) hphysical hrec hscoreUniform
  obtain ⟨lower⟩ := recurse chosen lowerProblem
  have hmark := uniform.nativeFrozen_mark_on_slice hφ W Dref hDref Fref
    markedMiddle middle sectionMap hSectionFilt hsection leftMark rightMark
    (dictionary.left chosen.1) (dictionary.right chosen.2)
    (dictionary.left_bounds chosen.1).1 (dictionary.right_bounds chosen.2).1
    localLeft localRight localLeftMark localRightMark hfactor hleft hright hprojLeft hprojRight
  obtain ⟨out⟩ := uniform.problem.conclusion_of_refilteredQuotientScored_on A Fmark φ hφ W
    Dref hDref Fref hFref Qquot hQquot Fquot hFquot leftOrbit rightOrbit markedMiddle K
    hσ1 H hH hchart hsmall hp
    (uniform.refilteredMiddle hφ W Dref Fref markedMiddle middle)
    (fun x => x ∈ integerBox N) hphysical hrec hscoreUniform hmark
    D.basis dw hdb c fw hfb hW hsurj lower
  exact ⟨P₀.conclusion_of_withKeep keep hkeep (uniform.conclusion out)⟩

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

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

namespace AllocatedExternalCandidateProblem

variable {L M κ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P₀ : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P₀.productive, (P₀.chart z).keep = keep)

variable (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (hDref : Dref.filtration = D.filtration.gradedRefiltration W)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (markedMiddle : Fref.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (middle : ∀ z : (P₀.withKeep keep hkeep).productive,
      AllocatedExternalLocalCandidate ((P₀.withKeep keep hkeep).chart z) Dref Fref.filtration
        (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) markedMiddle)
    (sectionMap : M →ₗ[ℚ] L)
    (hSectionFilt : ∀ j, ∀ y ∈ Fmark.filtration.layer j, sectionMap y ∈ D.filtration.layer j)
    (c : Basis κ ℚ M)
    (leftMark rightMark : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (localLeft localRight : (P₀.withKeep keep hkeep).productive →
      (D.filtration.realification.adaptedPolynomialFiltration (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1)).Group)
    (localLeftMark localRightMark : (P₀.withKeep keep hkeep).productive →
      (Fmark.filtration.realification.adaptedPolynomialFiltration (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1)).Group)
    (hfactor : ∀ z : (P₀.withKeep keep hkeep).productive,
      (show (D.filtration.realification.adaptedPolynomialFiltration
          (fun _ : ((P₀.withKeep keep hkeep).chart z).Variables => 1)).Group from localLeft z) *
        (P₀.withKeep keep hkeep).refilteredLocalCoordinates A Fmark φ hφ W Dref hDref Fref
          markedMiddle middle z *
        (show (D.filtration.realification.adaptedPolynomialFiltration
          (fun _ : ((P₀.withKeep keep hkeep).chart z).Variables => 1)).Group from localRight z) =
      D.filtration.realification.polynomialOrbitCoordinates _ ((P₀.withKeep keep hkeep).candidate z).orbit)
    (hprojLeft : ∀ z, D.filtration.realPolynomialGroupMap Fmark.filtration φ hφ
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) (localLeft z) = localLeftMark z)
    (hprojRight : ∀ z, D.filtration.realPolynomialGroupMap Fmark.filtration φ hφ
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) (localRight z) = localRightMark z)
    (hleft : ∀ z : (P₀.withKeep keep hkeep).productive, ∀ u ∈ ((P₀.withKeep keep hkeep).chart z).slice.integerPoints,
      Fmark.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ))
        (localLeftMark z) =
      Fmark.filtration.realification.polynomialOrbitRealEval (fullTaggedVariableWeight (X := X) J)
        (fun i => (((P₀.withKeep keep hkeep).chart z).chartValues u i : ℝ)) leftMark)
    (hright : ∀ z : (P₀.withKeep keep hkeep).productive, ∀ u ∈ ((P₀.withKeep keep hkeep).chart z).slice.integerPoints,
      Fmark.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ))
        (localRightMark z) =
      Fmark.filtration.realification.polynomialOrbitRealEval (fullTaggedVariableWeight (X := X) J)
        (fun i => (((P₀.withKeep keep hkeep).chart z).chartValues u i : ℝ)) rightMark)
    (tests : (X → ℤ) → D.Niltest (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1))
    (htests : ∀ x, (tests x).observable = observable x)
    (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))

variable (hFref : Fref.filtration = Fmark.filtration.gradedRefiltration
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))
    {nQ nQF : ℕ}
    (Qquot : RationalFilteredNilmanifold
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)) s nQ)
    (hQquot : Qquot.filtration = Dref.filtration.quotientTop)
    (Fquot : RationalFilteredNilmanifold
      ((Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) ⧸
        Fref.filtration.layerIdeal (s + 1)) s nQF)
    (hFquot : Fquot.filtration = Fref.filtration.quotientTop)
    [PseudoMetricSpace Qquot.Space] [PseudoMetricSpace Fref.Space]
    (K : ℝ≥0)

include hQquot hDref hfactor hprojLeft hprojRight hleft hright htests hσ1 H hH hchart hsmall hp

theorem conclusion_of_finite_freezing_successor
    {l : ℕ} {slow ε budget Bweight Bobs Lip frozenThreshold θ densityCost : ℝ}
    (hfreeze : D.ExternalMarkedAffineSliceFreezing (X := X → ℤ) Fmark.filtration c φ hφ
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) sectionMap hSectionFilt l
      (fun i : { i : LayerSamplerVariables G I n B // keep i } => (A.sides i.val : ℝ)) slow ε budget)
    (hslowLeft : ∀ z, D.filtration.PolynomialSlowBound D.basis (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1)
      (fun i : { i : LayerSamplerVariables G I n B // keep i } => (A.sides i.val : ℝ)) slow (localLeft z))
    (hslowMark : ∀ z, Fmark.filtration.PolynomialSlowBound c (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1)
      (fun i : { i : LayerSamplerVariables G I n B // keep i } => (A.sides i.val : ℝ)) slow (localLeftMark z))
    (hrationalRight : ∀ z, D.filtration.PolynomialRationalGrid D.basis
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) l (localRight z))
    (hrationalMark : ∀ z, Fmark.filtration.PolynomialRationalGrid c
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) l (localRightMark z))
    (hdensity : ∀ z : (P₀.withKeep keep hkeep).productive,
      IsDenseCommonStrideBox
        (fun i : ((P₀.withKeep keep hkeep).chart z).Variables => A.sides i.val)
        densityCost ((P₀.withKeep keep hkeep).chart z).slice.integerPoints)
    (hfloor : ∀ i : { i : LayerSamplerVariables G I n B // keep i },
      Real.exp densityCost * max 2 (2 * budget * max 1 budget) ≤ (A.sides i.val : ℝ))
    (hBweight : 0 ≤ Bweight) (hBobs : 0 ≤ Bobs) (hLip : 0 ≤ Lip) (hε : 0 ≤ ε)
    (hweight : ∀ x, ‖weight x‖ ≤ Bweight)
    (hnorm : ∀ x, ((tests x).normBound : ℝ) ≤ Bobs)
    (hlip : ∀ x, ((tests x).lipBound : ℝ) ≤ Lip)
    (hthreshold : 0 ≤ frozenThreshold) (hθ : 0 < θ)
    (hbudget : frozenThreshold + Bweight * (Lip * ε) + (Bweight * Bobs) * θ < scoreThreshold)
    (hsection : Function.RightInverse sectionMap φ)
    (hmass : 0 ≤ massThreshold)
    (dw : Fin d → ℕ)
    (hdb : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ dw i}))
    (fw : κ → ℕ)
    (hfb : ∀ j, Fmark.filtration.layer j = Submodule.span ℚ (c '' {i | j ≤ fw i}))
    (hW : BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis dw hdb) dw W.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (hrecovery : ∀ denominator : ℕ, 0 < denominator → (denominator : ℝ) ≤ budget →
      ∀ kE kR : D.RealGroup,
      (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ kE = 1 ∧
        ∀ k, |(D.basis.baseChange ℝ).repr kE.coord k| ≤ budget) →
      (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ kR = 1 ∧
        (∀ k, |(D.basis.baseChange ℝ).repr kR.coord k| ≤ budget) ∧
        (D.basis.baseChange ℝ).equivFun kR.coord ∈ realDenominatorGrid denominator) →
      ∀ x source, positiveImageSlice
        (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Qquot) K
        ((P₀.withKeep keep hkeep).refilteredFrozenObservable A Fmark φ W Dref (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt leftMark kE) (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt rightMark kR) x)
        (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Qquot source).2
        (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Qquot source).1 =
        (P₀.withKeep keep hkeep).refilteredFrozenObservable A Fmark φ W Dref (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt leftMark kE) (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt rightMark kR) x source)
    {outputCost outputMass outputScore : ℝ}
    (recurse : ∀ denominator : ℕ, 0 < denominator → (denominator : ℝ) ≤ budget →
      ∀ kE kR : D.RealGroup,
      (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ kE = 1 ∧
        ∀ k, |(D.basis.baseChange ℝ).repr kE.coord k| ≤ budget) →
      (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ kR = 1 ∧
        (∀ k, |(D.basis.baseChange ℝ).repr kR.coord k| ≤ budget) ∧
        (D.basis.baseChange ℝ).equivFun kR.coord ∈ realDenominatorGrid denominator) →
      ∀ lowerProblem : AllocatedExternalCandidateProblem (E := E) A Qquot Fquot.filtration
        (Dref.topQuotientMarkedMap Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) (D.refilteredMarkedMap_mem_layer Fmark φ hφ W Dref hDref Fref hFref))
        (Fref.topQuotientOrbit Fquot hFquot markedMiddle)
        ((P₀.withKeep keep hkeep).refilteredQuotientObservable A Fmark φ hφ W Dref Fref Qquot (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt leftMark kE) (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt rightMark kR) markedMiddle K)
        weight (max cost (densityCost + Real.log ((4 * budget * max 1 budget * (Fintype.card { i : LayerSamplerVariables G I n B // keep i } + 1 : ℝ)) / θ))) (massThreshold / budget ^ 2) frozenThreshold,
        Nonempty (lowerProblem.Conclusion outputCost outputMass outputScore)) :
    Nonempty (P₀.Conclusion outputCost outputMass outputScore) := by
  obtain ⟨grid, Q, modulus, denominator, rightCount, hgrid, hQ, hQbound, hmodulus,
      hdenominator, hrightCount, hgridCard, hcellCard, hmodulusBound, hdenominatorBound,
      hrightBound, hpair, left, right, hleftCenters, hrightCenters, chosen,
      refinement, hfrozen⟩ :=
    P₀.exists_finite_freezing_refinement Fmark φ hφ keep hkeep W Dref hDref Fref
      markedMiddle middle sectionMap hSectionFilt c leftMark rightMark
      localLeft localRight localLeftMark localRightMark hfactor hprojLeft hprojRight
      hleft hright tests htests hσ1 H hH hchart hsmall hp
      hfreeze hslowLeft hslowMark hrationalRight hrationalMark hdensity hfloor
      hBweight hBobs hLip hε hweight hnorm hlip hthreshold hθ hbudget
  let : Nonempty (Fin rightCount) := ⟨⟨0, hrightCount⟩⟩
  have hcostBound := finiteFreezing_cost_le_uniform
    (cost := cost) (densityCost := densityCost)
    (k := Fintype.card { i : LayerSamplerVariables G I n B // keep i })
    hθ hmodulus hQ hmodulusBound hQbound
  have hmassBound : massThreshold / budget ^ 2 ≤
      massThreshold / (Fintype.card ((Fin d → Fin (grid + 1)) × Fin rightCount) : ℝ) :=
    div_le_div_of_nonneg_left hmass (by exact_mod_cast Fintype.card_pos) hpair
  let uniform := refinement.mono hcostBound hmassBound le_rfl
  let leftOrbit := D.filtration.frozenMarkedLeftOrbit Fmark.filtration
    (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt leftMark (left chosen.1)
  let rightOrbit := D.filtration.frozenMarkedRightOrbit Fmark.filtration
    (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt rightMark (right chosen.2)
  have hscoreUniform : ∀ z : uniform.problem.productive, frozenThreshold ≤
      uniform.problem.refilteredFrozenScore A Fmark φ hφ W Dref Fref leftOrbit rightOrbit
        markedMiddle (uniform.refilteredMiddle hφ W Dref Fref markedMiddle middle) z := by
    intro z
    exact hfrozen z
  have hrec := hrecovery denominator hdenominator hdenominatorBound
    (left chosen.1) (right chosen.2) (hleftCenters chosen.1) (hrightCenters chosen.2)
  let lowerProblem := uniform.problem.refilteredQuotientScoredProblem A Fmark φ hφ W
    Dref hDref Fref hFref Qquot hQquot Fquot hFquot leftOrbit rightOrbit markedMiddle K
    hσ1 H hH hchart hsmall hp
    (uniform.refilteredMiddle hφ W Dref Fref markedMiddle middle) hrec hscoreUniform
  obtain ⟨lower⟩ := recurse denominator hdenominator hdenominatorBound
    (left chosen.1) (right chosen.2) (hleftCenters chosen.1) (hrightCenters chosen.2) lowerProblem
  have hmark := uniform.nativeFrozen_mark_on_slice hφ W Dref hDref Fref
    markedMiddle middle sectionMap hSectionFilt hsection leftMark rightMark
    (left chosen.1) (right chosen.2) (hleftCenters chosen.1).1 (hrightCenters chosen.2).1
    localLeft localRight localLeftMark localRightMark hfactor hleft hright hprojLeft hprojRight
  obtain ⟨out⟩ := uniform.problem.conclusion_of_refilteredQuotientScored A Fmark φ hφ W
    Dref hDref Fref hFref Qquot hQquot Fquot hFquot leftOrbit rightOrbit markedMiddle K
    hσ1 H hH hchart hsmall hp
    (uniform.refilteredMiddle hφ W Dref Fref markedMiddle middle) hrec hscoreUniform hmark
    D.basis dw hdb c fw hfb hW hsurj lower
  exact ⟨P₀.conclusion_of_withKeep keep hkeep (uniform.conclusion out)⟩

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

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

namespace AllocatedExternalCandidateProblem

variable {L M κ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f nD nF : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P₀ : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P₀.productive, (P₀.chart z).keep = keep)

variable (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (hDref : Dref.filtration = D.filtration.gradedRefiltration W)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (markedMiddle : Fref.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (middle : ∀ z : (P₀.withKeep keep hkeep).productive,
      AllocatedExternalLocalCandidate ((P₀.withKeep keep hkeep).chart z) Dref Fref.filtration
        (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) markedMiddle)
    (sectionMap : M →ₗ[ℚ] L)
    (hSectionFilt : ∀ j, ∀ y ∈ Fmark.filtration.layer j, sectionMap y ∈ D.filtration.layer j)
    (c : Basis κ ℚ M)
    (leftMark rightMark : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (localLeft localRight : (P₀.withKeep keep hkeep).productive →
      (D.filtration.realification.adaptedPolynomialFiltration (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1)).Group)
    (localLeftMark localRightMark : (P₀.withKeep keep hkeep).productive →
      (Fmark.filtration.realification.adaptedPolynomialFiltration (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1)).Group)
    (hfactor : ∀ z : (P₀.withKeep keep hkeep).productive,
      (show (D.filtration.realification.adaptedPolynomialFiltration
          (fun _ : ((P₀.withKeep keep hkeep).chart z).Variables => 1)).Group from localLeft z) *
        (P₀.withKeep keep hkeep).refilteredLocalCoordinates A Fmark φ hφ W Dref hDref Fref
          markedMiddle middle z *
        (show (D.filtration.realification.adaptedPolynomialFiltration
          (fun _ : ((P₀.withKeep keep hkeep).chart z).Variables => 1)).Group from localRight z) =
      D.filtration.realification.polynomialOrbitCoordinates _ ((P₀.withKeep keep hkeep).candidate z).orbit)
    (hprojLeft : ∀ z, D.filtration.realPolynomialGroupMap Fmark.filtration φ hφ
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) (localLeft z) = localLeftMark z)
    (hprojRight : ∀ z, D.filtration.realPolynomialGroupMap Fmark.filtration φ hφ
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) (localRight z) = localRightMark z)
    (hleft : ∀ z : (P₀.withKeep keep hkeep).productive, ∀ u ∈ ((P₀.withKeep keep hkeep).chart z).slice.integerPoints,
      Fmark.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ))
        (localLeftMark z) =
      Fmark.filtration.realification.polynomialOrbitRealEval (fullTaggedVariableWeight (X := X) J)
        (fun i => (((P₀.withKeep keep hkeep).chart z).chartValues u i : ℝ)) leftMark)
    (hright : ∀ z : (P₀.withKeep keep hkeep).productive, ∀ u ∈ ((P₀.withKeep keep hkeep).chart z).slice.integerPoints,
      Fmark.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ))
        (localRightMark z) =
      Fmark.filtration.realification.polynomialOrbitRealEval (fullTaggedVariableWeight (X := X) J)
        (fun i => (((P₀.withKeep keep hkeep).chart z).chartValues u i : ℝ)) rightMark)
    (tests : (X → ℤ) → D.Niltest (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1))
    (htests : ∀ x, (tests x).observable = observable x)
    (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))

variable (hFref : Fref.filtration = Fmark.filtration.gradedRefiltration
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))
    {nQ nQF : ℕ}
    (Qquot : RationalFilteredNilmanifold
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)) s nQ)
    (hQquot : Qquot.filtration = Dref.filtration.quotientTop)
    (Fquot : RationalFilteredNilmanifold
      ((Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) ⧸
        Fref.filtration.layerIdeal (s + 1)) s nQF)
    (hFquot : Fquot.filtration = Fref.filtration.quotientTop)
    [PseudoMetricSpace Qquot.Space] [PseudoMetricSpace Fref.Space]
    (K : ℝ≥0)

include hQquot hDref hfactor hprojLeft hprojRight hleft hright htests hσ1 H hH hchart hsmall hp

theorem conclusion_of_uniform_dictionary_successor
    {l : ℕ} {slow Bweight Bobs Lip densityCost p budgetLog massLog : ℝ}
    (C : ℕ) (hp0 : 0 ≤ p) (hC : 2 ≤ C)
    (dictionary : RationalFilteredNilmanifold.ExternalMarkedAffineSliceFreezing.Dictionary
      (X := X → ℤ) D Fmark.filtration c φ hφ
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) sectionMap hSectionFilt l
      (fun i : { i : LayerSamplerVariables G I n B // keep i } => (A.sides i.val : ℝ)) slow (finiteFreezingInitialPrecision p) (Real.exp budgetLog))
    (hslowLeft : ∀ z, D.filtration.PolynomialSlowBound D.basis (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1)
      (fun i : { i : LayerSamplerVariables G I n B // keep i } => (A.sides i.val : ℝ)) slow (localLeft z))
    (hslowMark : ∀ z, Fmark.filtration.PolynomialSlowBound c (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1)
      (fun i : { i : LayerSamplerVariables G I n B // keep i } => (A.sides i.val : ℝ)) slow (localLeftMark z))
    (hrationalRight : ∀ z, D.filtration.PolynomialRationalGrid D.basis
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) l (localRight z))
    (hrationalMark : ∀ z, Fmark.filtration.PolynomialRationalGrid c
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) l (localRightMark z))
    (hdensity : ∀ z : (P₀.withKeep keep hkeep).productive,
      IsDenseCommonStrideBox
        (fun i : ((P₀.withKeep keep hkeep).chart z).Variables => A.sides i.val)
        densityCost ((P₀.withKeep keep hkeep).chart z).slice.integerPoints)
    (hfloor : ∀ i : { i : LayerSamplerVariables G I n B // keep i },
      Real.exp densityCost * max 2 (2 * (Real.exp budgetLog) * max 1 (Real.exp budgetLog)) ≤ (A.sides i.val : ℝ))
    (hBweight : 0 ≤ Bweight) (hBobs : 0 ≤ Bobs) (hLip : 0 ≤ Lip)
    (hweight : ∀ x, ‖weight x‖ ≤ Bweight)
    (hnorm : ∀ x, ((tests x).normBound : ℝ) ≤ Bobs)
    (hlip : ∀ x, ((tests x).lipBound : ℝ) ≤ Lip)
    (hweightCap : Bweight ≤ Real.exp p) (hobsCap : Bobs ≤ Real.exp p)
    (hlipCap : Lip ≤ Real.exp p) (hscoreInput : Real.exp (-p) ≤ scoreThreshold)
    (hcostInput : cost ≤ (p + C) ^ C) (hdensityInput : densityCost ≤ (p + C) ^ C)
    (hbudgetLog0 : 0 ≤ budgetLog) (hbudgetLog : budgetLog ≤ (p + C) ^ C)
    (hcount : (Fintype.card { i : LayerSamplerVariables G I n B // keep i } : ℝ) ≤ (p + C) ^ C)
    (hmassLog : massLog ≤ (p + C) ^ C) (hmassInput : Real.exp (-massLog) ≤ massThreshold)
    (hsection : Function.RightInverse sectionMap φ)
    (dw : Fin d → ℕ)
    (hdb : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ dw i}))
    (fw : κ → ℕ)
    (hfb : ∀ j, Fmark.filtration.layer j = Submodule.span ℚ (c '' {i | j ≤ fw i}))
    (hW : BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis dw hdb) dw W.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (hξ1 : ξ ≤ 1)
    (hrecovery : ∀ ij : (Fin d → Fin (dictionary.grid + 1)) × Fin dictionary.rightCount, ∀ x, x ∈ integerBox N → ∀ source,
      positiveImageSlice
        (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Qquot) K
        ((P₀.withKeep keep hkeep).refilteredFrozenObservable A Fmark φ W Dref (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt leftMark (dictionary.left ij.1)) (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt rightMark (dictionary.right ij.2)) x)
        (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Qquot source).2
        (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Qquot source).1 =
        (P₀.withKeep keep hkeep).refilteredFrozenObservable A Fmark φ W Dref (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt leftMark (dictionary.left ij.1)) (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt rightMark (dictionary.right ij.2)) x source)
    {outputCost outputMass outputScore : ℝ}
    (recurse : ∀ ij : (Fin d → Fin (dictionary.grid + 1)) × Fin dictionary.rightCount,
      ∀ lowerProblem : AllocatedExternalCandidateProblem (E := E) A Qquot Fquot.filtration
        (Dref.topQuotientMarkedMap Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) (D.refilteredMarkedMap_mem_layer Fmark φ hφ W Dref hDref Fref hFref)) (Fref.topQuotientOrbit Fquot hFquot markedMiddle)
        ((P₀.withKeep keep hkeep).refilteredQuotientObservable A Fmark φ hφ W Dref Fref Qquot (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt leftMark (dictionary.left ij.1)) (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt rightMark (dictionary.right ij.2)) markedMiddle K)
        weight (finiteFreezingRecursiveParameter C p) (Real.exp (-(finiteFreezingRecursiveParameter C p))) (Real.exp (-(finiteFreezingRecursiveParameter C p))),
        Nonempty (lowerProblem.Conclusion outputCost outputMass outputScore)) :
    Nonempty (P₀.Conclusion outputCost outputMass outputScore) := by
  obtain ⟨hcostRec, hmassRec, hscoreRec⟩ :=
    finiteFreezing_uniform_recursive_budget
      (Fintype.card { i : LayerSamplerVariables G I n B // keep i })
      hp0 hC hcostInput hdensityInput hbudgetLog0 hbudgetLog hcount hmassLog hmassInput
  have hsurplus := finiteFreezing_initial_score_surplus hp0 hBobs hLip
    hweightCap hobsCap hlipCap hscoreInput
  exact P₀.conclusion_of_dictionary_successor Fmark φ hφ keep hkeep W Dref hDref Fref
    markedMiddle middle sectionMap hSectionFilt c leftMark rightMark
    localLeft localRight localLeftMark localRightMark hfactor hprojLeft hprojRight
    hleft hright tests htests hσ1 H hH hchart hsmall hp
    hFref Qquot hQquot Fquot hFquot K
    dictionary hslowLeft hslowMark hrationalRight hrationalMark hdensity hfloor
    hBweight hBobs hLip (finiteFreezing_initial_precision_pos p).le hweight hnorm hlip
    (by positivity) (finiteFreezing_initial_discard_pos p) hsurplus
    hsection ((Real.exp_nonneg _).trans hmassInput)
    dw hdb fw hfb hW hsurj hξ1 hrecovery
    (finiteFreezingRecursiveParameter C p) hcostRec hmassRec hscoreRec recurse

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
