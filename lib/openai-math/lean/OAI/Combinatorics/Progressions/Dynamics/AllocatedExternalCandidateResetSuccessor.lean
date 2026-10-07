import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateUniformSuccessor
import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalLocalGlobalMarkedCandidate
import OAI.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateNativeMiddleCoordinates
import OAI.Combinatorics.Progressions.Geometry.AllocatedExternalLocalChartOrbitValues

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realChartSubstitute realPolynomialGroupMap associatedGradedMap gradedRefiltrationMap

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
    {L M κ : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d f : ℕ} {D : RationalFilteredNilmanifold L (s + 1) d}
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    {marked : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P.productive, (P.chart z).keep = keep)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    {c : Basis κ ℚ M} {ν : κ → ℕ}
    {hF : ∀ j, Fmark.filtration.layer j = span ℚ (c '' {i | j ≤ ν i})}
    {g : (Fmark.filtration.realification.adaptedPolynomialFiltration
      (fullTaggedVariableWeight (X := X) J)).Group}
    {EF RF : Fmark.filtration.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
    (factors : GlobalMarkedNativeFactors Fmark.filtration c ν hF (fullTaggedVariableWeight J)
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)) g EF RF)
    (slow : ℝ) (denominator : ℕ)

structure AllocatedExternalGlobalNativeResetFamily where
  localLeft : (P.withKeep keep hkeep).productive →
    (D.filtration.realification.adaptedPolynomialFiltration (fun _ : {i // keep i} => 1)).Group
  localMiddle : (P.withKeep keep hkeep).productive →
    (D.filtration.realification.adaptedPolynomialFiltration (fun _ : {i // keep i} => 1)).Group
  localRight : (P.withKeep keep hkeep).productive →
    (D.filtration.realification.adaptedPolynomialFiltration (fun _ : {i // keep i} => 1)).Group
  native : (P.withKeep keep hkeep).productive →
    (D.filtration.gradedRefiltration W).realification.PolynomialOrbit (fun _ : {i // keep i} => 1)
  source_factor : ∀ z, localLeft z * localMiddle z * localRight z =
    D.filtration.realification.polynomialOrbitCoordinates _ ((P.withKeep keep hkeep).candidate z).orbit
  projection_left : ∀ z, D.filtration.realPolynomialGroupMap Fmark.filtration φ hφ
    (fun _ : {i // keep i} => 1) (localLeft z) =
    Fmark.filtration.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
      (fun _ : {i // keep i} => 1)
      (integerSampledRealChart ((P.withKeep keep hkeep).chart z).integerChart)
      ((P.withKeep keep hkeep).chart z).integerChart_support factors.left
  projection_middle : ∀ z, D.filtration.realPolynomialGroupMap Fmark.filtration φ hφ
    (fun _ : {i // keep i} => 1) (localMiddle z) =
    Fmark.filtration.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
      (fun _ : {i // keep i} => 1)
      (integerSampledRealChart ((P.withKeep keep hkeep).chart z).integerChart)
      ((P.withKeep keep hkeep).chart z).integerChart_support factors.middle
  projection_right : ∀ z, D.filtration.realPolynomialGroupMap Fmark.filtration φ hφ
    (fun _ : {i // keep i} => 1) (localRight z) =
    Fmark.filtration.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
      (fun _ : {i // keep i} => 1)
      (integerSampledRealChart ((P.withKeep keep hkeep).chart z).integerChart)
      ((P.withKeep keep hkeep).chart z).integerChart_support factors.right
  slow_left : ∀ z, D.filtration.PolynomialSlowBound D.basis
    (fun _ : {i // keep i} => 1) (fun i => (A.sides i.val : ℝ)) slow (localLeft z)
  grid_right : ∀ z, D.filtration.PolynomialRationalGrid D.basis
    (fun _ : {i // keep i} => 1) denominator (localRight z)
  native_log : ∀ z, map
    (realLieHomToRat (realificationLieHom
      (D.filtration.gradedRefiltrationSubalgebra W).incl)).toLinearMap (native z).log =
    ((localMiddle z).coord : VectorPolynomial {i // keep i} ℚ (ℝ ⊗[ℚ] L))

namespace AllocatedExternalGlobalNativeResetFamily

variable {Fmark φ hφ P keep hkeep W factors slow denominator}

noncomputable def leftMark
    (_reset : AllocatedExternalGlobalNativeResetFamily Fmark φ hφ P keep hkeep W factors slow denominator) :
    Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J) :=
  (Fmark.filtration.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J)).symm factors.left

noncomputable def rightMark
    (_reset : AllocatedExternalGlobalNativeResetFamily Fmark φ hφ P keep hkeep W factors slow denominator) :
    Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J) :=
  (Fmark.filtration.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J)).symm factors.right

variable (reset : AllocatedExternalGlobalNativeResetFamily
    Fmark φ hφ P keep hkeep W factors slow denominator)

theorem left_mark_values (z : (P.withKeep keep hkeep).productive) (u : {i // keep i} → ℤ) :
    Fmark.filtration.adaptedPolynomialRealValueHom (fun _ : {i // keep i} => 1)
      (fun i => (u i : ℝ))
      (Fmark.filtration.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
        (fun _ : {i // keep i} => 1)
        (integerSampledRealChart ((P.withKeep keep hkeep).chart z).integerChart)
        ((P.withKeep keep hkeep).chart z).integerChart_support factors.left) =
      Fmark.filtration.realification.polynomialOrbitRealEval (fullTaggedVariableWeight J)
        (fun i => (((P.withKeep keep hkeep).chart z).chartValues u i : ℝ)) reset.leftMark :=
  ((P.withKeep keep hkeep).chart z).globalOrbit_chart_values Fmark.filtration factors.left u

theorem right_mark_values (z : (P.withKeep keep hkeep).productive) (u : {i // keep i} → ℤ) :
    Fmark.filtration.adaptedPolynomialRealValueHom (fun _ : {i // keep i} => 1)
      (fun i => (u i : ℝ))
      (Fmark.filtration.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
        (fun _ : {i // keep i} => 1)
        (integerSampledRealChart ((P.withKeep keep hkeep).chart z).integerChart)
        ((P.withKeep keep hkeep).chart z).integerChart_support factors.right) =
      Fmark.filtration.realification.polynomialOrbitRealEval (fullTaggedVariableWeight J)
        (fun i => (((P.withKeep keep hkeep).chart z).chartValues u i : ℝ)) reset.rightMark :=
  ((P.withKeep keep hkeep).chart z).globalOrbit_chart_values Fmark.filtration factors.right u

variable {nD nF : ℕ}
    (Dref : RationalFilteredNilmanifold
      (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
    (hDref : Dref.filtration = D.filtration.gradedRefiltration W)
    (Fref : RationalFilteredNilmanifold
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
    (hFref : Fref.filtration = Fmark.filtration.gradedRefiltration
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))

noncomputable def candidate (z : (P.withKeep keep hkeep).productive) :
    AllocatedExternalLocalCandidate ((P.withKeep keep hkeep).chart z) Dref Fref.filtration
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W)
      (factors.markedMiddleOn Fref hFref) :=
  AllocatedExternalLocalCandidate.ofGlobalMarkedNativeMiddle
    ((P.withKeep keep hkeep).chart z) D Fmark φ hφ W Dref hDref Fref hFref factors
    (reset.localMiddle z) (reset.native z) (reset.projection_middle z) (reset.native_log z)

@[simp] theorem candidate_orbit_log (z : (P.withKeep keep hkeep).productive) :
    (reset.candidate Dref hDref Fref hFref z).orbit.log = (reset.native z).log := rfl

theorem candidate_included_log (z : (P.withKeep keep hkeep).productive) :
    map (realLieHomToRat (realificationLieHom
      (D.filtration.gradedRefiltrationSubalgebra W).incl)).toLinearMap
      (reset.candidate Dref hDref Fref hFref z).orbit.log =
      ((reset.localMiddle z).coord : VectorPolynomial {i // keep i} ℚ (ℝ ⊗[ℚ] L)) :=
  reset.native_log z

theorem candidate_factor (z : (P.withKeep keep hkeep).productive) :
    (show (D.filtration.realification.adaptedPolynomialFiltration
        (fun _ : ((P.withKeep keep hkeep).chart z).Variables => 1)).Group from reset.localLeft z) *
      (P.withKeep keep hkeep).refilteredLocalCoordinates A Fmark φ hφ W Dref hDref Fref
        (factors.markedMiddleOn Fref hFref) (reset.candidate Dref hDref Fref hFref) z *
      (show (D.filtration.realification.adaptedPolynomialFiltration
        (fun _ : ((P.withKeep keep hkeep).chart z).Variables => 1)).Group from reset.localRight z) =
      D.filtration.realification.polynomialOrbitCoordinates _
        ((P.withKeep keep hkeep).candidate z).orbit := by
  exact (P.withKeep keep hkeep).refilteredLocalCoordinates_factor_of_log A Fmark φ hφ W
    Dref hDref Fref (factors.markedMiddleOn Fref hFref)
    (reset.candidate Dref hDref Fref hFref) reset.localLeft reset.localMiddle reset.localRight
    (reset.candidate_included_log Dref hDref Fref hFref) reset.source_factor z

end AllocatedExternalGlobalNativeResetFamily
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realChartSubstitute realPolynomialGroupMap associatedGradedMap gradedRefiltrationMap
  PolynomialRationalGrid PolynomialSlowBound

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
    (hFref : Fref.filtration = Fmark.filtration.gradedRefiltration
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))
    (sectionMap : M →ₗ[ℚ] L)
    (hSectionFilt : ∀ j, ∀ y ∈ Fmark.filtration.layer j, sectionMap y ∈ D.filtration.layer j)
    (c : Basis κ ℚ M)
    (ν : κ → ℕ)
    (hF : ∀ j, Fmark.filtration.layer j = span ℚ (c '' {i | j ≤ ν i}))
    {g : (Fmark.filtration.realification.adaptedPolynomialFiltration
      (fullTaggedVariableWeight (X := X) J)).Group}
    {EF RF : Fmark.filtration.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
    (factors : GlobalMarkedNativeFactors Fmark.filtration c ν hF (fullTaggedVariableWeight J)
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)) g EF RF)
    {slow : ℝ} {denominator : ℕ}
    (reset : AllocatedExternalGlobalNativeResetFamily
      Fmark φ hφ P₀ keep hkeep W factors slow denominator)
    (tests : (X → ℤ) → D.Niltest (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1))
    (htests : ∀ x, (tests x).observable = observable x)
    (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))

variable    {nQ nQF : ℕ}
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

include hQquot hDref htests hσ1 H hH hchart hsmall hp

theorem conclusion_of_globalNativeReset_dictionary_successor
    {Bweight Bobs Lip densityCost p budgetLog massLog : ℝ}
    (C : ℕ) (hp0 : 0 ≤ p) (hC : 2 ≤ C)
    (dictionary : RationalFilteredNilmanifold.ExternalMarkedAffineSliceFreezing.Dictionary
      (X := X → ℤ) D Fmark.filtration c φ hφ
      (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1) sectionMap hSectionFilt denominator
      (fun i : { i : LayerSamplerVariables G I n B // keep i } => (A.sides i.val : ℝ)) slow (finiteFreezingInitialPrecision p) (Real.exp budgetLog))
    (hslowMark : ∀ z, Fmark.filtration.PolynomialSlowBound c (fun _ : { i : LayerSamplerVariables G I n B // keep i } => 1)
      (fun i : { i : LayerSamplerVariables G I n B // keep i } => (A.sides i.val : ℝ)) slow (Fmark.filtration.weightedAdaptedRealChartHom (fullTaggedVariableWeight J) (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1) (integerSampledRealChart ((P₀.withKeep keep hkeep).chart z).integerChart) ((P₀.withKeep keep hkeep).chart z).integerChart_support factors.left))
    (hgrid : Fmark.filtration.PolynomialRationalGrid c
      (fullTaggedVariableWeight (X := X) J) denominator factors.right)
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
    (hW : BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis dw hdb) dw W.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (hξ1 : ξ ≤ 1)
    (hrecovery : ∀ ij : (Fin d → Fin (dictionary.grid + 1)) × Fin dictionary.rightCount, ∀ x, x ∈ integerBox N → ∀ source,
      positiveImageSlice
        (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Qquot) K
        ((P₀.withKeep keep hkeep).refilteredFrozenObservable A Fmark φ W Dref (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt reset.leftMark (dictionary.left ij.1)) (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt reset.rightMark (dictionary.right ij.2)) x)
        (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Qquot source).2
        (Dref.markedTopQuotientDiagram Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Qquot source).1 =
        (P₀.withKeep keep hkeep).refilteredFrozenObservable A Fmark φ W Dref (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt reset.leftMark (dictionary.left ij.1)) (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt reset.rightMark (dictionary.right ij.2)) x source)
    {outputCost outputMass outputScore : ℝ}
    (recurse : ∀ ij : (Fin d → Fin (dictionary.grid + 1)) × Fin dictionary.rightCount,
      ∀ lowerProblem : AllocatedExternalCandidateProblem (E := E) A Qquot Fquot.filtration
        (Dref.topQuotientMarkedMap Fref (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) (D.refilteredMarkedMap_mem_layer Fmark φ hφ W Dref hDref Fref hFref)) (Fref.topQuotientOrbit Fquot hFquot (factors.markedMiddleOn Fref hFref))
        ((P₀.withKeep keep hkeep).refilteredQuotientObservable A Fmark φ hφ W Dref Fref Qquot (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt reset.leftMark (dictionary.left ij.1)) (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt reset.rightMark (dictionary.right ij.2)) (factors.markedMiddleOn Fref hFref) K)
        weight (finiteFreezingRecursiveParameter C p) (Real.exp (-(finiteFreezingRecursiveParameter C p))) (Real.exp (-(finiteFreezingRecursiveParameter C p))),
        Nonempty (lowerProblem.Conclusion outputCost outputMass outputScore)) :
    Nonempty (P₀.Conclusion outputCost outputMass outputScore) := by
  let localLeftMark (z : (P₀.withKeep keep hkeep).productive) :=
    Fmark.filtration.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
      (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)
      (integerSampledRealChart ((P₀.withKeep keep hkeep).chart z).integerChart)
      ((P₀.withKeep keep hkeep).chart z).integerChart_support factors.left
  let localRightMark (z : (P₀.withKeep keep hkeep).productive) :=
    Fmark.filtration.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
      (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)
      (integerSampledRealChart ((P₀.withKeep keep hkeep).chart z).integerChart)
      ((P₀.withKeep keep hkeep).chart z).integerChart_support factors.right
  have hrightGrid (z : (P₀.withKeep keep hkeep).productive) :
      Fmark.filtration.PolynomialRationalGrid c
        (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)
        denominator (localRightMark z) :=
    Fmark.filtration.polynomialRationalGrid_integerChart c
      (fullTaggedVariableWeight J) (fun _ => 1)
      ((P₀.withKeep keep hkeep).chart z).integerChart
      ((P₀.withKeep keep hkeep).chart z).integerChart_support
      denominator factors.right hgrid
  exact P₀.conclusion_of_uniform_dictionary_successor Fmark φ hφ keep hkeep W Dref hDref Fref
    (factors.markedMiddleOn Fref hFref) (reset.candidate Dref hDref Fref hFref)
    sectionMap hSectionFilt c reset.leftMark reset.rightMark reset.localLeft reset.localRight
    localLeftMark localRightMark (reset.candidate_factor Dref hDref Fref hFref)
    reset.projection_left reset.projection_right
    (fun z u _ => reset.left_mark_values z u) (fun z u _ => reset.right_mark_values z u)
    tests htests hσ1 H hH hchart hsmall hp hFref Qquot hQquot Fquot hFquot K
    C hp0 hC dictionary reset.slow_left hslowMark reset.grid_right hrightGrid
    hdensity hfloor hBweight hBobs hLip hweight hnorm hlip hweightCap hobsCap hlipCap hscoreInput
    hcostInput hdensityInput hbudgetLog0 hbudgetLog hcount hmassLog hmassInput
    hsection dw hdb ν hF hW hsurj hξ1 hrecovery recurse

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
