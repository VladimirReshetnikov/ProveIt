import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalLocalFiniteFreezing
import OAI.Combinatorics.Progressions.Sampling.AllocatedExternalCandidateNativeFrozenScore

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

    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
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
    (hσ1 : ∀ j, σ j ≤ 1) (H : Fin m → ℝ) (hH : ∀ j, 0 ≤ H j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ H j * ‖v‖)
    (hsmall : ∀ j, H j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))

omit [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] in
include hleft hright hσ1 H hH hchart hsmall hp in

theorem refilteredFrozenObservable_eq_localFrozen
    (z : P.productive) (u : (P.chart z).Variables → ℤ)
    (hu : u ∈ (P.chart z).slice.integerPoints) :
    P.refilteredFrozenObservable A Fmark φ W Dref
      (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt leftMark kE)
      (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt rightMark kR)
      ((P.chart z).physical u)
      (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u (middle z).orbit) =
    observable ((P.chart z).physical u) (QuotientGroup.mk
      (D.filtration.adaptedPolynomialRealValueHom (fun _ => 1) (fun i => (u i : ℝ))
        (D.filtration.frozenMarkedLeft Fmark.filtration (fun _ => 1) sectionMap hSectionFilt
            (localLeftMark z) kE *
          P.refilteredLocalCoordinates A Fmark φ hφ W Dref hDref Fref markedMiddle middle z *
          D.filtration.frozenMarkedRight Fmark.filtration (fun _ => 1) sectionMap hSectionFilt
            (localRightMark z) kR))) := by
  have hl := D.filtration.frozenMarkedLeftOrbit_realEval_eq_local Fmark.filtration (fullTaggedVariableWeight (X := X) J)
    sectionMap hSectionFilt leftMark kE (fun _ : (P.chart z).Variables => 1)
    (localLeftMark z) (fun i => (u i : ℝ))
    (fun i => ((P.chart z).chartValues u i : ℝ)) (hleft z u hu)
  have hr := D.filtration.frozenMarkedRightOrbit_realEval_eq_local Fmark.filtration (fullTaggedVariableWeight (X := X) J)
    sectionMap hSectionFilt rightMark kR (fun _ : (P.chart z).Variables => 1)
    (localRightMark z) (fun i => (u i : ℝ))
    (fun i => ((P.chart z).chartValues u i : ℝ)) (hright z u hu)
  simp only [polynomialOrbitRealEval_integer] at hl hr
  have htags := P.chartValues_eq_physicalIntegerPoint hσ1 H hH hchart hsmall hp z u hu
  unfold refilteredFrozenObservable
  rw [← htags, hl, hr]
  simp only [map_mul,
    P.refilteredLocalCoordinates_value A Fmark φ hφ W Dref hDref Fref markedMiddle middle]

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

namespace Refinement
variable {A Fmark φ P} {newCost newMass newScore : ℝ}
    (refinement : P.Refinement newCost newMass newScore)

noncomputable def refilteredMiddle : ∀ z : refinement.problem.productive,
    AllocatedExternalLocalCandidate (refinement.problem.chart z) Dref Fref.filtration (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W)
      markedMiddle := fun z =>
  (middle ⟨z.val, refinement.subset z.property⟩).refineSlice
    (refinement.step z) (refinement.step_pos z) (refinement.slice z) (refinement.dense z)
    (refinement.inside z)

end Refinement

variable {Index : Type*} [Fintype Index] [Nonempty Index]
    (sectionMap : M →ₗ[ℚ] L)
    (hSectionFilt : ∀ j, ∀ y ∈ Fmark.filtration.layer j, sectionMap y ∈ D.filtration.layer j)
    (leftMark rightMark : Fmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (leftCenter rightCenter : Index → D.RealGroup)

theorem exists_frozen_refinement_of_local_slices
    {newCost frozenThreshold Bweight ε : ℝ}
    (hcost : cost ≤ newCost) (hBweight : 0 ≤ Bweight) (hε : 0 ≤ ε)
    (step : P.productive → ℕ) (hstep : ∀ z, 0 < step z)
    (slice : ∀ z : P.productive,
      ResidueBoxSlice (fun i : (P.chart z).Variables => A.sides i.val) (step z))
    (hdense : ∀ z, IsDenseCommonStrideBox (fun i : (P.chart z).Variables => A.sides i.val)
      newCost (slice z).integerPoints)
    (hinside : ∀ z, (slice z).integerPoints ⊆ (P.chart z).slice.integerPoints)
    (label : P.productive → Index)
    (hweight : ∀ z, ∀ u ∈ (slice z).integerPoints, ‖weight ((P.chart z).physical u)‖ ≤ Bweight)
    (herror : ∀ z, ∀ u ∈ (slice z).integerPoints,
      ‖observable ((P.chart z).physical u) ((P.candidate z).value u) -
        P.refilteredFrozenObservable A Fmark φ W Dref
          (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt
            leftMark (leftCenter (label z)))
          (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt
            rightMark (rightCenter (label z)))
          ((P.chart z).physical u)
          (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u (middle z).orbit)‖ ≤ ε)
    (hfrozen : ∀ z, frozenThreshold ≤
      (𝔼 u ∈ (slice z).integerPoints, weight ((P.chart z).physical u) *
        P.refilteredFrozenObservable A Fmark φ W Dref
          (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt
            leftMark (leftCenter (label z)))
          (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt
            rightMark (rightCenter (label z)))
          ((P.chart z).physical u)
          (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u (middle z).orbit)).re) :
    ∃ chosen : Index,
      ∃ refinement : P.Refinement newCost
        (massThreshold / (Fintype.card Index : ℝ)) (frozenThreshold - Bweight * ε),
      ∀ z : refinement.problem.productive, frozenThreshold ≤
        refinement.problem.refilteredFrozenScore A Fmark φ hφ W Dref Fref
          (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt
            leftMark (leftCenter chosen))
          (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt
            rightMark (rightCenter chosen)) markedMiddle
          (refinement.refilteredMiddle hφ W Dref Fref markedMiddle middle) z := by
  have hscore (z : P.productive) : frozenThreshold - Bweight * ε ≤
      (𝔼 u ∈ (slice z).integerPoints, weight ((P.chart z).physical u) *
        observable ((P.chart z).physical u) ((P.candidate z).value u)).re := by
    have he := complex_expect_error_le (slice z).integerPoints
      (fun u => weight ((P.chart z).physical u) *
        observable ((P.chart z).physical u) ((P.candidate z).value u))
      (fun u => weight ((P.chart z).physical u) *
        P.refilteredFrozenObservable A Fmark φ W Dref
          (D.filtration.frozenMarkedLeftOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt
            leftMark (leftCenter (label z)))
          (D.filtration.frozenMarkedRightOrbit Fmark.filtration (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt
            rightMark (rightCenter (label z)))
          ((P.chart z).physical u)
          (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u (middle z).orbit))
      (mul_nonneg hBweight hε) (by
        intro u hu
        rw [← mul_sub, norm_mul]
        exact mul_le_mul (hweight z u hu) (herror z u hu) (norm_nonneg _) hBweight)
    have hre := (Complex.abs_re_le_norm _).trans he
    rw [Complex.sub_re] at hre
    have hlo := (abs_le.mp hre).1
    have hs := hfrozen z
    linarith
  let initial : P.Refinement newCost massThreshold (frozenThreshold - Bweight * ε) := {
    retained := P.productive
    subset := fun _ hz => hz
    mass := P.mass
    cost_le := hcost
    step := step
    step_pos := hstep
    slice := slice
    dense := hdense
    inside := hinside
    scoreLower := hscore }
  obtain ⟨chosen, paths, hpaths, hmass, hlabel⟩ := initial.exists_common_label label
  let refinement := initial.restrictPaths paths hpaths hmass
  refine ⟨chosen, refinement, ?_⟩
  intro z
  have hl : label ⟨z.val, hpaths z.property⟩ = chosen := hlabel z
  have hs := hfrozen ⟨z.val, hpaths z.property⟩
  rw [hl] at hs
  exact hs

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
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

include hDref hfactor hprojLeft hprojRight hleft hright htests hσ1 H hH hchart hsmall hp

theorem exists_finite_freezing_refinement
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
    (hbudget : frozenThreshold + Bweight * (Lip * ε) + (Bweight * Bobs) * θ < scoreThreshold) :
    ∃ grid Q modulus denominator rightCount : ℕ,
      0 < grid ∧ 0 < Q ∧ (Q : ℝ) ≤ max 1 budget ∧ 0 < modulus ∧
      0 < denominator ∧ 0 < rightCount ∧
      (Fintype.card (Fin d → Fin (grid + 1)) : ℝ) ≤ budget ∧
      (Fintype.card ({ i : LayerSamplerVariables G I n B // keep i } → Fin (Q + 1)) : ℝ) ≤ budget ∧
      (modulus : ℝ) ≤ budget ∧ (denominator : ℝ) ≤ budget ∧ (rightCount : ℝ) ≤ budget ∧
      (Fintype.card ((Fin d → Fin (grid + 1)) × Fin rightCount) : ℝ) ≤ budget ^ 2 ∧
      ∃ (left : (Fin d → Fin (grid + 1)) → D.RealGroup) (right : Fin rightCount → D.RealGroup),
        (∀ i, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ (left i) = 1 ∧
          ∀ k, |(D.basis.baseChange ℝ).repr (left i).coord k| ≤ budget) ∧
        (∀ j, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ (right j) = 1 ∧
          (∀ k, |(D.basis.baseChange ℝ).repr (right j).coord k| ≤ budget) ∧
          (D.basis.baseChange ℝ).equivFun (right j).coord ∈ realDenominatorGrid denominator) ∧
        ∃ chosen : (Fin d → Fin (grid + 1)) × Fin rightCount,
          ∃ refinement : (P₀.withKeep keep hkeep).Refinement
            (max cost (densityCost +
              Real.log ((4 * modulus * Q * (Fintype.card { i : LayerSamplerVariables G I n B // keep i } + 1 : ℝ)) / θ)))
            (massThreshold / (Fintype.card ((Fin d → Fin (grid + 1)) × Fin rightCount) : ℝ))
            (frozenThreshold - Bweight * (Lip * ε)),
          ∀ z : refinement.problem.productive, frozenThreshold ≤
            refinement.problem.refilteredFrozenScore A Fmark φ hφ W Dref Fref
              (D.filtration.frozenMarkedLeftOrbit Fmark.filtration
                (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt leftMark (left chosen.1))
              (D.filtration.frozenMarkedRightOrbit Fmark.filtration
                (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt rightMark (right chosen.2))
              markedMiddle (refinement.refilteredMiddle hφ W Dref Fref markedMiddle middle) z := by
  obtain ⟨grid, Q, modulus, denominator, rightCount, hgrid, hQ, hQbound, hmodulus,
    hdenominator, hrightCount, hgridCard, hcellCard, hmodulusBound,
    hdenominatorBound, hrightBound, hpair, left, right, hleftCenters, hrightCenters,
    hselect⟩ := hfreeze
  let : Nonempty (Fin rightCount) := ⟨⟨0, hrightCount⟩⟩
  have hlength (z : (P₀.withKeep keep hkeep).productive) (i : { i : LayerSamplerVariables G I n B // keep i }) :
      max 2 (2 * budget * max 1 budget) ≤ (((P₀.withKeep keep hkeep).chart z).slice.length i : ℝ) := by
    calc
      _ = Real.exp (-densityCost) *
          (Real.exp densityCost * max 2 (2 * budget * max 1 budget)) := by
        rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
      _ ≤ Real.exp (-densityCost) * (A.sides i.val : ℝ) :=
        mul_le_mul_of_nonneg_left (hfloor i) (Real.exp_nonneg _)
      _ ≤ _ := ((P₀.withKeep keep hkeep).chart z).slice.length_lower_of_dense ((P₀.withKeep keep hkeep).chart z).step_pos (hdensity z) i
  have htwo (z : (P₀.withKeep keep hkeep).productive) (i : { i : LayerSamplerVariables G I n B // keep i }) : 2 ≤ ((P₀.withKeep keep hkeep).chart z).slice.length i := by
    exact_mod_cast (le_max_left (2 : ℝ) _).trans (hlength z i)
  have hlong (z : (P₀.withKeep keep hkeep).productive) (i : { i : LayerSamplerVariables G I n B // keep i }) :
      2 * budget * max 1 budget ≤ (((P₀.withKeep keep hkeep).chart z).slice.length i : ℝ) :=
    (le_max_right (2 : ℝ) _).trans (hlength z i)
  have hlocal (z : (P₀.withKeep keep hkeep).productive) :=
    ((P₀.withKeep keep hkeep).chart z).finiteFreezing_of_selection ((P₀.withKeep keep hkeep).candidate z) sectionMap hSectionFilt
      (localLeftMark z) (localRightMark z)
      ((P₀.withKeep keep hkeep).refilteredLocalCoordinates A Fmark φ hφ W Dref hDref Fref markedMiddle middle z)
      Q modulus hQ hmodulus left right tests weight hQbound hmodulusBound
      (htwo z) (hlong z) (hdensity z) hθ (mul_nonneg hBweight (mul_nonneg hLip hε))
      (by simpa only [htests] using (P₀.withKeep keep hkeep).score z)
      (by
        intro hNp hparent hwidth hlarge hindexed
        obtain ⟨_, hselected⟩ := hselect (localLeft z) (localLeftMark z)
          (localRight z) (localRightMark z) (hslowLeft z) (hslowMark z)
          (hrationalRight z) (hrationalMark z) (hprojLeft z) (hprojRight z)
        exact hselected tests ((P₀.withKeep keep hkeep).chart z).physical (fun u => weight (((P₀.withKeep keep hkeep).chart z).physical u))
          Bweight Bobs Lip hBweight hBobs hLip (fun u _ => hweight _) hnorm hlip
          (((P₀.withKeep keep hkeep).chart z).freezingNativeOrbit ((P₀.withKeep keep hkeep).candidate z))
          ((P₀.withKeep keep hkeep).refilteredLocalCoordinates A Fmark φ hφ W Dref hDref Fref markedMiddle middle z)
          (hfactor z) ((P₀.withKeep keep hkeep).chart z).slice.length hNp
          (fun i => (((P₀.withKeep keep hkeep).chart z).slice.start i : ℤ)) ((P₀.withKeep keep hkeep).chart z).step
          hparent hwidth hlarge frozenThreshold θ scoreThreshold hthreshold hθ hindexed hbudget)
  choose slice hdense hinside ileft iright herror _hweighted hfrozen _hscore using hlocal
  have hvalue (z : (P₀.withKeep keep hkeep).productive) (i : Fin d → Fin (grid + 1)) (j : Fin rightCount)
      (u : ((P₀.withKeep keep hkeep).chart z).Variables → ℤ) (hu : u ∈ ((P₀.withKeep keep hkeep).chart z).slice.integerPoints) :
      ((P₀.withKeep keep hkeep).chart z).freezingFrozenValue sectionMap hSectionFilt
        (localLeftMark z) (localRightMark z)
        ((P₀.withKeep keep hkeep).refilteredLocalCoordinates A Fmark φ hφ W Dref hDref Fref markedMiddle middle z)
        tests (left i) (right j) u =
      (P₀.withKeep keep hkeep).refilteredFrozenObservable A Fmark φ W Dref
        (D.filtration.frozenMarkedLeftOrbit Fmark.filtration
          (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt leftMark (left i))
        (D.filtration.frozenMarkedRightOrbit Fmark.filtration
          (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt rightMark (right j))
        (((P₀.withKeep keep hkeep).chart z).physical u)
        (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u (middle z).orbit) := by
    symm
    simpa only [AllocatedExternalLocalChart.freezingFrozenValue,
      RationalFilteredNilmanifold.Niltest.markedFrozenValue, htests] using
      (P₀.withKeep keep hkeep).refilteredFrozenObservable_eq_localFrozen A Fmark φ hφ W Dref hDref Fref
        markedMiddle middle sectionMap hSectionFilt leftMark rightMark (left i) (right j)
        localLeftMark localRightMark hleft hright hσ1 H hH hchart hsmall hp z u hu
  obtain ⟨chosen, refinement, hscore⟩ :=
    (P₀.withKeep keep hkeep).exists_frozen_refinement_of_local_slices A Fmark φ hφ W Dref Fref markedMiddle middle
      sectionMap hSectionFilt leftMark rightMark
      (fun ij : (Fin d → Fin (grid + 1)) × Fin rightCount => left ij.1)
      (fun ij : (Fin d → Fin (grid + 1)) × Fin rightCount => right ij.2)
      (le_max_left cost _) hBweight (mul_nonneg hLip hε)
      (fun z => ((P₀.withKeep keep hkeep).chart z).step * modulus)
      (fun z => Nat.mul_pos ((P₀.withKeep keep hkeep).chart z).step_pos hmodulus)
      slice (fun z => (hdense z).mono (by
        exact le_max_right cost (densityCost +
          Real.log ((4 * modulus * Q *
            (Fintype.card { i : LayerSamplerVariables G I n B // keep i } + 1 : ℝ)) / θ)))) hinside
      (fun z => (ileft z, iright z))
      (fun z u _ => hweight (((P₀.withKeep keep hkeep).chart z).physical u))
      (by
        intro z u hu
        have he := herror z u hu
        rw [hvalue z (ileft z) (iright z) u (hinside z hu)] at he
        simpa only [htests] using he)
      (by
        intro z
        apply (hfrozen z).le.trans_eq
        apply congrArg Complex.re
        apply Finset.expect_congr rfl
        intro u hu
        rw [hvalue z (ileft z) (iright z) u (hinside z hu)])
  exact ⟨grid, Q, modulus, denominator, rightCount, hgrid, hQ, hQbound, hmodulus,
    hdenominator, hrightCount, hgridCard, hcellCard, hmodulusBound, hdenominatorBound,
    hrightBound, hpair, left, right, hleftCenters, hrightCenters, chosen, refinement, hscore⟩

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

namespace Refinement

variable {A Fmark φ P} {newCost newMass newScore : ℝ}
    (refinement : P.Refinement newCost newMass newScore)
    (left right : D.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))

theorem refiltered_mark_on_slice
    (hmarkFactor : ∀ z : P.productive, ∀ u ∈ (P.chart z).slice.integerPoints,
      realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ
        (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
            ((P.chart z).chartValues u) left *
          realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
            (hM := D.filtration.lowerCentralSeries_eq_bot)
            (D.filtration.gradedRefiltrationSubalgebra W).incl
            (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u (middle z).orbit) *
          D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
            ((P.chart z).chartValues u) right) =
        Fmark.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
          ((P.chart z).chartValues u) marked)
    (z : refinement.problem.productive) (u : (refinement.problem.chart z).Variables → ℤ)
    (hu : u ∈ (refinement.problem.chart z).slice.integerPoints) :
    realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := Fmark.filtration.lowerCentralSeries_eq_bot) φ
      (D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
          ((refinement.problem.chart z).chartValues u) left *
        realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
          (hM := D.filtration.lowerCentralSeries_eq_bot)
          (D.filtration.gradedRefiltrationSubalgebra W).incl
          (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u
            ((refinement.refilteredMiddle hφ W Dref Fref markedMiddle middle) z).orbit) *
        D.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
          ((refinement.problem.chart z).chartValues u) right) =
      Fmark.filtration.realification.polynomialOrbitEval (fullTaggedVariableWeight (X := X) J)
        ((refinement.problem.chart z).chartValues u) marked :=
  hmarkFactor ⟨z.val, refinement.subset z.property⟩ u (refinement.inside z hu)

end Refinement
end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
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

include hDref hfactor hprojLeft hprojRight hleft hright htests hσ1 H hH hchart hsmall hp

theorem exists_finite_freezing_refinement_of_dictionary
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
    (hbudget : frozenThreshold + Bweight * (Lip * ε) + (Bweight * Bobs) * θ < scoreThreshold) :
    ∃ chosen : (Fin d → Fin (dictionary.grid + 1)) × Fin dictionary.rightCount,
      ∃ refinement : (P₀.withKeep keep hkeep).Refinement
        (max cost (densityCost +
          Real.log ((4 * dictionary.modulus * dictionary.Q * (Fintype.card { i : LayerSamplerVariables G I n B // keep i } + 1 : ℝ)) / θ)))
        (massThreshold / (Fintype.card ((Fin d → Fin (dictionary.grid + 1)) × Fin dictionary.rightCount) : ℝ))
        (frozenThreshold - Bweight * (Lip * ε)),
      ∀ z : refinement.problem.productive, frozenThreshold ≤
        refinement.problem.refilteredFrozenScore A Fmark φ hφ W Dref Fref
          (D.filtration.frozenMarkedLeftOrbit Fmark.filtration
            (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt leftMark (dictionary.left chosen.1))
          (D.filtration.frozenMarkedRightOrbit Fmark.filtration
            (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt rightMark (dictionary.right chosen.2))
          markedMiddle (refinement.refilteredMiddle hφ W Dref Fref markedMiddle middle) z := by
  let grid := dictionary.grid
  let Q := dictionary.Q
  let modulus := dictionary.modulus
  let rightCount := dictionary.rightCount
  let left := dictionary.left
  let right := dictionary.right
  have hQ := dictionary.Q_pos
  have hQbound := dictionary.Q_bound
  have hmodulus := dictionary.modulus_pos
  have hrightCount := dictionary.rightCount_pos
  have hmodulusBound := dictionary.modulus_bound
  have hselect := dictionary.select
  let : Nonempty (Fin rightCount) := ⟨⟨0, hrightCount⟩⟩
  have hlength (z : (P₀.withKeep keep hkeep).productive) (i : { i : LayerSamplerVariables G I n B // keep i }) :
      max 2 (2 * budget * max 1 budget) ≤ (((P₀.withKeep keep hkeep).chart z).slice.length i : ℝ) := by
    calc
      _ = Real.exp (-densityCost) *
          (Real.exp densityCost * max 2 (2 * budget * max 1 budget)) := by
        rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
      _ ≤ Real.exp (-densityCost) * (A.sides i.val : ℝ) :=
        mul_le_mul_of_nonneg_left (hfloor i) (Real.exp_nonneg _)
      _ ≤ _ := ((P₀.withKeep keep hkeep).chart z).slice.length_lower_of_dense ((P₀.withKeep keep hkeep).chart z).step_pos (hdensity z) i
  have htwo (z : (P₀.withKeep keep hkeep).productive) (i : { i : LayerSamplerVariables G I n B // keep i }) : 2 ≤ ((P₀.withKeep keep hkeep).chart z).slice.length i := by
    exact_mod_cast (le_max_left (2 : ℝ) _).trans (hlength z i)
  have hlong (z : (P₀.withKeep keep hkeep).productive) (i : { i : LayerSamplerVariables G I n B // keep i }) :
      2 * budget * max 1 budget ≤ (((P₀.withKeep keep hkeep).chart z).slice.length i : ℝ) :=
    (le_max_right (2 : ℝ) _).trans (hlength z i)
  have hlocal (z : (P₀.withKeep keep hkeep).productive) :=
    ((P₀.withKeep keep hkeep).chart z).finiteFreezing_of_selection ((P₀.withKeep keep hkeep).candidate z) sectionMap hSectionFilt
      (localLeftMark z) (localRightMark z)
      ((P₀.withKeep keep hkeep).refilteredLocalCoordinates A Fmark φ hφ W Dref hDref Fref markedMiddle middle z)
      Q modulus hQ hmodulus left right tests weight hQbound hmodulusBound
      (htwo z) (hlong z) (hdensity z) hθ (mul_nonneg hBweight (mul_nonneg hLip hε))
      (by simpa only [htests] using (P₀.withKeep keep hkeep).score z)
      (by
        intro hNp hparent hwidth hlarge hindexed
        obtain ⟨_, hselected⟩ := hselect (localLeft z) (localLeftMark z)
          (localRight z) (localRightMark z) (hslowLeft z) (hslowMark z)
          (hrationalRight z) (hrationalMark z) (hprojLeft z) (hprojRight z)
        exact hselected tests ((P₀.withKeep keep hkeep).chart z).physical (fun u => weight (((P₀.withKeep keep hkeep).chart z).physical u))
          Bweight Bobs Lip hBweight hBobs hLip (fun u _ => hweight _) hnorm hlip
          (((P₀.withKeep keep hkeep).chart z).freezingNativeOrbit ((P₀.withKeep keep hkeep).candidate z))
          ((P₀.withKeep keep hkeep).refilteredLocalCoordinates A Fmark φ hφ W Dref hDref Fref markedMiddle middle z)
          (hfactor z) ((P₀.withKeep keep hkeep).chart z).slice.length hNp
          (fun i => (((P₀.withKeep keep hkeep).chart z).slice.start i : ℤ)) ((P₀.withKeep keep hkeep).chart z).step
          hparent hwidth hlarge frozenThreshold θ scoreThreshold hthreshold hθ hindexed hbudget)
  choose slice hdense hinside ileft iright herror _hweighted hfrozen _hscore using hlocal
  have hvalue (z : (P₀.withKeep keep hkeep).productive) (i : Fin d → Fin (grid + 1)) (j : Fin rightCount)
      (u : ((P₀.withKeep keep hkeep).chart z).Variables → ℤ) (hu : u ∈ ((P₀.withKeep keep hkeep).chart z).slice.integerPoints) :
      ((P₀.withKeep keep hkeep).chart z).freezingFrozenValue sectionMap hSectionFilt
        (localLeftMark z) (localRightMark z)
        ((P₀.withKeep keep hkeep).refilteredLocalCoordinates A Fmark φ hφ W Dref hDref Fref markedMiddle middle z)
        tests (left i) (right j) u =
      (P₀.withKeep keep hkeep).refilteredFrozenObservable A Fmark φ W Dref
        (D.filtration.frozenMarkedLeftOrbit Fmark.filtration
          (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt leftMark (left i))
        (D.filtration.frozenMarkedRightOrbit Fmark.filtration
          (fullTaggedVariableWeight (X := X) J) sectionMap hSectionFilt rightMark (right j))
        (((P₀.withKeep keep hkeep).chart z).physical u)
        (Dref.filtration.realification.polynomialOrbitEval (fun _ => 1) u (middle z).orbit) := by
    symm
    simpa only [AllocatedExternalLocalChart.freezingFrozenValue,
      RationalFilteredNilmanifold.Niltest.markedFrozenValue, htests] using
      (P₀.withKeep keep hkeep).refilteredFrozenObservable_eq_localFrozen A Fmark φ hφ W Dref hDref Fref
        markedMiddle middle sectionMap hSectionFilt leftMark rightMark (left i) (right j)
        localLeftMark localRightMark hleft hright hσ1 H hH hchart hsmall hp z u hu
  obtain ⟨chosen, refinement, hscore⟩ :=
    (P₀.withKeep keep hkeep).exists_frozen_refinement_of_local_slices A Fmark φ hφ W Dref Fref markedMiddle middle
      sectionMap hSectionFilt leftMark rightMark
      (fun ij : (Fin d → Fin (grid + 1)) × Fin rightCount => left ij.1)
      (fun ij : (Fin d → Fin (grid + 1)) × Fin rightCount => right ij.2)
      (le_max_left cost _) hBweight (mul_nonneg hLip hε)
      (fun z => ((P₀.withKeep keep hkeep).chart z).step * modulus)
      (fun z => Nat.mul_pos ((P₀.withKeep keep hkeep).chart z).step_pos hmodulus)
      slice (fun z => (hdense z).mono (by
        exact le_max_right cost (densityCost +
          Real.log ((4 * modulus * Q *
            (Fintype.card { i : LayerSamplerVariables G I n B // keep i } + 1 : ℝ)) / θ)))) hinside
      (fun z => (ileft z, iright z))
      (fun z u _ => hweight (((P₀.withKeep keep hkeep).chart z).physical u))
      (by
        intro z u hu
        have he := herror z u hu
        rw [hvalue z (ileft z) (iright z) u (hinside z hu)] at he
        simpa only [htests] using he)
      (by
        intro z
        apply (hfrozen z).le.trans_eq
        apply congrArg Complex.re
        apply Finset.expect_congr rfl
        intro u hu
        rw [hvalue z (ileft z) (iright z) u (hinside z hu)])
  exact ⟨chosen, refinement, hscore⟩

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
