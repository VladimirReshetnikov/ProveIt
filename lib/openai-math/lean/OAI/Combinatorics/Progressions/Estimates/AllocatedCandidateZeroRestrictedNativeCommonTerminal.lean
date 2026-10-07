import OAI.Combinatorics.Progressions.Estimates.AllocatedCandidateGeneratedFastTerminal

namespace OAI

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

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom

namespace AllocatedExternalLocalChart

variable {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)

theorem hasCommonRefilteredOrbitFactors_axisPolynomial_of_zero_restriction
    (keep initialLong : LayerSamplerVariables G I n B → Prop)
    (hsub : ∀ i, keep i → initialLong i)
    {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] {s : ℕ}
    (F : NilpotentLieFiltration L s) (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (bD '' {i | j ≤ ω i}))
    (fixed : {i : C.Variables // ¬keep i.val} → ℤ)
    (q : ℝ) (l : ℕ) (W : LieSubalgebra ℚ F.AssociatedGraded)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : C.Variables => 1)).Group)
    (h : F.HasCommonRefilteredOrbitFactors bD ω hF
      (fun i : {i // initialLong i} => (A.sides i.val : ℝ)) q l W
      (F.weightedAdaptedRealChartHom (fun _ : C.Variables => 1)
        (fun _ : {i // initialLong i} => 1) (C.axisPolynomial initialLong (fun _ => 0))
        (C.axisPolynomial_support initialLong (fun _ => 0)) g)) :
    F.HasCommonRefilteredOrbitFactors bD ω hF
      (fun i : {i // keep i} => (A.sides i.val : ℝ)) q l W
      (F.weightedAdaptedRealChartHom (fun _ : C.Variables => 1)
        (fun _ : {i // keep i} => 1) (C.axisPolynomial keep fixed)
        (C.axisPolynomial_support keep fixed) g) := by
  let pureLong := F.weightedAdaptedRealChartHom (fun _ : C.Variables => 1)
    (fun _ : {i // initialLong i} => 1) (C.axisPolynomial initialLong (fun _ => 0))
    (C.axisPolynomial_support initialLong (fun _ => 0)) g
  have hpure := HasCommonRefilteredOrbitFactors.nested_freeze F bD ω hF
    initialLong keep hsub 0 (fun i => (A.sides i : ℝ)) q l W pureLong h
  apply HasCommonRefilteredOrbitFactors.of_symbol_eq F bD ω hF
    (fun i : {i // keep i} => (A.sides i.val : ℝ)) q l W _ _ hpure
  have haxis : C.axisPolynomial keep fixed =
      nestedFrozenCoordinate C.keep keep (fun i => (fixed i : ℝ)) := rfl
  have hzero : C.axisPolynomial initialLong (fun _ => 0) =
      nestedFrozenCoordinate C.keep initialLong 0 := by
    funext i
    simp only [axisPolynomial, nestedFrozenCoordinate, Pi.zero_apply, Int.cast_zero]
  have hactual : F.weightedAdaptedRealChartHom (fun _ : C.Variables => 1)
      (fun _ : {i // keep i} => 1) (C.axisPolynomial keep fixed)
      (C.axisPolynomial_support keep fixed) g =
      F.weightedAdaptedRealChartHom (fun _ : C.Variables => 1)
        (fun _ : {i // keep i} => 1)
        (nestedFrozenCoordinate C.keep keep (fun i => (fixed i : ℝ)))
        (nestedFrozenCoordinate_support C.keep keep (fun i => (fixed i : ℝ))) g := by
    apply NilpotentLieBCHGroup.ext
    apply Subtype.ext
    simp only [weightedAdaptedRealChartHom_coord]
    rw [haxis]
  have hlong : pureLong =
      F.weightedAdaptedRealChartHom (fun _ : C.Variables => 1)
        (fun _ : {i // initialLong i} => 1)
        (nestedFrozenCoordinate C.keep initialLong 0)
        (nestedFrozenCoordinate_support C.keep initialLong 0) g := by
    dsimp only [pureLong]
    apply NilpotentLieBCHGroup.ext
    apply Subtype.ext
    simp only [weightedAdaptedRealChartHom_coord]
    rw [hzero]
  rw [hactual, hlong]
  exact F.realPolynomialSymbolHom_nested_nested_frozenCoordinate bD ω hF
    C.keep initialLong keep hsub (fun i => (fixed i : ℝ)) g

end AllocatedExternalLocalChart

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}

namespace AllocatedExternalLocalCandidate

variable {cost shortCost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ i, keep i → C.keep i)
    (fixed : {i : C.Variables // ¬keep i.val} → ℤ)
    (hfixed : ∀ i, fixed i ∈ integerProgressionSupport
      (C.slice.start i.val : ℤ) C.step (C.slice.length i.val))

theorem hasCommonRefilteredOrbitFactors_freezeAxes_of_zero_restriction
    (initialLong : LayerSamplerVariables G I n B → Prop)
    (hsub : ∀ i, keep i → initialLong i)
    {ι : Type*} [Fintype ι] (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = Submodule.span ℚ (bD '' {i | j ≤ ω i}))
    (q : ℝ) (l : ℕ) (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (h : D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : {i // initialLong i} => (A.sides i.val : ℝ)) q l W
      (D.filtration.weightedAdaptedRealChartHom (fun _ : C.Variables => 1)
        (fun _ : {i // initialLong i} => 1) (C.axisPolynomial initialLong (fun _ => 0))
        (C.axisPolynomial_support initialLong (fun _ => 0))
        (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1) candidate.orbit))) :
    D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : {i // keep i} => (A.sides i.val : ℝ)) q l W
      (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
        (candidate.freezeAxes (shortCost := shortCost) keep hkeep fixed hfixed).orbit) := by
  change D.filtration.HasCommonRefilteredOrbitFactors bD ω hD _ q l W
    (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
      (D.filtration.polynomialOrbitRealChart (fun _ => 1) (fun _ => 1)
        (C.axisPolynomial keep fixed) (C.axisPolynomial_support keep fixed) candidate.orbit))
  rw [D.filtration.polynomialOrbitRealChart_polynomialCoordinates]
  exact C.hasCommonRefilteredOrbitFactors_axisPolynomial_of_zero_restriction keep initialLong hsub
    D.filtration bD ω hD fixed q l W _ h

end AllocatedExternalLocalCandidate

namespace AllocatedExternalCandidateProblem.AxisFreezing

variable {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}
    {cost massThreshold scoreThreshold : ℝ}
    {P : AllocatedExternalCandidateProblem (E := E) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {keep : P.productive → LayerSamplerVariables G I n B → Prop}
    {shortCost : ℝ} (freezing : P.AxisFreezing keep shortCost)

theorem problem_nativeFactors_of_zero_restriction
    (initialLong : LayerSamplerVariables G I n B → Prop)
    (hstageLong : ∀ z i, keep z i → initialLong i)
    {ι : Type*} [Fintype ι] (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = Submodule.span ℚ (bD '' {i | j ≤ ω i}))
    (q : ℝ) (l : ℕ) (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (z : P.productive)
    (h : D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : {i // initialLong i} => (A.sides i.val : ℝ)) q l W
      (D.filtration.weightedAdaptedRealChartHom (fun _ : (P.chart z).Variables => 1)
        (fun _ : {i // initialLong i} => 1) ((P.chart z).axisPolynomial initialLong (fun _ => 0))
        ((P.chart z).axisPolynomial_support initialLong (fun _ => 0))
        (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1) (P.candidate z).orbit))) :
    D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : (freezing.problem.chart z).Variables => (A.sides i.val : ℝ)) q l W
      (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
        (freezing.problem.candidate z).orbit) :=
  (P.candidate z).hasCommonRefilteredOrbitFactors_freezeAxes_of_zero_restriction
    (shortCost := shortCost) (keep z) (freezing.keep_subset z) (freezing.fixed z)
    (freezing.fixed_mem z) initialLong (hstageLong z) bD ω hD q l W h

theorem withKeep_nativeFactors_of_zero_restriction
    (commonKeep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : freezing.problem.productive,
      (freezing.problem.chart z).keep = commonKeep)
    (initialLong : LayerSamplerVariables G I n B → Prop)
    (hstageLong : ∀ z i, keep z i → initialLong i)
    {ι : Type*} [Fintype ι] (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = Submodule.span ℚ (bD '' {i | j ≤ ω i}))
    (q : ℝ) (l : ℕ) (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (z : P.productive)
    (h : D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : {i // initialLong i} => (A.sides i.val : ℝ)) q l W
      (D.filtration.weightedAdaptedRealChartHom (fun _ : (P.chart z).Variables => 1)
        (fun _ : {i // initialLong i} => 1) ((P.chart z).axisPolynomial initialLong (fun _ => 0))
        ((P.chart z).axisPolynomial_support initialLong (fun _ => 0))
        (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1) (P.candidate z).orbit))) :
    D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : {i // commonKeep i} => (A.sides i.val : ℝ)) q l W
      (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
        ((freezing.problem.withKeep commonKeep hkeep).candidate z).orbit) :=
  (freezing.problem.candidate z).hasCommonRefilteredOrbitFactors_withKeep
    commonKeep (hkeep z) bD ω hD q l W
    (freezing.problem_nativeFactors_of_zero_restriction initialLong hstageLong bD ω hD q l W z h)

end AllocatedExternalCandidateProblem.AxisFreezing

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct BigOperators

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer allocatedFrozenCurrentGradeResetConstant

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X] [DecidableEq X]
    {I Deck J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {Rad σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U btag Rad σ}
    {hb : ∀ j, span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hRad : ∀ j, 0 < Rad j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U btag S hb o hRad hσ N poly hm τ ξ stride cells center}
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M s} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem.AxisFreezing

variable {cost massThreshold scoreThreshold : ℝ}
    {P0 : AllocatedExternalCandidateProblem (E := Deck) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold}
    {keepOld : P0.productive → LayerSamplerVariables G I n B → Prop}
    {shortCost : ℝ} (freezing : P0.AxisFreezing keepOld shortCost)
    (commonKeep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : freezing.problem.productive,
      (freezing.problem.chart z).keep = commonKeep)
    {ι κ χ η : Type} [Fintype ι] [Fintype κ] [Fintype χ] [Fintype η]
    (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = span ℚ (bD '' {i | j ≤ ω i}))
    (bF : Basis κ ℚ M) (ν : κ → ℕ)
    (hF : ∀ j, Fmark.layer j = span ℚ (bF '' {i | j ≤ ν i}))
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)

local notation "Vars" => {i : LayerSamplerVariables G I n B // commonKeep i}
local notation "fast" => W.map (D.filtration.associatedGradedMap Fmark φ hφ)
local notation "gmark" => Fmark.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J) marked
local notation "Z" => Fmark.realPolynomialSymbolHom bF ν hF (fullTaggedVariableWeight J) gmark
local notation "Q" => freezing.problem.withKeep commonKeep hkeep

noncomputable def historyStageData_of_zero_restricted_factors
    [instSymbolD : Fintype (SymbolBasisIndex (fun _ : Vars => 1) ω)]
    [instSymbolF : Fintype (SymbolBasisIndex (fun _ : Vars => 1) ν)]
    (eQ : Basis η ℚ (Fmark.AssociatedGraded ⧸ (fast).toSubmodule))
    (r : ℕ) (hr : r ≤ s)
    [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    (Cprimitive : ℕ) (x b Bstage Rrank : ℝ) (C : ℕ)
    (hx : 0 ≤ x) (hxb : x ≤ b) (hBstage : Bstage ≤ b)
    (hcost : cost ≤ (x + Cprimitive) ^ Cprimitive)
    (HMap l H Hθ : ℕ) (qNative : ℝ)
    (hHMap : 1 ≤ HMap) (hl : 0 < l) (hH : 1 ≤ H)
    (hHMapExp : (HMap : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hlExp : (l : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hHExp : (H : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hHθExp : (Hθ : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hqNative : qNative ≤ (x + Cprimitive) ^ Cprimitive)
    (hentries : ∀ i j, RationalHeightLE (bF.repr (φ (bD j)) i) HMap)
    (hsource : (Fintype.card (SymbolBasisIndex (fun _ : Vars => 1) ω) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (htarget : (Fintype.card (SymbolBasisIndex (fun _ : Vars => 1) ν) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hκ : (Fintype.card κ : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hχ : (Fintype.card χ : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hη : (Fintype.card η : ℝ) ≤ x)
    (htags : (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hsampler : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hbracket : ∀ i j z, RationalHeightLE (bF.repr ⁅bF i, bF j⁆ z) H)
    (vg : χ → Fmark.PolynomialSymbol (fun _ : Vars => 1))
    (hspan : span ℚ (Set.range vg) =
      (Fmark.symbolPointwiseSubalgebra bF ν hF (fun _ : Vars => 1) fast).toSubmodule)
    (hvg : ∀ i z, RationalHeightLE
      ((Fmark.polynomialSymbolBasis bF ν hF (fun _ : Vars => 1)).repr (vg i) z) H)
    (hθ : ∀ j i, RationalHeightLE (((eQ.coord j).comp (fast).toSubmodule.mkQ)
      (Fmark.associatedGradedBasis bF ν hF i)) Hθ)
    (initialLong : LayerSamplerVariables G I n B → Prop)
    (hstageLong : ∀ z : P0.productive, ∀ i, keepOld z i → initialLong i)
    (hOriginal : ∀ z : P0.productive, D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : {i : LayerSamplerVariables G I n B // initialLong i} => (A.sides i.val : ℝ)) qNative l W
      (D.filtration.weightedAdaptedRealChartHom (fun _ : (P0.chart z).Variables => 1)
        (fun _ : {i : LayerSamplerVariables G I n B // initialLong i} => 1)
        ((P0.chart z).axisPolynomial initialLong (fun _ => 0))
        ((P0.chart z).axisPolynomial_support initialLong (fun _ => 0))
        (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
          (P0.candidate z).orbit)))
    (hτ : τ ≤ 1) (hξ : ξ ≤ 1) (hσone : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ 1 / 8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (pTest sourceNative α : ℝ)
    (hsourceNative : 0 ≤ sourceNative)
    (hkept : ∀ i, commonKeep i → Real.exp (allocatedCandidateStageSlice s m Cprimitive b) ≤ (A.sides i : ℝ))
    (hfrozen : ∀ i, ¬commonKeep i → (A.sides i : ℝ) ≤ Real.exp (allocatedCandidateStageSlice s m Cprimitive b))
    (hTest : OrdinaryPolynomialPhase.budget r ≤ pTest)
    (hα : α ≤ (9 / 10 : ℝ) * massThreshold)
    (hdirect : A.NativeDetection r (allocatedCandidateStageSlice s m Cprimitive b) pTest sourceNative α)
    (hNmajor : ∀ i, Real.exp ((allocatedCandidateNativeMajorBudget
      (sourceNative + allocatedCandidateStageBase s m Cprimitive b + 2)
      (allocatedCandidateStageBase s m Cprimitive b) + C) ^ C) ≤ (N i : ℝ))
    (hRrank : Real.exp ((allocatedCandidateNativeMajorBudget
      (sourceNative + allocatedCandidateStageBase s m Cprimitive b + 2)
      (allocatedCandidateStageBase s m Cprimitive b) + C) ^ C) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j)) :
    HistoryStageData (χ := χ) (instSymbolD := instSymbolD) (instSymbolF := instSymbolF)
      (P := freezing.problem) (keep := commonKeep) (hkeep := hkeep) (bD := bD) (ω := ω) (hD := hD)
      (bF := bF) (ν := ν) (hF := hF) (hφ := hφ) (W := W)
      eQ r 1 Bstage
        ((allocatedCandidateForwardControlInput s (Fintype.card η) b +
          allocatedCandidateTerminalControlConstant s m 1) ^
          allocatedCandidateTerminalControlConstant s m 1)
        (allocatedCandidateNativeMajorBudget
          (sourceNative + allocatedCandidateStageBase s m Cprimitive b + 2)
          (allocatedCandidateStageBase s m Cprimitive b)) Rrank C := by
  exact freezing.problem.historyStageData_of_prefix_bounds
    commonKeep hkeep bD ω hD bF ν hF hφ W eQ r hr
    Cprimitive x b Bstage Rrank C hx hxb hBstage
    cost hcost (fun z => freezing.withKeep_slice_dense commonKeep hkeep z)
    HMap l H Hθ qNative hHMap hl hH hHMapExp hlExp hHExp hHθExp
    hqNative hentries hsource htarget hκ hχ hη htags hsampler hJ
    hbracket vg hspan hvg hθ
    (fun z => freezing.withKeep_nativeFactors_of_zero_restriction commonKeep hkeep
      initialLong hstageLong bD ω hD qNative l W z
      (hOriginal z))
    hτ hξ hσone Cgeo hCgeo hchart hsmall hpoly
    pTest sourceNative α hsourceNative hkept hfrozen hTest hα hdirect hNmajor hRrank hrank

end AllocatedExternalCandidateProblem.AxisFreezing
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct BigOperators

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X] [DecidableEq X]
    {I Deck J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {Rad σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U btag Rad σ}
    {hb : ∀ j, span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hRad : ∀ j, 0 < Rad j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U btag S hb o hRad hσ N poly hm τ ξ stride cells center}
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M s} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := Deck) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)
    (keep : ℕ → LayerSamplerVariables G I n B → Prop)
    {ι κ η : Type} {χ : ℕ → Type} [Fintype ι] [Fintype κ] [∀ r, Fintype (χ r)] [Fintype η]
    (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = span ℚ (bD '' {i | j ≤ ω i}))
    (bF : Basis κ ℚ M) (ν : κ → ℕ)
    (hF : ∀ j, Fmark.layer j = span ℚ (bF '' {i | j ≤ ν i}))
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)

local notation "fast" => W.map (D.filtration.associatedGradedMap Fmark φ hφ)
local notation "gmark" => Fmark.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J) marked
local notation "Z" => Fmark.realPolynomialSymbolHom bF ν hF (fullTaggedVariableWeight J) gmark
local notation "countConstants" => (fun n => fullChartStageCountConstant (n + 1) 254)

theorem exists_forward_terminal_of_zero_restricted_candidates
    [Fintype (SymbolBasisIndex (fun _ : LayerSamplerVariables G I n B => 1) ω)]
    [Fintype (SymbolBasisIndex (fun _ : LayerSamplerVariables G I n B => 1) ν)]
    [∀ r, Fintype (SymbolBasisIndex (fun _ : {i : LayerSamplerVariables G I n B // keep r i} => 1) ω)]
    [∀ r, Fintype (SymbolBasisIndex (fun _ : {i : LayerSamplerVariables G I n B // keep r i} => 1) ν)]
    [∀ r, TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [∀ r, IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [∀ r, ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [∀ r, T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    (eQ : Basis η ℚ (Fmark.AssociatedGraded ⧸ (fast).toSubmodule))
    (lift : (Fmark.AssociatedGraded ⧸ (fast).toSubmodule) →ₗ[ℚ] Fmark.AssociatedGraded)
    (hfast : BasisGradedSubmodule (Fmark.associatedGradedBasis bF ν hF) ν (fast).toSubmodule)
    (hsection : ∀ y, (fast).toSubmodule.mkQ (lift y) = y)
    (Bphase Bbound pTree Rrank : ℝ) (Hbr qS : ℕ)
    (scheduleExponent : ℕ) (x gainLog stageLog : ℝ)
    (T : CertifiedFullChartFiniteHistory.BudgetedBranchTree Fmark bF ν hF J
      (fast).toSubmodule (eQ.baseChange ℝ) lift Z U poly N Bphase
      (fun r => preparedFiniteForwardCap scheduleExponent countConstants r x) s pTree)
    (hx : 0 ≤ x) (hgain : gainLog ∈ Set.Icc 0 x) (hstage : stageLog ∈ Set.Icc 0 x)
    (Cprimitive Csource : ℕ) (sourceNative pTest α : ℕ → ℝ)
    (hSourceNonneg : ∀ r < s, 0 ≤ sourceNative r)
    (hSourceBound : ∀ r < s, sourceNative r ≤
      (preparedFiniteForwardSourcePrecision scheduleExponent countConstants r x gainLog stageLog +
        preparedFiniteForwardWork scheduleExponent countConstants r x + Csource) ^ Csource)
    (hBaseExponent : allocatedCandidateStageBaseExponent s m Cprimitive ≤ scheduleExponent)
    (hphaseExponent : ∀ r < s,
      allocatedCandidateCompositePhaseConstant s m 1
        (allocatedCandidatePromotedMajorConstant Csource) r ≤ scheduleExponent)
    (hHbr : 1 ≤ Hbr) (hqS : 0 < qS)
    (hκBase : (Fintype.card κ : ℝ) ≤ x)
    (hTagsBase : (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ x)
    (hηBase : (Fintype.card η : ℝ) ≤ x)
    (hHbrBase : (Hbr : ℝ) ≤ Real.exp x) (hqSBase : (qS : ℝ) ≤ Real.exp x)
    (hBboundBase : Bbound ≤ Real.exp x)
    (hstructure : ∀ i j z, RationalHeightLE ((Fmark.associatedGradedBasis bF ν hF).repr
      ⁅Fmark.associatedGradedBasis bF ν hF i, Fmark.associatedGradedBasis bF ν hF j⁆ z) Hbr)
    (hentry : ∀ i j, |((Fmark.associatedGradedBasis bF ν hF).baseChange ℝ).repr
      (lift.baseChange ℝ ((eQ.baseChange ℝ) j)) i| ≤ Bbound)
    (hgrid : ∀ j, (fun i => ((Fmark.associatedGradedBasis bF ν hF).baseChange ℝ).repr
      (lift.baseChange ℝ ((eQ.baseChange ℝ) j)) i) ∈ realDenominatorGrid qS)
    (hcost : cost ≤ (x + Cprimitive) ^ Cprimitive)
    (HMap l H Hθ : ℕ) (qNative : ℝ)
    (hHMap : 1 ≤ HMap) (hl : 0 < l) (hH : 1 ≤ H)
    (hHMapExp : (HMap : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hlExp : (l : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hHExp : (H : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hHθExp : (Hθ : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hqNative : qNative ≤ (x + Cprimitive) ^ Cprimitive)
    (hentries : ∀ i j, RationalHeightLE (bF.repr (φ (bD j)) i) HMap)
    (hsource : (Fintype.card (SymbolBasisIndex
      (fun _ : LayerSamplerVariables G I n B => 1) ω) : ℝ) ≤
        (x + Cprimitive) ^ Cprimitive)
    (htarget : (Fintype.card (SymbolBasisIndex
      (fun _ : LayerSamplerVariables G I n B => 1) ν) : ℝ) ≤
        (x + Cprimitive) ^ Cprimitive)
    (hκ : (Fintype.card κ : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hχ : ∀ r < s, (Fintype.card (χ r) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (htags : (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hsampler : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hbracket : ∀ i j z, RationalHeightLE (bF.repr ⁅bF i, bF j⁆ z) H)
    (vg : ∀ r, χ r → Fmark.PolynomialSymbol
      (fun _ : {i : LayerSamplerVariables G I n B // keep r i} => 1))
    (hspan : ∀ r < s, span ℚ (Set.range (vg r)) =
      (Fmark.symbolPointwiseSubalgebra bF ν hF
        (fun _ : {i : LayerSamplerVariables G I n B // keep r i} => 1) fast).toSubmodule)
    (hvg : ∀ r < s, ∀ i z, RationalHeightLE
      ((Fmark.polynomialSymbolBasis bF ν hF
        (fun _ : {i : LayerSamplerVariables G I n B // keep r i} => 1)).repr (vg r i) z) H)
    (hθ : ∀ j i, RationalHeightLE (((eQ.coord j).comp (fast).toSubmodule.mkQ)
      (Fmark.associatedGradedBasis bF ν hF i)) Hθ)
    (initialLong : LayerSamplerVariables G I n B → Prop)
    (hstageLong : ∀ r < s, ∀ i, keep r i → initialLong i)
    (hOriginal : ∀ z : P.productive, D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : {i : LayerSamplerVariables G I n B // initialLong i} => (A.sides i.val : ℝ)) qNative l W
      (D.filtration.weightedAdaptedRealChartHom (fun _ : (P.chart z).Variables => 1)
        (fun _ : {i : LayerSamplerVariables G I n B // initialLong i} => 1)
        ((P.chart z).axisPolynomial initialLong (fun _ => 0))
        ((P.chart z).axisPolynomial_support initialLong (fun _ => 0))
        (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
          (P.candidate z).orbit)))
    (hτ : τ ≤ 1) (hξ : ξ ≤ 1) (hσone : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ 1 / 8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hkept : ∀ r, ∀ i, keep r i → Real.exp (allocatedCandidateStageSlice s m Cprimitive
      (preparedFiniteForwardParameter scheduleExponent countConstants r x)) ≤ (A.sides i : ℝ))
    (hfrozen : ∀ r, ∀ i, ¬keep r i → (A.sides i : ℝ) ≤ Real.exp (allocatedCandidateStageSlice s m Cprimitive
      (preparedFiniteForwardParameter scheduleExponent countConstants r x)))
    (hTest : ∀ r < s, OrdinaryPolynomialPhase.budget r ≤ pTest r)
    (hα : ∀ r < s, α r ≤ (9 / 10 : ℝ) * massThreshold)
    (hdirect : ∀ r < s, A.NativeDetection r (allocatedCandidateStageSlice s m Cprimitive
      (preparedFiniteForwardParameter scheduleExponent countConstants r x)) (pTest r) (sourceNative r) (α r))
    (hN : ∀ i, Real.exp (preparedFiniteForwardCumulative scheduleExponent countConstants s x) ≤ (N i : ℝ))
    (hRrank : Real.exp (preparedFiniteForwardCumulative scheduleExponent countConstants s x) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j)) :
    ∃ history ∈ T.level s,
      FullChartControlledFactors Fmark bF ν hF J poly N history.outer.1 history.outer.2
        (preparedFiniteForwardWork scheduleExponent countConstants s x) ∧
      RationalTaggedConstraintCertificate J Set.univ history.K
        (preparedFiniteForwardCumulative scheduleExponent countConstants s x)
        (s * (Fintype.card η * m)) ∧
      ∀ point ∈ history.K,
        eval₂ point (Fmark.realGradedSymbolPolynomial bF ν hF (fullTaggedVariableWeight J)
          (history.outer.1⁻¹ * Z * history.outer.2⁻¹).coord) ∈
            (fast).toSubmodule.baseChange ℝ := by
  let shortCost : ℕ → ℝ := fun r => allocatedCandidateStageSlice s m Cprimitive
    (preparedFiniteForwardParameter scheduleExponent countConstants r x)
  have hrefinement (r : ℕ) : Nonempty (P.AxisFreezing (fun _ => keep r) (shortCost r)) :=
    P.exists_forward_axisFreezing (keep r) Cprimitive scheduleExponent r x hx hcost
      (hkept r) (hfrozen r)
  let freezing : ∀ r, P.AxisFreezing (fun _ => keep r) (shortCost r) :=
    fun r => Classical.choice (hrefinement r)
  have hkeep : ∀ r, ∀ z : (freezing r).problem.productive,
      ((freezing r).problem.chart z).keep = keep r := fun _ _ => rfl
  apply exists_forward_terminal_of_native_stage_data (χ := χ)
    (fun r => max cost (shortCost r)) (fun _ => massThreshold) (fun _ => scoreThreshold)
    (fun r => (freezing r).problem) keep hkeep bD ω hD bF ν hF hφ W
    eQ lift hfast hsection Bphase Bbound pTree Rrank Hbr qS
    scheduleExponent x gainLog stageLog T hx hgain hstage Cprimitive Csource sourceNative
    hSourceNonneg hSourceBound hBaseExponent hphaseExponent hHbr hqS hκBase hTagsBase
    hηBase hHbrBase hqSBase hBboundBase hstructure hentry hgrid
  intro r hr
  have hphase := allocatedCandidateForwardMajor_cap s m Cprimitive Csource
    scheduleExponent r hx hgain hstage (hSourceNonneg r hr) (hSourceBound r hr)
    hBaseExponent (hphaseExponent r hr)
  have hscale := Real.exp_le_exp.mpr (hphase.trans
    (preparedFiniteForwardCap_le_cumulative scheduleExponent countConstants hx hr))
  exact ⟨(freezing r).historyStageData_of_zero_restricted_factors (χ := χ r) (keep r) (hkeep r)
    bD ω hD bF ν hF hφ W eQ r (Nat.le_of_lt hr)
    Cprimitive x (preparedFiniteForwardParameter scheduleExponent countConstants r x)
    (preparedFiniteForwardCumulative scheduleExponent countConstants r x) Rrank
    (allocatedCandidateTerminalPhaseConstant s m 1 r) hx
    (le_preparedFiniteForwardParameter scheduleExponent countConstants r hx)
    (preparedFiniteForward_prefix_bounds scheduleExponent countConstants r hx).1.2
    hcost HMap l H Hθ qNative hHMap hl hH hHMapExp hlExp hHExp hHθExp hqNative hentries
    ((Nat.cast_le.mpr (ordinarySymbolSubtype_card_le (keep r) ω)).trans hsource)
    ((Nat.cast_le.mpr (ordinarySymbolSubtype_card_le (keep r) ν)).trans htarget)
    hκ (hχ r hr) hηBase htags hsampler hJ hbracket
    (vg r) (hspan r hr) (hvg r hr) hθ initialLong
    (fun z i hi => hstageLong r hr i hi) hOriginal hτ hξ hσone Cgeo hCgeo hchart hsmall hpoly
    (pTest r) (sourceNative r) (α r) (hSourceNonneg r hr) (hkept r) (hfrozen r)
    (hTest r hr) (hα r hr) (hdirect r hr) (fun i => hscale.trans (hN i))
    (hscale.trans hRrank) hrank⟩

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct BigOperators

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X] [DecidableEq X]
    {I Deck J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {Rad σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U btag Rad σ}
    {hb : ∀ j, span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hRad : ∀ j, 0 < Rad j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U btag S hb o hRad hσ N poly hm τ ξ stride cells center}
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M s} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := Deck) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)
    (keep : ℕ → LayerSamplerVariables G I n B → Prop)
    {ι κ η : Type} {χ : ℕ → Type} [Fintype ι] [Fintype κ] [∀ r, Fintype (χ r)] [Fintype η]
    (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = span ℚ (bD '' {i | j ≤ ω i}))
    (bF : Basis κ ℚ M) (ν : κ → ℕ)
    (hF : ∀ j, Fmark.layer j = span ℚ (bF '' {i | j ≤ ν i}))
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)

local notation "fast" => W.map (D.filtration.associatedGradedMap Fmark φ hφ)
local notation "gmark" => Fmark.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J) marked
local notation "Z" => Fmark.realPolynomialSymbolHom bF ν hF (fullTaggedVariableWeight J) gmark
local notation "countConstants" => (fun n => fullChartStageCountConstant (n + 1) 254)

theorem exists_early_forward_terminal_of_zero_restricted_candidates
    [Fintype (SymbolBasisIndex (fun _ : LayerSamplerVariables G I n B => 1) ω)]
    [Fintype (SymbolBasisIndex (fun _ : LayerSamplerVariables G I n B => 1) ν)]
    [∀ r, Fintype (SymbolBasisIndex (fun _ : {i : LayerSamplerVariables G I n B // keep r i} => 1) ω)]
    [∀ r, Fintype (SymbolBasisIndex (fun _ : {i : LayerSamplerVariables G I n B // keep r i} => 1) ν)]
    [∀ r, TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [∀ r, IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [∀ r, ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [∀ r, T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    (eQ : Basis η ℚ (Fmark.AssociatedGraded ⧸ (fast).toSubmodule))
    (lift : (Fmark.AssociatedGraded ⧸ (fast).toSubmodule) →ₗ[ℚ] Fmark.AssociatedGraded)
    (hfast : BasisGradedSubmodule (Fmark.associatedGradedBasis bF ν hF) ν (fast).toSubmodule)
    (hsection : ∀ y, (fast).toSubmodule.mkQ (lift y) = y)
    (Bbound Rrank : ℝ) (Hbr qS : ℕ)
    (scheduleExponent : ℕ) (x gainLog stageLog : ℝ)
    (hx : 0 ≤ x) (hgain : gainLog ∈ Set.Icc 0 x) (hstage : stageLog ∈ Set.Icc 0 x)
    (Cprimitive Csource : ℕ) (sourceNative pTest α : ℕ → ℝ)
    (hSourceNonneg : ∀ r < s, 0 ≤ sourceNative r)
    (hSourceBound : ∀ r < s, sourceNative r ≤
      (preparedFiniteForwardSourcePrecision scheduleExponent countConstants r x gainLog stageLog +
        preparedFiniteForwardWork scheduleExponent countConstants r x + Csource) ^ Csource)
    (hBaseExponent : allocatedCandidateStageBaseExponent s m Cprimitive ≤ scheduleExponent)
    (hphaseExponent : ∀ r < s,
      allocatedCandidateCompositePhaseConstant s m 1
        (allocatedCandidatePromotedMajorConstant Csource) r ≤ scheduleExponent)
    (hHbr : 1 ≤ Hbr) (hqS : 0 < qS)
    (hκBase : (Fintype.card κ : ℝ) ≤ x)
    (hTagsBase : (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ x)
    (hηBase : (Fintype.card η : ℝ) ≤ x)
    (hmEarly : (m : ℝ) ≤ x)
    (hblocksEarly : ((s * (Fintype.card η * m) : ℕ) : ℝ) ≤ x)
    (hHbrBase : (Hbr : ℝ) ≤ Real.exp x) (hqSBase : (qS : ℝ) ≤ Real.exp x)
    (hBboundBase : Bbound ≤ Real.exp x)
    (hstructure : ∀ i j z, RationalHeightLE ((Fmark.associatedGradedBasis bF ν hF).repr
      ⁅Fmark.associatedGradedBasis bF ν hF i, Fmark.associatedGradedBasis bF ν hF j⁆ z) Hbr)
    (hentry : ∀ i j, |((Fmark.associatedGradedBasis bF ν hF).baseChange ℝ).repr
      (lift.baseChange ℝ ((eQ.baseChange ℝ) j)) i| ≤ Bbound)
    (hgrid : ∀ j, (fun i => ((Fmark.associatedGradedBasis bF ν hF).baseChange ℝ).repr
      (lift.baseChange ℝ ((eQ.baseChange ℝ) j)) i) ∈ realDenominatorGrid qS)
    (hcost : cost ≤ (x + Cprimitive) ^ Cprimitive)
    (HMap l H Hθ : ℕ) (qNative : ℝ)
    (hHMap : 1 ≤ HMap) (hl : 0 < l) (hH : 1 ≤ H)
    (hHMapExp : (HMap : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hlExp : (l : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hHExp : (H : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hHθExp : (Hθ : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hqNative : qNative ≤ (x + Cprimitive) ^ Cprimitive)
    (hentries : ∀ i j, RationalHeightLE (bF.repr (φ (bD j)) i) HMap)
    (hsource : (Fintype.card (SymbolBasisIndex
      (fun _ : LayerSamplerVariables G I n B => 1) ω) : ℝ) ≤
        (x + Cprimitive) ^ Cprimitive)
    (htarget : (Fintype.card (SymbolBasisIndex
      (fun _ : LayerSamplerVariables G I n B => 1) ν) : ℝ) ≤
        (x + Cprimitive) ^ Cprimitive)
    (hκ : (Fintype.card κ : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hχ : ∀ r < s, (Fintype.card (χ r) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (htags : (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hsampler : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hbracket : ∀ i j z, RationalHeightLE (bF.repr ⁅bF i, bF j⁆ z) H)
    (vg : ∀ r, χ r → Fmark.PolynomialSymbol
      (fun _ : {i : LayerSamplerVariables G I n B // keep r i} => 1))
    (hspan : ∀ r < s, span ℚ (Set.range (vg r)) =
      (Fmark.symbolPointwiseSubalgebra bF ν hF
        (fun _ : {i : LayerSamplerVariables G I n B // keep r i} => 1) fast).toSubmodule)
    (hvg : ∀ r < s, ∀ i z, RationalHeightLE
      ((Fmark.polynomialSymbolBasis bF ν hF
        (fun _ : {i : LayerSamplerVariables G I n B // keep r i} => 1)).repr (vg r i) z) H)
    (hθ : ∀ j i, RationalHeightLE (((eQ.coord j).comp (fast).toSubmodule.mkQ)
      (Fmark.associatedGradedBasis bF ν hF i)) Hθ)
    (initialLong : LayerSamplerVariables G I n B → Prop)
    (hstageLong : ∀ r < s, ∀ i, keep r i → initialLong i)
    (hOriginal : ∀ z : P.productive, D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : {i : LayerSamplerVariables G I n B // initialLong i} => (A.sides i.val : ℝ)) qNative l W
      (D.filtration.weightedAdaptedRealChartHom (fun _ : (P.chart z).Variables => 1)
        (fun _ : {i : LayerSamplerVariables G I n B // initialLong i} => 1)
        ((P.chart z).axisPolynomial initialLong (fun _ => 0))
        ((P.chart z).axisPolynomial_support initialLong (fun _ => 0))
        (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
          (P.candidate z).orbit)))
    (hτ : τ ≤ 1) (hξ : ξ ≤ 1) (hσone : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ 1 / 8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hkept : ∀ r, ∀ i, keep r i → Real.exp (allocatedCandidateStageSlice s m Cprimitive
      (preparedFiniteForwardParameter scheduleExponent countConstants r x)) ≤ (A.sides i : ℝ))
    (hfrozen : ∀ r, ∀ i, ¬keep r i → (A.sides i : ℝ) ≤ Real.exp (allocatedCandidateStageSlice s m Cprimitive
      (preparedFiniteForwardParameter scheduleExponent countConstants r x)))
    (hTest : ∀ r < s, OrdinaryPolynomialPhase.budget r ≤ pTest r)
    (hα : ∀ r < s, α r ≤ (9 / 10 : ℝ) * massThreshold)
    (hdirect : ∀ r < s, A.NativeDetection r (allocatedCandidateStageSlice s m Cprimitive
      (preparedFiniteForwardParameter scheduleExponent countConstants r x)) (pTest r) (sourceNative r) (α r))
    (hN : ∀ i, Real.exp (preparedFiniteForwardCumulative scheduleExponent countConstants s x) ≤ (N i : ℝ))
    (hRrank : Real.exp (preparedFiniteForwardCumulative scheduleExponent countConstants s x) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j)) :
    let hXEarly : (Fintype.card X : ℝ) ≤ x := by
      have hsum : (Fintype.card X : ℝ) + (Fintype.card (Σ j, J j) : ℝ) ≤ x := by
        simpa only [Fintype.card_sum, Nat.cast_add] using hTagsBase
      exact (le_add_of_nonneg_right (Nat.cast_nonneg _)).trans hsum
    let hJEarly : (Fintype.card (Σ j, J j) : ℝ) ≤ x := by
      have hsum : (Fintype.card X : ℝ) + (Fintype.card (Σ j, J j) : ℝ) ≤ x := by
        simpa only [Fintype.card_sum, Nat.cast_add] using hTagsBase
      exact (le_add_of_nonneg_left (Nat.cast_nonneg _)).trans hsum
    let hNEarly : ∀ i, 1 ≤ N i := by
      intro i
      have hpos : 0 < N i := by
        exact_mod_cast ((Real.exp_pos _).trans_le (hN i))
      exact Nat.succ_le_iff.mpr hpos
    let T := CertifiedFullChartFiniteHistory.earlyForwardBranchTree
      Fmark bF ν hF J (fast).toSubmodule (eQ.baseChange ℝ) lift Z U poly N
      s scheduleExponent x hx hXEarly hmEarly hJEarly hηBase hblocksEarly
      (fun j ex _ => hm j ex) hNEarly
    ∃ history ∈ T.level s,
      FullChartControlledFactors Fmark bF ν hF J poly N history.outer.1 history.outer.2
        (preparedFiniteForwardWork scheduleExponent countConstants s x) ∧
      RationalTaggedConstraintCertificate J Set.univ history.K
        (preparedFiniteForwardCumulative scheduleExponent countConstants s x)
        (s * (Fintype.card η * m)) ∧
      ∀ point ∈ history.K,
        eval₂ point (Fmark.realGradedSymbolPolynomial bF ν hF (fullTaggedVariableWeight J)
          (history.outer.1⁻¹ * Z * history.outer.2⁻¹).coord) ∈
            (fast).toSubmodule.baseChange ℝ := by
  intro hXEarly hJEarly hNEarly T
  exact P.exists_forward_terminal_of_zero_restricted_candidates keep bD ω hD bF ν hF hφ W
    eQ lift hfast hsection (preparedFiniteForwardCumulative scheduleExponent countConstants s x) Bbound
    (preparedFiniteForwardParameter scheduleExponent countConstants s x) Rrank Hbr qS scheduleExponent x
    gainLog stageLog T hx hgain hstage Cprimitive Csource sourceNative pTest α hSourceNonneg hSourceBound
    hBaseExponent hphaseExponent hHbr hqS hκBase hTagsBase hηBase hHbrBase hqSBase hBboundBase hstructure
    hentry hgrid hcost HMap l H Hθ qNative hHMap hl hH hHMapExp hlExp hHExp hHθExp hqNative hentries
    hsource htarget hκ hχ htags hsampler hJ hbracket vg hspan hvg hθ initialLong hstageLong hOriginal hτ hξ hσone Cgeo hCgeo
    hchart hsmall hpoly hkept hfrozen hTest hα hdirect hN hRrank hrank

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct BigOperators

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X] [DecidableEq X]
    {I Deck J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {Rad σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U btag Rad σ}
    {hb : ∀ j, span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hRad : ∀ j, 0 < Rad j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U btag S hb o hRad hσ N poly hm τ ξ stride cells center}
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M s} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := Deck) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)
    (keep : ℕ → LayerSamplerVariables G I n B → Prop)
    {ι κ η γ : Type} [Fintype ι] [Fintype κ] [Fintype η] [Fintype γ]
    (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = span ℚ (bD '' {i | j ≤ ω i}))
    (bF : Basis κ ℚ M) (ν : κ → ℕ)
    (hF : ∀ j, Fmark.layer j = span ℚ (bF '' {i | j ≤ ν i}))
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)

local notation "fast" => W.map (D.filtration.associatedGradedMap Fmark φ hφ)
local notation "gmark" => Fmark.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J) marked
local notation "Z" => Fmark.realPolynomialSymbolHom bF ν hF (fullTaggedVariableWeight J) gmark
local notation "countConstants" => (fun n => fullChartStageCountConstant (n + 1) 254)

theorem exists_early_forward_terminal_of_zero_restricted_fast_generators
    [Fintype (SymbolBasisIndex (fun _ : LayerSamplerVariables G I n B => 1) ω)]
    [Fintype (SymbolBasisIndex (fun _ : LayerSamplerVariables G I n B => 1) ν)]
    [∀ r, Fintype (SymbolBasisIndex (fun _ : {i : LayerSamplerVariables G I n B // keep r i} => 1) ω)]
    [∀ r, Fintype (SymbolBasisIndex (fun _ : {i : LayerSamplerVariables G I n B // keep r i} => 1) ν)]
    [∀ r, TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [∀ r, IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [∀ r, ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [∀ r, T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    (eQ : Basis η ℚ (Fmark.AssociatedGraded ⧸ (fast).toSubmodule))
    (lift : (Fmark.AssociatedGraded ⧸ (fast).toSubmodule) →ₗ[ℚ] Fmark.AssociatedGraded)
    (hfast : BasisGradedSubmodule (Fmark.associatedGradedBasis bF ν hF) ν (fast).toSubmodule)
    (hsection : ∀ y, (fast).toSubmodule.mkQ (lift y) = y)
    (Bbound Rrank : ℝ) (Hbr qS : ℕ)
    (scheduleExponent : ℕ) (x gainLog stageLog : ℝ)
    (hx : 0 ≤ x) (hgain : gainLog ∈ Set.Icc 0 x) (hstage : stageLog ∈ Set.Icc 0 x)
    (Cprimitive Csource : ℕ) (sourceNative pTest α : ℕ → ℝ)
    (hSourceNonneg : ∀ r < s, 0 ≤ sourceNative r)
    (hSourceBound : ∀ r < s, sourceNative r ≤
      (preparedFiniteForwardSourcePrecision scheduleExponent countConstants r x gainLog stageLog +
        preparedFiniteForwardWork scheduleExponent countConstants r x + Csource) ^ Csource)
    (hBaseExponent : allocatedCandidateStageBaseExponent s m Cprimitive ≤ scheduleExponent)
    (hphaseExponent : ∀ r < s,
      allocatedCandidateCompositePhaseConstant s m 1
        (allocatedCandidatePromotedMajorConstant Csource) r ≤ scheduleExponent)
    (hHbr : 1 ≤ Hbr) (hqS : 0 < qS)
    (hκBase : (Fintype.card κ : ℝ) ≤ x)
    (hTagsBase : (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ x)
    (hηBase : (Fintype.card η : ℝ) ≤ x)
    (hmEarly : (m : ℝ) ≤ x)
    (hblocksEarly : ((s * (Fintype.card η * m) : ℕ) : ℝ) ≤ x)
    (hHbrBase : (Hbr : ℝ) ≤ Real.exp x) (hqSBase : (qS : ℝ) ≤ Real.exp x)
    (hBboundBase : Bbound ≤ Real.exp x)
    (hstructure : ∀ i j z, RationalHeightLE ((Fmark.associatedGradedBasis bF ν hF).repr
      ⁅Fmark.associatedGradedBasis bF ν hF i, Fmark.associatedGradedBasis bF ν hF j⁆ z) Hbr)
    (hentry : ∀ i j, |((Fmark.associatedGradedBasis bF ν hF).baseChange ℝ).repr
      (lift.baseChange ℝ ((eQ.baseChange ℝ) j)) i| ≤ Bbound)
    (hgrid : ∀ j, (fun i => ((Fmark.associatedGradedBasis bF ν hF).baseChange ℝ).repr
      (lift.baseChange ℝ ((eQ.baseChange ℝ) j)) i) ∈ realDenominatorGrid qS)
    (hcost : cost ≤ (x + Cprimitive) ^ Cprimitive)
    (HMap l H Hθ : ℕ) (qNative : ℝ)
    (hHMap : 1 ≤ HMap) (hl : 0 < l) (hH : 1 ≤ H)
    (hHMapExp : (HMap : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hlExp : (l : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hHExp : (H : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hHθExp : (Hθ : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hqNative : qNative ≤ (x + Cprimitive) ^ Cprimitive)
    (hentries : ∀ i j, RationalHeightLE (bF.repr (φ (bD j)) i) HMap)
    (hsource : (Fintype.card (SymbolBasisIndex
      (fun _ : LayerSamplerVariables G I n B => 1) ω) : ℝ) ≤
        (x + Cprimitive) ^ Cprimitive)
    (htarget : (Fintype.card (SymbolBasisIndex
      (fun _ : LayerSamplerVariables G I n B => 1) ν) : ℝ) ≤
        (x + Cprimitive) ^ Cprimitive)
    (hκ : (Fintype.card κ : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (htags : (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hsampler : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive)
    (hbracket : ∀ i j z, RationalHeightLE (bF.repr ⁅bF i, bF j⁆ z) H)
    (fastGenerators : γ → Fmark.AssociatedGraded)
    (hfastSpan : span ℚ (Set.range fastGenerators) = (fast).toSubmodule)
    (hfastHeight : ∀ a i, RationalHeightLE
      ((Fmark.associatedGradedBasis bF ν hF).repr (fastGenerators a) i) H)
    (hgeneratorCount :
      ((Fintype.card (SymbolBasisIndex
        (fun _ : LayerSamplerVariables G I n B => 1) ν) * Fintype.card γ : ℕ) : ℝ) ≤
          (x + Cprimitive) ^ Cprimitive)
    (hθ : ∀ j i, RationalHeightLE (((eQ.coord j).comp (fast).toSubmodule.mkQ)
      (Fmark.associatedGradedBasis bF ν hF i)) Hθ)
    (initialLong : LayerSamplerVariables G I n B → Prop)
    (hstageLong : ∀ r < s, ∀ i, keep r i → initialLong i)
    (hOriginal : ∀ z : P.productive, D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : {i : LayerSamplerVariables G I n B // initialLong i} =>
        (A.sides i.val : ℝ)) qNative l W
      (D.filtration.weightedAdaptedRealChartHom (fun _ : (P.chart z).Variables => 1)
        (fun _ : {i : LayerSamplerVariables G I n B // initialLong i} => 1)
        ((P.chart z).axisPolynomial initialLong (fun _ => 0))
        ((P.chart z).axisPolynomial_support initialLong (fun _ => 0))
        (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
          (P.candidate z).orbit)))
    (hτ : τ ≤ 1) (hξ : ξ ≤ 1) (hσone : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ 1 / 8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hkept : ∀ r, ∀ i, keep r i → Real.exp (allocatedCandidateStageSlice s m Cprimitive
      (preparedFiniteForwardParameter scheduleExponent countConstants r x)) ≤ (A.sides i : ℝ))
    (hfrozen : ∀ r, ∀ i, ¬keep r i → (A.sides i : ℝ) ≤ Real.exp (allocatedCandidateStageSlice s m Cprimitive
      (preparedFiniteForwardParameter scheduleExponent countConstants r x)))
    (hTest : ∀ r < s, OrdinaryPolynomialPhase.budget r ≤ pTest r)
    (hα : ∀ r < s, α r ≤ (9 / 10 : ℝ) * massThreshold)
    (hdirect : ∀ r < s, A.NativeDetection r (allocatedCandidateStageSlice s m Cprimitive
      (preparedFiniteForwardParameter scheduleExponent countConstants r x)) (pTest r) (sourceNative r) (α r))
    (hN : ∀ i, Real.exp (preparedFiniteForwardCumulative scheduleExponent countConstants s x) ≤ (N i : ℝ))
    (hRrank : Real.exp (preparedFiniteForwardCumulative scheduleExponent countConstants s x) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j)) :
    let hXEarly : (Fintype.card X : ℝ) ≤ x := by
      have hsum : (Fintype.card X : ℝ) + (Fintype.card (Σ j, J j) : ℝ) ≤ x := by
        simpa only [Fintype.card_sum, Nat.cast_add] using hTagsBase
      exact (le_add_of_nonneg_right (Nat.cast_nonneg _)).trans hsum
    let hJEarly : (Fintype.card (Σ j, J j) : ℝ) ≤ x := by
      have hsum : (Fintype.card X : ℝ) + (Fintype.card (Σ j, J j) : ℝ) ≤ x := by
        simpa only [Fintype.card_sum, Nat.cast_add] using hTagsBase
      exact (le_add_of_nonneg_left (Nat.cast_nonneg _)).trans hsum
    let hNEarly : ∀ i, 1 ≤ N i := by
      intro i
      have hpos : 0 < N i := by
        exact_mod_cast ((Real.exp_pos _).trans_le (hN i))
      exact Nat.succ_le_iff.mpr hpos
    let T := CertifiedFullChartFiniteHistory.earlyForwardBranchTree
      Fmark bF ν hF J (fast).toSubmodule (eQ.baseChange ℝ) lift Z U poly N
      s scheduleExponent x hx hXEarly hmEarly hJEarly hηBase hblocksEarly
      (fun j ex _ => hm j ex) hNEarly
    ∃ history ∈ T.level s,
      FullChartControlledFactors Fmark bF ν hF J poly N history.outer.1 history.outer.2
        (preparedFiniteForwardWork scheduleExponent countConstants s x) ∧
      RationalTaggedConstraintCertificate J Set.univ history.K
        (preparedFiniteForwardCumulative scheduleExponent countConstants s x)
        (s * (Fintype.card η * m)) ∧
      ∀ point ∈ history.K,
        eval₂ point (Fmark.realGradedSymbolPolynomial bF ν hF (fullTaggedVariableWeight J)
          (history.outer.1⁻¹ * Z * history.outer.2⁻¹).coord) ∈
            (fast).toSubmodule.baseChange ℝ := by
  intro hXEarly hJEarly hNEarly T
  let χ : ℕ → Type := fun r =>
    SymbolBasisIndex (fun _ : {i : LayerSamplerVariables G I n B // keep r i} => 1) ν × γ
  let vg := fun r => Fmark.pointwiseSymbolSpanningFamily bF ν hF
    (fun _ : {i : LayerSamplerVariables G I n B // keep r i} => 1) fastGenerators
  have hχ (r : ℕ) (_hr : r < s) : (Fintype.card (χ r) : ℝ) ≤
      (x + Cprimitive) ^ Cprimitive := by
    have hcard := ordinarySymbolSubtype_card_le (keep r) ν
    have hmul := Nat.mul_le_mul_right (Fintype.card γ) hcard
    exact (Nat.cast_le.mpr (by simpa only [χ, Fintype.card_prod] using hmul)).trans hgeneratorCount
  have hspan (r : ℕ) (_hr : r < s) : span ℚ (Set.range (vg r)) =
      (Fmark.symbolPointwiseSubalgebra bF ν hF
        (fun _ : {i : LayerSamplerVariables G I n B // keep r i} => 1) fast).toSubmodule :=
    Fmark.pointwiseSymbolSpanningFamily_span bF ν hF _ fast hfast fastGenerators hfastSpan
  have hvg (r : ℕ) (_hr : r < s) : ∀ a i, RationalHeightLE
      ((Fmark.polynomialSymbolBasis bF ν hF
        (fun _ : {i : LayerSamplerVariables G I n B // keep r i} => 1)).repr (vg r a) i) H :=
    Fmark.pointwiseSymbolSpanningFamily_height bF ν hF _ fastGenerators hH hfastHeight
  exact P.exists_early_forward_terminal_of_zero_restricted_candidates keep bD ω hD bF ν hF hφ W
    eQ lift hfast hsection Bbound Rrank Hbr qS scheduleExponent x
    gainLog stageLog hx hgain hstage Cprimitive Csource sourceNative pTest α hSourceNonneg hSourceBound
    hBaseExponent hphaseExponent hHbr hqS hκBase hTagsBase hηBase hmEarly hblocksEarly
    hHbrBase hqSBase hBboundBase hstructure hentry hgrid hcost HMap l H Hθ qNative
    hHMap hl hH hHMapExp hlExp hHExp hHθExp hqNative hentries hsource htarget hκ hχ htags
    hsampler hJ hbracket vg hspan hvg hθ initialLong hstageLong hOriginal hτ hξ hσone Cgeo hCgeo hchart hsmall
    hpoly hkept hfrozen hTest hα hdirect hN hRrank hrank

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct BigOperators

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X] [DecidableEq X]
    {I Deck J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {Rad σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U btag Rad σ}
    {hb : ∀ j, span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hRad : ∀ j, 0 < Rad j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U btag S hb o hRad hσ N poly hm τ ξ stride cells center}
    {L M : Type} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M s} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := Deck) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)
    (keep : ℕ → LayerSamplerVariables G I n B → Prop)
    {ι κ γ : Type} [Fintype ι] [Fintype κ] [Fintype γ]
    (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = span ℚ (bD '' {i | j ≤ ω i}))
    (bF : Basis κ ℚ M) (ν : κ → ℕ)
    (hF : ∀ j, Fmark.layer j = span ℚ (bF '' {i | j ≤ ν i}))
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)

local notation "fast" => W.map (D.filtration.associatedGradedMap Fmark φ hφ)
local notation "gmark" => Fmark.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J) marked
local notation "Z" => Fmark.realPolynomialSymbolHom bF ν hF (fullTaggedVariableWeight J) gmark
local notation "countConstants" => (fun n => fullChartStageCountConstant (n + 1) 254)

theorem exists_early_forward_terminal_of_zero_restricted_native_common_factors
    [Fintype (SymbolBasisIndex (fun _ : LayerSamplerVariables G I n B => 1) ω)]
    [Fintype (SymbolBasisIndex (fun _ : LayerSamplerVariables G I n B => 1) ν)]
    [∀ r, Fintype (SymbolBasisIndex (fun _ : {i : LayerSamplerVariables G I n B // keep r i} => 1) ω)]
    [∀ r, Fintype (SymbolBasisIndex (fun _ : {i : LayerSamplerVariables G I n B // keep r i} => 1) ν)]
    [∀ r, TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [∀ r, IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [∀ r, ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [∀ r, T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    (v : γ → D.filtration.AssociatedGraded)
    (hv : span ℚ (Set.range v) = W.toSubmodule)
    (hW : BasisGradedSubmodule (D.filtration.associatedGradedBasis bD ω hD) ω W.toSubmodule)
    (pGeometry Rrank : ℝ) (Hbr : ℕ)
    (hpGeometry : 0 ≤ pGeometry)
    (hιGeometry : (Fintype.card ι : ℝ) ≤ pGeometry)
    (hκGeometry : (Fintype.card κ : ℝ) ≤ pGeometry)
    (hγGeometry : (Fintype.card γ : ℝ) ≤ pGeometry)
    (hsamplerGeometry : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pGeometry)
    (hvGeometry : ∀ a i, rationalLogHeight
      ((D.filtration.associatedGradedBasis bD ω hD).repr (v a) i) ≤ pGeometry)
    (scheduleExponent : ℕ) (x gainLog stageLog : ℝ)
    (hx : 0 ≤ x) (hgain : gainLog ∈ Set.Icc 0 x) (hstage : stageLog ∈ Set.Icc 0 x)
    (Cprimitive Csource : ℕ) (sourceNative pTest α : ℕ → ℝ)
    (hSourceNonneg : ∀ r < s, 0 ≤ sourceNative r)
    (hSourceBound : ∀ r < s, sourceNative r ≤
      (preparedFiniteForwardSourcePrecision scheduleExponent countConstants r x gainLog stageLog +
        preparedFiniteForwardWork scheduleExponent countConstants r x + Csource) ^ Csource)
    (hBaseExponent : allocatedCandidateStageBaseExponent s m Cprimitive ≤ scheduleExponent)
    (hphaseExponent : ∀ r < s,
      allocatedCandidateCompositePhaseConstant s m 1
        (allocatedCandidatePromotedMajorConstant Csource) r ≤ scheduleExponent)
    (hCprimitive : 1 ≤ Cprimitive)
    (hGeometryBase : allocatedCandidateCommonFastBudget s pGeometry ≤ x)
    (hHbr : 1 ≤ Hbr)
    (hTagsBase : (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ x)
    (hmEarly : (m : ℝ) ≤ x)
    (hblocksEarly : ((s * (Fintype.card κ * m) : ℕ) : ℝ) ≤ x)
    (hHbrBase : (Hbr : ℝ) ≤ Real.exp x)
    (hcost : cost ≤ (x + Cprimitive) ^ Cprimitive)
    (HMap l : ℕ) (qNative : ℝ)
    (hHMap : 1 ≤ HMap) (hl : 0 < l)
    (hHMapGeometry : (HMap : ℝ) ≤ Real.exp pGeometry)
    (hlExp : (l : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive))
    (hqNative : qNative ≤ (x + Cprimitive) ^ Cprimitive)
    (hentries : ∀ i j, RationalHeightLE (bF.repr (φ (bD j)) i) HMap)
    (hbracket : ∀ i j z, RationalHeightLE (bF.repr ⁅bF i, bF j⁆ z) Hbr)
    (initialLong : LayerSamplerVariables G I n B → Prop)
    (hstageLong : ∀ r < s, ∀ i, keep r i → initialLong i)
    (hOriginal : ∀ z : P.productive, D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : {i // initialLong i} => (A.sides i.val : ℝ)) qNative l W
      (D.filtration.weightedAdaptedRealChartHom (fun _ : (P.chart z).Variables => 1)
        (fun _ : {i // initialLong i} => 1)
        ((P.chart z).axisPolynomial initialLong (fun _ => 0))
        ((P.chart z).axisPolynomial_support initialLong (fun _ => 0))
        (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
          (P.candidate z).orbit)))
    (hτ : τ ≤ 1) (hξ : ξ ≤ 1) (hσone : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ 1 / 8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hkept : ∀ r, ∀ i, keep r i → Real.exp (allocatedCandidateStageSlice s m Cprimitive
      (preparedFiniteForwardParameter scheduleExponent countConstants r x)) ≤ (A.sides i : ℝ))
    (hfrozen : ∀ r, ∀ i, ¬keep r i → (A.sides i : ℝ) ≤ Real.exp (allocatedCandidateStageSlice s m Cprimitive
      (preparedFiniteForwardParameter scheduleExponent countConstants r x)))
    (hTest : ∀ r < s, OrdinaryPolynomialPhase.budget r ≤ pTest r)
    (hα : ∀ r < s, α r ≤ (9 / 10 : ℝ) * massThreshold)
    (hdirect : ∀ r < s, A.NativeDetection r (allocatedCandidateStageSlice s m Cprimitive
      (preparedFiniteForwardParameter scheduleExponent countConstants r x)) (pTest r) (sourceNative r) (α r))
    (hN : ∀ i, Real.exp (preparedFiniteForwardCumulative scheduleExponent countConstants s x) ≤ (N i : ℝ))
    (hRrank : Real.exp (preparedFiniteForwardCumulative scheduleExponent countConstants s x) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j)) :
    ∃ (qDim : ℕ) (hdim : qDim ≤ Fintype.card κ)
      (eQ : Basis (Fin qDim) ℚ (Fmark.AssociatedGraded ⧸ (fast).toSubmodule))
      (lift : (Fmark.AssociatedGraded ⧸ (fast).toSubmodule) →ₗ[ℚ] Fmark.AssociatedGraded),
    BasisGradedSubmodule (Fmark.associatedGradedBasis bF ν hF) ν (fast).toSubmodule ∧
    Function.RightInverse lift (fast).toSubmodule.mkQ ∧
    let hηBase : (Fintype.card (Fin qDim) : ℝ) ≤ x := by
      simpa only [Fintype.card_fin] using (Nat.cast_le.mpr hdim).trans (hκGeometry.trans
        ((allocatedCandidateCommonFastBudget_bounds s hpGeometry).2.2.trans hGeometryBase))
    let hblocks : ((s * (Fintype.card (Fin qDim) * m) : ℕ) : ℝ) ≤ x := by
      simpa only [Fintype.card_fin] using
        (Nat.cast_le.mpr (Nat.mul_le_mul_left s (Nat.mul_le_mul_right m hdim))).trans hblocksEarly
    let hXEarly : (Fintype.card X : ℝ) ≤ x := by
      have hsum : (Fintype.card X : ℝ) + (Fintype.card (Σ j, J j) : ℝ) ≤ x := by
        simpa only [Fintype.card_sum, Nat.cast_add] using hTagsBase
      exact (le_add_of_nonneg_right (Nat.cast_nonneg _)).trans hsum
    let hJEarly : (Fintype.card (Σ j, J j) : ℝ) ≤ x := by
      have hsum : (Fintype.card X : ℝ) + (Fintype.card (Σ j, J j) : ℝ) ≤ x := by
        simpa only [Fintype.card_sum, Nat.cast_add] using hTagsBase
      exact (le_add_of_nonneg_left (Nat.cast_nonneg _)).trans hsum
    let hNEarly : ∀ i, 1 ≤ N i := by
      intro i
      have hpos : 0 < N i := by
        exact_mod_cast ((Real.exp_pos _).trans_le (hN i))
      exact Nat.succ_le_iff.mpr hpos
    let T := CertifiedFullChartFiniteHistory.earlyForwardBranchTree
      Fmark bF ν hF J (fast).toSubmodule (eQ.baseChange ℝ) lift Z U poly N
      s scheduleExponent x hx hXEarly hmEarly hJEarly hηBase hblocks
      (fun j ex _ => hm j ex) hNEarly
    ∃ history ∈ T.level s,
      FullChartControlledFactors Fmark bF ν hF J poly N history.outer.1 history.outer.2
        (preparedFiniteForwardWork scheduleExponent countConstants s x) ∧
      RationalTaggedConstraintCertificate J Set.univ history.K
        (preparedFiniteForwardCumulative scheduleExponent countConstants s x)
        (s * (Fintype.card (Fin qDim) * m)) ∧
      ∀ point ∈ history.K,
        eval₂ point (Fmark.realGradedSymbolPolynomial bF ν hF (fullTaggedVariableWeight J)
          (history.outer.1⁻¹ * Z * history.outer.2⁻¹).coord) ∈
            (fast).toSubmodule.baseChange ℝ := by
  classical
  have hpGeometryX : pGeometry ≤ x :=
    (allocatedCandidateCommonFastBudget_bounds s hpGeometry).2.2.trans hGeometryBase
  have hGeomX : allocatedCandidateCommonFastGeometryLog pGeometry ≤ x :=
    (allocatedCandidateCommonFastBudget_bounds s hpGeometry).1.trans hGeometryBase
  have hprimitive : x ≤ (x + Cprimitive) ^ Cprimitive := by
    have hC : (1 : ℝ) ≤ Cprimitive := by exact_mod_cast hCprimitive
    have hbase : 1 ≤ x + Cprimitive := by linarith
    exact (le_add_of_nonneg_right (Nat.cast_nonneg Cprimitive)).trans
      (by simpa only [pow_one] using pow_le_pow_right₀ hbase hCprimitive)
  have hκBase : (Fintype.card κ : ℝ) ≤ x := hκGeometry.trans hpGeometryX
  have hκ : (Fintype.card κ : ℝ) ≤ (x + Cprimitive) ^ Cprimitive := hκBase.trans hprimitive
  have htags : (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤
      (x + Cprimitive) ^ Cprimitive := hTagsBase.trans hprimitive
  have hsampler : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤
      (x + Cprimitive) ^ Cprimitive := (hsamplerGeometry.trans hpGeometryX).trans hprimitive
  have hsymbolPower : (pGeometry + (s + 3)) ^ (s + 3) ≤ pointwiseFastSectionInput s pGeometry := by
    have hnonneg : 0 ≤ (pGeometry + (s + 3)) ^ (s + 3) := by positivity
    unfold pointwiseFastSectionInput
    nlinarith only [hnonneg, sq_nonneg ((pGeometry + (s + 3)) ^ (s + 3)), hpGeometry]
  have hsymbolBase : (pGeometry + (s + 3)) ^ (s + 3) ≤ (x + Cprimitive) ^ Cprimitive :=
    ((hsymbolPower.trans (allocatedCandidateCommonFastBudget_bounds s hpGeometry).2.1).trans
      hGeometryBase).trans hprimitive
  have hsource : (Fintype.card (SymbolBasisIndex
      (fun _ : LayerSamplerVariables G I n B => 1) ω) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive :=
    (D.filtration.symbolBasisIndex_card_le_spanning_budget bD ω hD _ (fun _ => Nat.zero_lt_one)
      hpGeometry hιGeometry hsamplerGeometry).trans hsymbolBase
  have htarget : (Fintype.card (SymbolBasisIndex
      (fun _ : LayerSamplerVariables G I n B => 1) ν) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive :=
    (Fmark.symbolBasisIndex_card_le_spanning_budget bF ν hF _ (fun _ => Nat.zero_lt_one)
      hpGeometry hκGeometry hsamplerGeometry).trans hsymbolBase
  have hJ (j : Fin m) : (Fintype.card (J j) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive := by
    have hinj : Function.Injective (fun z : J j => (Sum.inr ⟨j, z⟩ : X ⊕ (Σ j, J j))) := by
      intro a b hab
      exact eq_of_heq (Sigma.mk.inj (Sum.inr.inj hab)).2
    exact (Nat.cast_le.mpr (Fintype.card_le_of_injective _ hinj)).trans htags
  have hφGeometry (i : ι) (j : κ) : rationalLogHeight (bF.repr (φ (bD i)) j) ≤ pGeometry :=
    rationalLogHeight_le_of_height (hentries j i) hHMapGeometry
  obtain ⟨qDim, hdim, eQ, lift, qS, hfast, hsection, _hsectionReal, hqS,
      hqSBound, hentry, hgrid, hθ, _hHθ, hHθBound⟩ :=
    D.filtration.exists_allocatedCandidateCommonFastGeometry Fmark φ hφ bD ω hD bF ν hF
      W v hv hW hpGeometry hιGeometry hκGeometry hγGeometry hvGeometry hφGeometry
  refine ⟨qDim, hdim, eQ, lift, hfast, hsection, ?_⟩
  intro hηBase hblocks hXEarly hJEarly hNEarly T
  let Hfast : ℕ := ⌈Real.exp ((pGeometry + 2) ^ 4)⌉₊
  let H : ℕ := max Hbr Hfast
  have hH : 1 ≤ H := hHbr.trans (Nat.le_max_left _ _)
  have hHfastBound : (Hfast : ℝ) ≤ Real.exp x :=
    (allocatedCandidateCommonFastGeneratorHeight_le hpGeometry).trans (Real.exp_le_exp.mpr hGeomX)
  have hHBound : (H : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive) := by
    have hmax : (H : ℝ) ≤ Real.exp x := by
      simpa only [H, Nat.cast_max] using max_le hHbrBase hHfastBound
    exact hmax.trans (Real.exp_le_exp.mpr hprimitive)
  have hHMapBound : (HMap : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive) :=
    hHMapGeometry.trans (Real.exp_le_exp.mpr (hpGeometryX.trans hprimitive))
  have hstructure (i j z : κ) : RationalHeightLE
      ((Fmark.associatedGradedBasis bF ν hF).repr
        ⁅Fmark.associatedGradedBasis bF ν hF i, Fmark.associatedGradedBasis bF ν hF j⁆ z) Hbr := by
    rw [Fmark.associatedGradedBasis_bracket]
    split_ifs
    · exact hbracket i j z
    · exact rationalHeightLE_zero hHbr
  let fastGenerators := D.filtration.gradedImageSpanningFamily Fmark φ hφ v
  have hfastSpan : span ℚ (Set.range fastGenerators) = (fast).toSubmodule :=
    D.filtration.gradedImageSpanningFamily_span Fmark φ hφ W v hv
  have hfastHeight (a : γ) (i : κ) : RationalHeightLE
      ((Fmark.associatedGradedBasis bF ν hF).repr (fastGenerators a) i) H := by
    apply (rationalHeightLE_ceil_exp
      (D.filtration.gradedImageSpanningFamily_logHeight Fmark φ hφ bD ω hD bF ν hF v
        hpGeometry hιGeometry hvGeometry hφGeometry a i)).mono
    exact Nat.le_max_right _ _
  have hgeneratorCount :
      ((Fintype.card (SymbolBasisIndex (fun _ : LayerSamplerVariables G I n B => 1) ν) *
        Fintype.card γ : ℕ) : ℝ) ≤ (x + Cprimitive) ^ Cprimitive := by
    have hcount := Fmark.pointwiseSpanningIndex_card_le (γ := γ) bF ν hF
      (fun _ : LayerSamplerVariables G I n B => 1) (fun _ => Nat.zero_lt_one)
      hpGeometry hκGeometry hγGeometry hsamplerGeometry
    apply (show _ ≤ pointwiseFastSectionInput s pGeometry by
      simpa only [Fintype.card_prod, Nat.cast_mul] using hcount).trans
    exact ((allocatedCandidateCommonFastBudget_bounds s hpGeometry).2.1.trans hGeometryBase).trans hprimitive
  exact P.exists_early_forward_terminal_of_zero_restricted_fast_generators keep bD ω hD bF ν hF hφ W
    eQ lift hfast hsection (Real.exp (allocatedCandidateCommonFastGeometryLog pGeometry))
    Rrank Hbr qS scheduleExponent x gainLog stageLog hx hgain hstage Cprimitive Csource
    sourceNative pTest α hSourceNonneg hSourceBound hBaseExponent hphaseExponent hHbr hqS
    hκBase hTagsBase hηBase hmEarly hblocks hHbrBase
    (hqSBound.trans (Real.exp_le_exp.mpr hGeomX)) (Real.exp_le_exp.mpr hGeomX)
    hstructure hentry hgrid hcost HMap l H (allocatedCandidateCommonFastCoordinateHeight pGeometry)
    qNative hHMap hl hH hHMapBound hlExp hHBound
    (hHθBound.trans (Real.exp_le_exp.mpr (hGeomX.trans hprimitive))) hqNative hentries
    hsource htarget hκ htags hsampler hJ
    (fun i j z => (hbracket i j z).mono (Nat.le_max_left _ _))
    fastGenerators hfastSpan hfastHeight hgeneratorCount hθ initialLong hstageLong hOriginal hτ hξ hσone Cgeo hCgeo
    hchart hsmall hpoly hkept hfrozen hTest hα hdirect hN hRrank hrank

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
