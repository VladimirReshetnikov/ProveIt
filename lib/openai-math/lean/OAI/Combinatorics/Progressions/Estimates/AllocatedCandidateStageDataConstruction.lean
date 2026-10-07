import OAI.Combinatorics.Progressions.Dynamics.AllocatedCandidateNativeMajorBudget
import OAI.Combinatorics.Progressions.Dynamics.AllocatedCandidateStageScalarBudget
import OAI.Combinatorics.Progressions.Dynamics.AllocatedNativeDetectionBudgetMonotonicity
import OAI.Combinatorics.Progressions.Nilpotent.AllocatedCandidateHistoryLocalNiltests

namespace OAI

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
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P.productive, (P.chart z).keep = keep)
    {ι κ χ η : Type} [Fintype ι] [Fintype κ] [Fintype χ] [Fintype η]
    (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = span ℚ (bD '' {i | j ≤ ω i}))
    (bF : Basis κ ℚ M) (ν : κ → ℕ)
    (hF : ∀ j, Fmark.layer j = span ℚ (bF '' {i | j ≤ ν i}))
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)

local notation "Vars" => {i : LayerSamplerVariables G I n B // keep i}
local notation "fast" => W.map (D.filtration.associatedGradedMap Fmark φ hφ)
local notation "gmark" => Fmark.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J) marked
local notation "Z" => Fmark.realPolynomialSymbolHom bF ν hF (fullTaggedVariableWeight J) gmark
local notation "Q" => P.withKeep keep hkeep

theorem exists_history_full_chart_major_correlation_witness
    [Fintype (SymbolBasisIndex (fun _ : Vars => 1) ω)]
    [Fintype (SymbolBasisIndex (fun _ : Vars => 1) ν)]
    (eQ : Basis η ℚ (Fmark.AssociatedGraded ⧸ (fast).toSubmodule))
    (lift : (Fmark.AssociatedGraded ⧸ (fast).toSubmodule) →ₗ[ℚ] Fmark.AssociatedGraded)
    (r a : ℕ) (hr : r ≤ s)
    [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    (Bhistory Bstage budget : ℝ)
    (history : CertifiedFullChartFiniteHistory Fmark bF ν hF J (fast).toSubmodule
      (eQ.baseChange ℝ) lift Z Set.univ U poly N Bhistory r)
    (hcontrol : FullChartControlledFactors Fmark bF ν hF J poly N history.outer.1 history.outer.2 budget)
    (hcertificate : RationalTaggedConstraintCertificate J Set.univ history.K Bstage
      (r * (Fintype.card η * m)))
    (HMap l : ℕ) (pMap : ℝ) (hHMap : 1 ≤ HMap) (hl : 0 < l) (hpMap : 0 ≤ pMap)
    (hentries : ∀ i j, RationalHeightLE (bF.repr (φ (bD j)) i) HMap)
    (hsource : (Fintype.card (SymbolBasisIndex (fun _ : Vars => 1) ω) : ℝ) ≤ pMap)
    (htarget : (Fintype.card (SymbolBasisIndex (fun _ : Vars => 1) ν) : ℝ) ≤ pMap)
    (hHMapExp : (HMap : ℝ) ≤ Real.exp pMap) (hlExp : (l : ℝ) ≤ Real.exp pMap)
    (H : ℕ) (p qNative : ℝ) (hH : 1 ≤ H) (hp : 0 ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hVars : (Fintype.card Vars : ℝ) ≤ p)
    (hχ : (Fintype.card χ : ℝ) ≤ p) (hHExp : (H : ℝ) ≤ Real.exp p)
    (hbracket : ∀ i j z, RationalHeightLE (bF.repr ⁅bF i, bF j⁆ z) H)
    (hcommon : Real.exp budget * Real.exp ((pMap + 2) ^ 4) ≤ Real.exp p)
    (hmapSlow : Real.exp ((pMap + 2) ^ 3 + qNative) ≤ Real.exp ((p + 2) ^ a))
    (hallowance :
      (((s : ℝ) + 1) * ((Fintype.card (X ⊕ (Σ j, J j)) : ℝ) + 1) ^ s * Real.exp budget *
        (((m + 1 : ℕ) : ℝ) * ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m) ^ s)
        ≤ Real.exp ((p + 2) ^ a))
    (hNreset : ∀ i : Vars, Real.exp ((p + allocatedFrozenCurrentGradeResetConstant s a) ^
      allocatedFrozenCurrentGradeResetConstant s a) ≤ (A.sides i.val : ℝ))
    (vg : χ → Fmark.PolynomialSymbol (fun _ : Vars => 1))
    (hspan : span ℚ (Set.range vg) = (Fmark.symbolPointwiseSubalgebra bF ν hF (fun _ : Vars => 1) fast).toSubmodule)
    (hvg : ∀ i z, RationalHeightLE ((Fmark.polynomialSymbolBasis bF ν hF (fun _ : Vars => 1)).repr (vg i) z) H)
    (hτ : τ ≤ 1) (hξ : ξ ≤ 1) (hσone : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ 1 / 8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (pK Mbound LongSide : ℝ) (hpK : 0 ≤ pK) (hBstage : Bstage ≤ pK)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ pK) (hM : 0 ≤ Mbound)
    (hcap : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ Mbound)
    (hLong : 1 ≤ LongSide) (hlong : ∀ i, keep i → LongSide ≤ layerSamplerBox B U btag S i)
    (hthreshold : Real.exp ((pK + 2) ^ 9) ^ 2 * Mbound < LongSide)
    (hNinterpolate : ∀ i : Vars, Real.exp (cost + (s : ℝ) + 1) ≤ (A.sides i.val : ℝ))
    (hfactor : ∀ z : P.productive, D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : Vars => (A.sides i.val : ℝ)) qNative l W
      (D.filtration.realification.polynomialOrbitCoordinates _ ((Q).candidate z).orbit))
    (Hθ : ℕ) (pLocal : ℝ)
    (hθ : ∀ j i, RationalHeightLE (((eQ.coord j).comp (fast).toSubmodule.mkQ)
      (Fmark.associatedGradedBasis bF ν hF i)) Hθ)
    (hpLocal : 1 ≤ pLocal) (hLocalDim : (Fintype.card Vars : ℝ) ≤ pLocal)
    (hLocalSize : (Fintype.card κ : ℝ) * Hθ * Real.exp
      ((p + allocatedFrozenCurrentGradeResetConstant s a) ^ allocatedFrozenCurrentGradeResetConstant s a) ≤ Real.exp pLocal)
    (hLocalDen : ((Hθ ^ Fintype.card κ : ℕ) : ℝ) * Real.exp
      ((p + allocatedFrozenCurrentGradeResetConstant s a) ^ allocatedFrozenCurrentGradeResetConstant s a) ≤ Real.exp pLocal)
    (hNLocal : ∀ i : Vars, Real.exp ((pLocal + (r + 401 : ℕ)) ^ (r + 401)) ≤ (A.sides i.val : ℝ))
    (pSlice pTest pNative pMajor Rrank : ℝ) (C : ℕ)
    (hpNative : 2 ≤ pNative) (hη : (Fintype.card η : ℝ) ≤ pNative)
    (hNativeMajor : pNative ≤ pMajor) (hproduct : productNiltestBudget pNative ≤ pMajor)
    (hdim : ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ pMajor)
    (hNmajor : ∀ i, Real.exp ((pMajor + C) ^ C) ≤ (N i : ℝ))
    (hRrank : Real.exp ((pMajor + C) ^ C) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (Bshort : ℝ) (hBshort : 1 ≤ Bshort)
    (hshort : ∀ i, ¬keep i → (A.sides i : ℝ) ≤ Bshort)
    (α : ℝ) (hα : α ≤ (9 / 10 : ℝ) * massThreshold)
    (hdirect : A.NativeDetection r pSlice pTest pNative α)
    (hslice : max ((pLocal + (r + 401 : ℕ)) ^ (r + 401)) (Real.log Bshort) ≤ pSlice)
    (htest : OrdinaryPolynomialPhase.budget r ≤ pTest) :
    Nonempty (FullChartMajorCorrelationWitness Fmark bF ν hF J (r + 1)
      (fast).toSubmodule (eQ.baseChange ℝ) Z history.outer.1 history.outer.2
      N poly U pMajor Rrank C) := by
  have hlength : ∀ z : P.productive, ∀ i, s < ((Q).chart z).slice.length i :=
    fun z => ((Q).chart z).degree_lt_slice_length s hNinterpolate
  obtain ⟨reset, _, _, hlocal⟩ :=
    P.exists_history_current_grade_local_niltests keep hkeep bD ω hD bF ν hF hφ W
      eQ lift r a hr Bhistory Bstage budget history hcontrol hcertificate
      HMap l pMap hHMap hl hpMap hentries hsource htarget hHMapExp hlExp
      H p qNative hH hp hκ hVars hχ hHExp hbracket hcommon hmapSlow hallowance
      hNreset vg hspan hvg hτ hξ hσone Cgeo hCgeo hchart hsmall hpoly
      pK Mbound LongSide hpK hBstage hJ hM hcap hLong hlong hthreshold hlength hfactor
      Hθ pLocal hθ hpLocal hLocalDim hLocalSize hLocalDen hNLocal
  have hpLocal0 : 0 ≤ pLocal := le_trans (by norm_num) hpLocal
  apply exists_allocated_full_chart_major_correlation_witness_of_frozen_local_niltests
    A Fmark bF ν hF (fast).toSubmodule (eQ.baseChange ℝ) Z history.outer.1 history.outer.2
    (by omega) hpoly
    (fun i => (P.centerLift (lowTaggedIndex J (r + 1) i).1).val (lowTaggedIndex J (r + 1) i).2)
    pSlice pTest pNative pMajor Rrank C hpNative hη hNativeMajor hproduct hdim
    hNmajor hRrank hrank (fun _ => P.productive) keep
    ((pLocal + (r + 401 : ℕ)) ^ (r + 401)) Bshort (by positivity) hBshort hshort hξ
    α (fun _ => hα.trans (mul_le_mul_of_nonneg_left P.mass (by norm_num)))
    hdirect hslice htest (fun _ _ => Hθ ^ Fintype.card κ * reset) (fun _ _ _ => 0)
  intro j z hz
  let zz : P.productive := ⟨z, hz⟩
  exact ⟨((Q).chart zz).fixed, ((Q).chart zz).fixed_in_box, hlocal j zz (fun _ => 0)⟩

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
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P.productive, (P.chart z).keep = keep)
    {ι κ χ η : Type} [Fintype ι] [Fintype κ] [Fintype χ] [Fintype η]
    (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = span ℚ (bD '' {i | j ≤ ω i}))
    (bF : Basis κ ℚ M) (ν : κ → ℕ)
    (hF : ∀ j, Fmark.layer j = span ℚ (bF '' {i | j ≤ ν i}))
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)

local notation "Vars" => {i : LayerSamplerVariables G I n B // keep i}
local notation "fast" => W.map (D.filtration.associatedGradedMap Fmark φ hφ)
local notation "gmark" => Fmark.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J) marked
local notation "Z" => Fmark.realPolynomialSymbolHom bF ν hF (fullTaggedVariableWeight J) gmark
local notation "Q" => P.withKeep keep hkeep

theorem exists_history_full_chart_major_correlation_witness_of_lengths
    [Fintype (SymbolBasisIndex (fun _ : Vars => 1) ω)]
    [Fintype (SymbolBasisIndex (fun _ : Vars => 1) ν)]
    (eQ : Basis η ℚ (Fmark.AssociatedGraded ⧸ (fast).toSubmodule))
    (lift : (Fmark.AssociatedGraded ⧸ (fast).toSubmodule) →ₗ[ℚ] Fmark.AssociatedGraded)
    (r a : ℕ) (hr : r ≤ s)
    [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    (Bhistory Bstage budget : ℝ)
    (history : CertifiedFullChartFiniteHistory Fmark bF ν hF J (fast).toSubmodule
      (eQ.baseChange ℝ) lift Z Set.univ U poly N Bhistory r)
    (hcontrol : FullChartControlledFactors Fmark bF ν hF J poly N history.outer.1 history.outer.2 budget)
    (hcertificate : RationalTaggedConstraintCertificate J Set.univ history.K Bstage
      (r * (Fintype.card η * m)))
    (HMap l : ℕ) (pMap : ℝ) (hHMap : 1 ≤ HMap) (hl : 0 < l) (hpMap : 0 ≤ pMap)
    (hentries : ∀ i j, RationalHeightLE (bF.repr (φ (bD j)) i) HMap)
    (hsource : (Fintype.card (SymbolBasisIndex (fun _ : Vars => 1) ω) : ℝ) ≤ pMap)
    (htarget : (Fintype.card (SymbolBasisIndex (fun _ : Vars => 1) ν) : ℝ) ≤ pMap)
    (hHMapExp : (HMap : ℝ) ≤ Real.exp pMap) (hlExp : (l : ℝ) ≤ Real.exp pMap)
    (H : ℕ) (p qNative : ℝ) (hH : 1 ≤ H) (hp : 0 ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hVars : (Fintype.card Vars : ℝ) ≤ p)
    (hχ : (Fintype.card χ : ℝ) ≤ p) (hHExp : (H : ℝ) ≤ Real.exp p)
    (hbracket : ∀ i j z, RationalHeightLE (bF.repr ⁅bF i, bF j⁆ z) H)
    (hcommon : Real.exp budget * Real.exp ((pMap + 2) ^ 4) ≤ Real.exp p)
    (hmapSlow : Real.exp ((pMap + 2) ^ 3 + qNative) ≤ Real.exp ((p + 2) ^ a))
    (hallowance :
      (((s : ℝ) + 1) * ((Fintype.card (X ⊕ (Σ j, J j)) : ℝ) + 1) ^ s * Real.exp budget *
        (((m + 1 : ℕ) : ℝ) * ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m) ^ s)
        ≤ Real.exp ((p + 2) ^ a))
    (hNreset : ∀ i : Vars, Real.exp ((p + allocatedFrozenCurrentGradeResetConstant s a) ^
      allocatedFrozenCurrentGradeResetConstant s a) ≤ (A.sides i.val : ℝ))
    (vg : χ → Fmark.PolynomialSymbol (fun _ : Vars => 1))
    (hspan : span ℚ (Set.range vg) = (Fmark.symbolPointwiseSubalgebra bF ν hF (fun _ : Vars => 1) fast).toSubmodule)
    (hvg : ∀ i z, RationalHeightLE ((Fmark.polynomialSymbolBasis bF ν hF (fun _ : Vars => 1)).repr (vg i) z) H)
    (hτ : τ ≤ 1) (hξ : ξ ≤ 1) (hσone : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ 1 / 8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (pK Mbound LongSide : ℝ) (hpK : 0 ≤ pK) (hBstage : Bstage ≤ pK)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ pK) (hM : 0 ≤ Mbound)
    (hcap : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ Mbound)
    (hLong : 1 ≤ LongSide) (hlong : ∀ i, keep i → LongSide ≤ layerSamplerBox B U btag S i)
    (hthreshold : Real.exp ((pK + 2) ^ 9) ^ 2 * Mbound < LongSide)
    (hlength : ∀ z : P.productive, ∀ i, s < ((Q).chart z).slice.length i)
    (hfactor : ∀ z : P.productive, D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : Vars => (A.sides i.val : ℝ)) qNative l W
      (D.filtration.realification.polynomialOrbitCoordinates _ ((Q).candidate z).orbit))
    (Hθ : ℕ) (pLocal : ℝ)
    (hθ : ∀ j i, RationalHeightLE (((eQ.coord j).comp (fast).toSubmodule.mkQ)
      (Fmark.associatedGradedBasis bF ν hF i)) Hθ)
    (hpLocal : 1 ≤ pLocal) (hLocalDim : (Fintype.card Vars : ℝ) ≤ pLocal)
    (hLocalSize : (Fintype.card κ : ℝ) * Hθ * Real.exp
      ((p + allocatedFrozenCurrentGradeResetConstant s a) ^ allocatedFrozenCurrentGradeResetConstant s a) ≤ Real.exp pLocal)
    (hLocalDen : ((Hθ ^ Fintype.card κ : ℕ) : ℝ) * Real.exp
      ((p + allocatedFrozenCurrentGradeResetConstant s a) ^ allocatedFrozenCurrentGradeResetConstant s a) ≤ Real.exp pLocal)
    (hNLocal : ∀ i : Vars, Real.exp ((pLocal + (r + 401 : ℕ)) ^ (r + 401)) ≤ (A.sides i.val : ℝ))
    (pSlice pTest pNative pMajor Rrank : ℝ) (C : ℕ)
    (hpNative : 2 ≤ pNative) (hη : (Fintype.card η : ℝ) ≤ pNative)
    (hNativeMajor : pNative ≤ pMajor) (hproduct : productNiltestBudget pNative ≤ pMajor)
    (hdim : ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ pMajor)
    (hNmajor : ∀ i, Real.exp ((pMajor + C) ^ C) ≤ (N i : ℝ))
    (hRrank : Real.exp ((pMajor + C) ^ C) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (Bshort : ℝ) (hBshort : 1 ≤ Bshort)
    (hshort : ∀ i, ¬keep i → (A.sides i : ℝ) ≤ Bshort)
    (α : ℝ) (hα : α ≤ (9 / 10 : ℝ) * massThreshold)
    (hdirect : A.NativeDetection r pSlice pTest pNative α)
    (hslice : max ((pLocal + (r + 401 : ℕ)) ^ (r + 401)) (Real.log Bshort) ≤ pSlice)
    (htest : OrdinaryPolynomialPhase.budget r ≤ pTest) :
    Nonempty (FullChartMajorCorrelationWitness Fmark bF ν hF J (r + 1)
      (fast).toSubmodule (eQ.baseChange ℝ) Z history.outer.1 history.outer.2
      N poly U pMajor Rrank C) := by
  obtain ⟨reset, _, _, hlocal⟩ :=
    P.exists_history_current_grade_local_niltests keep hkeep bD ω hD bF ν hF hφ W
      eQ lift r a hr Bhistory Bstage budget history hcontrol hcertificate
      HMap l pMap hHMap hl hpMap hentries hsource htarget hHMapExp hlExp
      H p qNative hH hp hκ hVars hχ hHExp hbracket hcommon hmapSlow hallowance
      hNreset vg hspan hvg hτ hξ hσone Cgeo hCgeo hchart hsmall hpoly
      pK Mbound LongSide hpK hBstage hJ hM hcap hLong hlong hthreshold hlength hfactor
      Hθ pLocal hθ hpLocal hLocalDim hLocalSize hLocalDen hNLocal
  have hpLocal0 : 0 ≤ pLocal := le_trans (by norm_num) hpLocal
  apply exists_allocated_full_chart_major_correlation_witness_of_frozen_local_niltests
    A Fmark bF ν hF (fast).toSubmodule (eQ.baseChange ℝ) Z history.outer.1 history.outer.2
    (by omega) hpoly
    (fun i => (P.centerLift (lowTaggedIndex J (r + 1) i).1).val (lowTaggedIndex J (r + 1) i).2)
    pSlice pTest pNative pMajor Rrank C hpNative hη hNativeMajor hproduct hdim
    hNmajor hRrank hrank (fun _ => P.productive) keep
    ((pLocal + (r + 401 : ℕ)) ^ (r + 401)) Bshort (by positivity) hBshort hshort hξ
    α (fun _ => hα.trans (mul_le_mul_of_nonneg_left P.mass (by norm_num)))
    hdirect hslice htest (fun _ _ => Hθ ^ Fintype.card κ * reset) (fun _ _ _ => 0)
  intro j z hz
  let zz : P.productive := ⟨z, hz⟩
  exact ⟨((Q).chart zz).fixed, ((Q).chart zz).fixed_in_box, hlocal j zz (fun _ => 0)⟩

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
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P.productive, (P.chart z).keep = keep)
    {ι κ χ η : Type} [Fintype ι] [Fintype κ] [Fintype χ] [Fintype η]
    (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = span ℚ (bD '' {i | j ≤ ω i}))
    (bF : Basis κ ℚ M) (ν : κ → ℕ)
    (hF : ∀ j, Fmark.layer j = span ℚ (bF '' {i | j ≤ ν i}))
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)

local notation "Vars" => {i : LayerSamplerVariables G I n B // keep i}
local notation "fast" => W.map (D.filtration.associatedGradedMap Fmark φ hφ)
local notation "gmark" => Fmark.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J) marked
local notation "Z" => Fmark.realPolynomialSymbolHom bF ν hF (fullTaggedVariableWeight J) gmark
local notation "Q" => P.withKeep keep hkeep

structure HistoryStageData
    [instSymbolD : Fintype (SymbolBasisIndex (fun _ : Vars => 1) ω)]
    [instSymbolF : Fintype (SymbolBasisIndex (fun _ : Vars => 1) ν)]
    (eQ : Basis η ℚ (Fmark.AssociatedGraded ⧸ (fast).toSubmodule))
    (r a : ℕ)
    [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    (Bstage budget pMajor Rrank : ℝ) (C : ℕ) : Type where
  hr : r ≤ s
  HMap : ℕ
  l : ℕ
  pMap : ℝ
  hHMap : 1 ≤ HMap
  hl : 0 < l
  hpMap : 0 ≤ pMap
  hentries : ∀ i j, RationalHeightLE (bF.repr (φ (bD j)) i) HMap
  hsource : (Fintype.card (SymbolBasisIndex (fun _ : Vars => 1) ω) : ℝ) ≤ pMap
  htarget : (Fintype.card (SymbolBasisIndex (fun _ : Vars => 1) ν) : ℝ) ≤ pMap
  hHMapExp : (HMap : ℝ) ≤ Real.exp pMap
  hlExp : (l : ℝ) ≤ Real.exp pMap
  H : ℕ
  p : ℝ
  qNative : ℝ
  hH : 1 ≤ H
  hp : 0 ≤ p
  hκ : (Fintype.card κ : ℝ) ≤ p
  hVars : (Fintype.card Vars : ℝ) ≤ p
  hχ : (Fintype.card χ : ℝ) ≤ p
  hHExp : (H : ℝ) ≤ Real.exp p
  hbracket : ∀ i j z, RationalHeightLE (bF.repr ⁅bF i, bF j⁆ z) H
  hcommon : Real.exp budget * Real.exp ((pMap + 2) ^ 4) ≤ Real.exp p
  hmapSlow : Real.exp ((pMap + 2) ^ 3 + qNative) ≤ Real.exp ((p + 2) ^ a)
  hallowance :
      (((s : ℝ) + 1) * ((Fintype.card (X ⊕ (Σ j, J j)) : ℝ) + 1) ^ s * Real.exp budget *
        (((m + 1 : ℕ) : ℝ) * ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m) ^ s)
        ≤ Real.exp ((p + 2) ^ a)
  hNreset : ∀ i : Vars, Real.exp ((p + allocatedFrozenCurrentGradeResetConstant s a) ^
      allocatedFrozenCurrentGradeResetConstant s a) ≤ (A.sides i.val : ℝ)
  vg : χ → Fmark.PolynomialSymbol (fun _ : Vars => 1)
  hspan : span ℚ (Set.range vg) = (Fmark.symbolPointwiseSubalgebra bF ν hF (fun _ : Vars => 1) fast).toSubmodule
  hvg : ∀ i z, RationalHeightLE ((Fmark.polynomialSymbolBasis bF ν hF (fun _ : Vars => 1)).repr (vg i) z) H
  hτ : τ ≤ 1
  hξ : ξ ≤ 1
  hσone : ∀ j, σ j ≤ 1
  Cgeo : Fin m → ℝ
  hCgeo : ∀ j, 0 ≤ Cgeo j
  hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖
  hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ 1 / 8
  hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j)
  pK : ℝ
  Mbound : ℝ
  LongSide : ℝ
  hpK : 0 ≤ pK
  hBstage : Bstage ≤ pK
  hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ pK
  hM : 0 ≤ Mbound
  hcap : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ Mbound
  hLong : 1 ≤ LongSide
  hlong : ∀ i, keep i → LongSide ≤ layerSamplerBox B U btag S i
  hthreshold : Real.exp ((pK + 2) ^ 9) ^ 2 * Mbound < LongSide
  hlength : ∀ z : P.productive, ∀ i, s < ((Q).chart z).slice.length i
  hfactor : ∀ z : P.productive, D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : Vars => (A.sides i.val : ℝ)) qNative l W
      (D.filtration.realification.polynomialOrbitCoordinates _ ((Q).candidate z).orbit)
  Hθ : ℕ
  pLocal : ℝ
  hθ : ∀ j i, RationalHeightLE (((eQ.coord j).comp (fast).toSubmodule.mkQ)
      (Fmark.associatedGradedBasis bF ν hF i)) Hθ
  hpLocal : 1 ≤ pLocal
  hLocalDim : (Fintype.card Vars : ℝ) ≤ pLocal
  hLocalSize : (Fintype.card κ : ℝ) * Hθ * Real.exp
      ((p + allocatedFrozenCurrentGradeResetConstant s a) ^ allocatedFrozenCurrentGradeResetConstant s a) ≤ Real.exp pLocal
  hLocalDen : ((Hθ ^ Fintype.card κ : ℕ) : ℝ) * Real.exp
      ((p + allocatedFrozenCurrentGradeResetConstant s a) ^ allocatedFrozenCurrentGradeResetConstant s a) ≤ Real.exp pLocal
  hNLocal : ∀ i : Vars, Real.exp ((pLocal + (r + 401 : ℕ)) ^ (r + 401)) ≤ (A.sides i.val : ℝ)
  pSlice : ℝ
  pTest : ℝ
  pNative : ℝ
  hpNative : 2 ≤ pNative
  hη : (Fintype.card η : ℝ) ≤ pNative
  hNativeMajor : pNative ≤ pMajor
  hproduct : productNiltestBudget pNative ≤ pMajor
  hdim : ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ pMajor
  hNmajor : ∀ i, Real.exp ((pMajor + C) ^ C) ≤ (N i : ℝ)
  hRrank : Real.exp ((pMajor + C) ^ C) ≤ Rrank
  hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j)
  Bshort : ℝ
  hBshort : 1 ≤ Bshort
  hshort : ∀ i, ¬keep i → (A.sides i : ℝ) ≤ Bshort
  α : ℝ
  hα : α ≤ (9 / 10 : ℝ) * massThreshold
  hdirect : A.NativeDetection r pSlice pTest pNative α
  hslice : max ((pLocal + (r + 401 : ℕ)) ^ (r + 401)) (Real.log Bshort) ≤ pSlice
  htest : OrdinaryPolynomialPhase.budget r ≤ pTest

theorem historyStageData_majorWitness
    [instSymbolD : Fintype (SymbolBasisIndex (fun _ : Vars => 1) ω)]
    [instSymbolF : Fintype (SymbolBasisIndex (fun _ : Vars => 1) ν)]
    (eQ : Basis η ℚ (Fmark.AssociatedGraded ⧸ (fast).toSubmodule))
    (r a : ℕ)
    [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    (Bstage budget pMajor Rrank : ℝ) (C : ℕ)
    (data : HistoryStageData (χ := χ) (instSymbolD := instSymbolD) (instSymbolF := instSymbolF) (P := P) (keep := keep) (hkeep := hkeep)
      (bD := bD) (ω := ω) (hD := hD) (bF := bF) (ν := ν) (hF := hF) (hφ := hφ) (W := W)
      eQ r a Bstage budget pMajor Rrank C)
    (lift : (Fmark.AssociatedGraded ⧸ (fast).toSubmodule) →ₗ[ℚ] Fmark.AssociatedGraded)
    (Bhistory : ℝ)
    (history : CertifiedFullChartFiniteHistory Fmark bF ν hF J (fast).toSubmodule
      (eQ.baseChange ℝ) lift Z Set.univ U poly N Bhistory r)
    (hcontrol : FullChartControlledFactors Fmark bF ν hF J poly N history.outer.1 history.outer.2 budget)
    (hcertificate : RationalTaggedConstraintCertificate J Set.univ history.K Bstage
      (r * (Fintype.card η * m))) :
    Nonempty (FullChartMajorCorrelationWitness Fmark bF ν hF J (r + 1)
      (fast).toSubmodule (eQ.baseChange ℝ) Z history.outer.1 history.outer.2
      N poly U pMajor Rrank C) :=
  P.exists_history_full_chart_major_correlation_witness_of_lengths keep hkeep bD ω hD bF ν hF hφ W
    eQ lift r a data.hr Bhistory Bstage budget history hcontrol hcertificate
    data.HMap data.l data.pMap data.hHMap data.hl data.hpMap data.hentries data.hsource
    data.htarget data.hHMapExp data.hlExp data.H data.p data.qNative data.hH data.hp
    data.hκ data.hVars data.hχ data.hHExp data.hbracket data.hcommon data.hmapSlow
    data.hallowance data.hNreset data.vg data.hspan data.hvg data.hτ data.hξ data.hσone
    data.Cgeo data.hCgeo data.hchart data.hsmall data.hpoly data.pK data.Mbound data.LongSide
    data.hpK data.hBstage data.hJ data.hM data.hcap data.hLong data.hlong data.hthreshold
    data.hlength data.hfactor data.Hθ data.pLocal data.hθ data.hpLocal data.hLocalDim
    data.hLocalSize data.hLocalDen data.hNLocal data.pSlice data.pTest data.pNative pMajor
    Rrank C data.hpNative data.hη data.hNativeMajor data.hproduct data.hdim data.hNmajor
    data.hRrank data.hrank data.Bshort data.hBshort data.hshort data.α data.hα data.hdirect
    data.hslice data.htest

def historyStageData_lowerControlBudget
    [instSymbolD : Fintype (SymbolBasisIndex (fun _ : Vars => 1) ω)]
    [instSymbolF : Fintype (SymbolBasisIndex (fun _ : Vars => 1) ν)]
    (eQ : Basis η ℚ (Fmark.AssociatedGraded ⧸ (fast).toSubmodule))
    (r a : ℕ)
    [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    (Bstage budget pMajor Rrank : ℝ) (C : ℕ)
    (data : HistoryStageData (χ := χ) (instSymbolD := instSymbolD) (instSymbolF := instSymbolF) (P := P) (keep := keep) (hkeep := hkeep)
      (bD := bD) (ω := ω) (hD := hD) (bF := bF) (ν := ν) (hF := hF) (hφ := hφ) (W := W)
      eQ r a Bstage budget pMajor Rrank C)
    {budget' : ℝ} (hbudget : budget' ≤ budget) :
    HistoryStageData (χ := χ) (instSymbolD := instSymbolD) (instSymbolF := instSymbolF)
      (P := P) (keep := keep) (hkeep := hkeep) (bD := bD) (ω := ω) (hD := hD)
      (bF := bF) (ν := ν) (hF := hF) (hφ := hφ) (W := W)
      eQ r a Bstage budget' pMajor Rrank C := by
  exact { data with
    hcommon := (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hbudget)
      (Real.exp_nonneg _)).trans data.hcommon
    hallowance := (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hbudget) (by positivity))
      (by positivity)).trans data.hallowance }

end AllocatedExternalCandidateProblem
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

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := Deck) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ z : P.productive, (P.chart z).keep = keep)
    {ι κ χ η : Type} [Fintype ι] [Fintype κ] [Fintype χ] [Fintype η]
    (bD : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = span ℚ (bD '' {i | j ≤ ω i}))
    (bF : Basis κ ℚ M) (ν : κ → ℕ)
    (hF : ∀ j, Fmark.layer j = span ℚ (bF '' {i | j ≤ ν i}))
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)

local notation "Vars" => {i : LayerSamplerVariables G I n B // keep i}
local notation "fast" => W.map (D.filtration.associatedGradedMap Fmark φ hφ)
local notation "gmark" => Fmark.realification.polynomialOrbitCoordinates (fullTaggedVariableWeight J) marked
local notation "Z" => Fmark.realPolynomialSymbolHom bF ν hF (fullTaggedVariableWeight J) gmark
local notation "Q" => P.withKeep keep hkeep

noncomputable def historyStageData_of_base_bound
    [instSymbolD : Fintype (SymbolBasisIndex (fun _ : Vars => 1) ω)]
    [instSymbolF : Fintype (SymbolBasisIndex (fun _ : Vars => 1) ν)]
    (eQ : Basis η ℚ (Fmark.AssociatedGraded ⧸ (fast).toSubmodule))
    (r : ℕ) (hr : r ≤ s)
    [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    (Bstage budget pMajor Rrank : ℝ) (C : ℕ)
    (v : ℝ) (hv : 2 ≤ v) (hbudget : budget ≤ v) (hBstage : Bstage ≤ v)
    (sliceCost : ℝ) (hSliceCost : sliceCost ≤ v)
    (hdense : ∀ z : P.productive, IsDenseCommonStrideBox (fun i : Vars => A.sides i.val)
      sliceCost ((Q).chart z).slice.integerPoints)
    (HMap l H Hθ : ℕ) (qNative : ℝ)
    (hHMap : 1 ≤ HMap) (hl : 0 < l) (hH : 1 ≤ H)
    (hHMapExp : (HMap : ℝ) ≤ Real.exp v) (hlExp : (l : ℝ) ≤ Real.exp v)
    (hHExp : (H : ℝ) ≤ Real.exp v) (hHθExp : (Hθ : ℝ) ≤ Real.exp v)
    (hqNative : qNative ≤ v)
    (hentries : ∀ i j, RationalHeightLE (bF.repr (φ (bD j)) i) HMap)
    (hsource : (Fintype.card (SymbolBasisIndex (fun _ : Vars => 1) ω) : ℝ) ≤ v)
    (htarget : (Fintype.card (SymbolBasisIndex (fun _ : Vars => 1) ν) : ℝ) ≤ v)
    (hκ : (Fintype.card κ : ℝ) ≤ v) (hχ : (Fintype.card χ : ℝ) ≤ v)
    (hη : (Fintype.card η : ℝ) ≤ v)
    (htags : (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ v)
    (hsampler : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ v)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ v)
    (hbracket : ∀ i j z, RationalHeightLE (bF.repr ⁅bF i, bF j⁆ z) H)
    (vg : χ → Fmark.PolynomialSymbol (fun _ : Vars => 1))
    (hspan : span ℚ (Set.range vg) =
      (Fmark.symbolPointwiseSubalgebra bF ν hF (fun _ : Vars => 1) fast).toSubmodule)
    (hvg : ∀ i z, RationalHeightLE
      ((Fmark.polynomialSymbolBasis bF ν hF (fun _ : Vars => 1)).repr (vg i) z) H)
    (hθ : ∀ j i, RationalHeightLE (((eQ.coord j).comp (fast).toSubmodule.mkQ)
      (Fmark.associatedGradedBasis bF ν hF i)) Hθ)
    (hfactor : ∀ z : P.productive, D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : Vars => (A.sides i.val : ℝ)) qNative l W
      (D.filtration.realification.polynomialOrbitCoordinates _ ((Q).candidate z).orbit))
    (hτ : τ ≤ 1) (hξ : ξ ≤ 1) (hσone : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ 1 / 8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (pSlice pTest pNative α : ℝ)
    (hSlice : allocatedCandidateStageSliceLog s m v ≤ pSlice)
    (hkept : ∀ i, keep i → Real.exp pSlice ≤ (A.sides i : ℝ))
    (hfrozen : ∀ i, ¬keep i → (A.sides i : ℝ) ≤ Real.exp pSlice)
    (hNative : v ≤ pNative)
    (hTest : OrdinaryPolynomialPhase.budget r ≤ pTest)
    (hMajor : productNiltestBudget pNative + pNative + v + 2 ≤ pMajor)
    (hα : α ≤ (9 / 10 : ℝ) * massThreshold)
    (hdirect : A.NativeDetection r pSlice pTest pNative α)
    (hNmajor : ∀ i, Real.exp ((pMajor + C) ^ C) ≤ (N i : ℝ))
    (hRrank : Real.exp ((pMajor + C) ^ C) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j)) :
    HistoryStageData (χ := χ) (instSymbolD := instSymbolD) (instSymbolF := instSymbolF)
      (P := P) (keep := keep) (hkeep := hkeep) (bD := bD) (ω := ω) (hD := hD)
      (bF := bF) (ν := ν) (hF := hF) (hφ := hφ) (W := W)
      eQ r 1 Bstage budget pMajor Rrank C := by
  have hv0 : 0 ≤ v := le_trans (by norm_num) hv
  obtain ⟨hresetInput, hresetInput0⟩ := allocatedCandidateStage_reset_bounds s m hv
  obtain ⟨hlocalInput, hlocalV, _⟩ := allocatedCandidateStage_local_bounds s m hv
  obtain ⟨hSlice0, hresetSlice, hinterpolate, hthreshold⟩ :=
    allocatedCandidateStage_slice_bounds s m hv
  have hpSlice0 : 0 ≤ pSlice := hSlice0.trans hSlice
  have hlocalCost := allocatedCandidateStage_localCost_le_slice s m r hv hr
  have hVars : (Fintype.card Vars : ℝ) ≤ v :=
    (Nat.cast_le.mpr (Fintype.card_subtype_le keep)).trans hsampler
  have hpNative0 : 0 ≤ pNative := hv0.trans hNative
  have hproduct0 : 0 ≤ productNiltestBudget pNative :=
    (sq_nonneg _).trans (productNiltestBudget_geometry hpNative0)
  have hNativeMajor : pNative ≤ pMajor := by linarith only [hproduct0, hv0, hMajor]
  have hproduct : productNiltestBudget pNative ≤ pMajor := by
    linarith only [hpNative0, hv0, hMajor]
  have hvMajor : v ≤ pMajor := by linarith only [hproduct0, hpNative0, hMajor]
  refine {
    hr := hr
    HMap := HMap
    l := l
    pMap := v
    hHMap := hHMap
    hl := hl
    hpMap := hv0
    hentries := hentries
    hsource := hsource
    htarget := htarget
    hHMapExp := hHMapExp
    hlExp := hlExp
    H := H
    p := allocatedCandidateStageResetInput s m v
    qNative := qNative
    hH := hH
    hp := hresetInput0
    hκ := hκ.trans hresetInput
    hVars := hVars.trans hresetInput
    hχ := hχ.trans hresetInput
    hHExp := hHExp.trans (Real.exp_le_exp.mpr hresetInput)
    hbracket := hbracket
    hcommon := allocatedCandidateStage_common_bound s m hv hbudget
    hmapSlow := ?_
    hallowance := ?_
    hNreset := ?_
    vg := vg
    hspan := hspan
    hvg := hvg
    hτ := hτ
    hξ := hξ
    hσone := hσone
    Cgeo := Cgeo
    hCgeo := hCgeo
    hchart := hchart
    hsmall := hsmall
    hpoly := hpoly
    pK := v
    Mbound := 1
    LongSide := Real.exp pSlice
    hpK := hv0
    hBstage := hBstage
    hJ := hJ
    hM := by norm_num
    hcap := fun j => (hsmall j).trans (by norm_num)
    hLong := Real.one_le_exp_iff.mpr hpSlice0
    hlong := ?_
    hthreshold := ?_
    hlength := ?_
    hfactor := hfactor
    Hθ := Hθ
    pLocal := allocatedCandidateStageLocalInput s m v
    hθ := hθ
    hpLocal := hlocalInput
    hLocalDim := hVars.trans hlocalV
    hLocalSize := ?_
    hLocalDen := ?_
    hNLocal := ?_
    pSlice := pSlice
    pTest := pTest
    pNative := pNative
    hpNative := hv.trans hNative
    hη := hη.trans hNative
    hNativeMajor := hNativeMajor
    hproduct := hproduct
    hdim := ?_
    hNmajor := hNmajor
    hRrank := hRrank
    hrank := hrank
    Bshort := Real.exp pSlice
    hBshort := Real.one_le_exp_iff.mpr hpSlice0
    hshort := hfrozen
    α := α
    hα := hα
    hdirect := hdirect
    hslice := ?_
    htest := hTest }
  · simpa only [pow_one] using allocatedCandidateStage_mapSlow_bound s m hv hqNative
  · simpa only [pow_one, Nat.cast_add, Nat.cast_one] using
      allocatedCandidateStage_allowance s m (Fintype.card (X ⊕ (Σ j, J j)))
        (Fintype.card (LayerSamplerVariables G I n B)) hv htags hsampler hbudget
  · intro i
    change Real.exp (allocatedCandidateStageResetLog s m v) ≤ (A.sides i.val : ℝ)
    exact (Real.exp_le_exp.mpr (hresetSlice.trans hSlice)).trans (hkept i.val i.property)
  · intro i hi
    have he : layerSamplerBox B U btag S i = (A.sides i : ℝ) := by cases i <;> rfl
    rw [he]
    exact hkept i hi
  · rw [mul_one, ← Real.exp_nat_mul]
    exact Real.exp_lt_exp.mpr (hthreshold.trans_le hSlice)
  · intro z
    apply ((Q).chart z).degree_lt_slice_length_of_dense s (hdense z)
    intro i
    apply (Real.exp_le_exp.mpr ?_).trans (hkept i.val i.property)
    have hi : sliceCost + (s : ℝ) + 1 ≤ v + (s : ℝ) + 1 := by
      linarith only [hSliceCost]
    exact hi.trans (hinterpolate.trans hSlice)
  · exact allocatedCandidateStage_localSize_bound s m (Fintype.card κ) Hθ hv hκ hHθExp
  · simpa only [Nat.cast_pow, allocatedCandidateStageResetLog] using
      allocatedCandidateStage_localDen_bound s m (Fintype.card κ) Hθ hv hκ hHθExp
  · intro i
    exact (Real.exp_le_exp.mpr (hlocalCost.trans hSlice)).trans (hkept i.val i.property)
  · simpa only [Fintype.card_sum] using htags.trans hvMajor
  · rw [Real.log_exp]
    exact max_le (hlocalCost.trans hSlice) le_rfl

noncomputable def historyStageData_of_native_source
    [instSymbolD : Fintype (SymbolBasisIndex (fun _ : Vars => 1) ω)]
    [instSymbolF : Fintype (SymbolBasisIndex (fun _ : Vars => 1) ν)]
    (eQ : Basis η ℚ (Fmark.AssociatedGraded ⧸ (fast).toSubmodule))
    (r : ℕ) (hr : r ≤ s)
    [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    (Bstage budget Rrank : ℝ) (C : ℕ)
    (v : ℝ) (hv : 2 ≤ v) (hbudget : budget ≤ v) (hBstage : Bstage ≤ v)
    (sliceCost : ℝ) (hSliceCost : sliceCost ≤ v)
    (hdense : ∀ z : P.productive, IsDenseCommonStrideBox (fun i : Vars => A.sides i.val)
      sliceCost ((Q).chart z).slice.integerPoints)
    (HMap l H Hθ : ℕ) (qNative : ℝ)
    (hHMap : 1 ≤ HMap) (hl : 0 < l) (hH : 1 ≤ H)
    (hHMapExp : (HMap : ℝ) ≤ Real.exp v) (hlExp : (l : ℝ) ≤ Real.exp v)
    (hHExp : (H : ℝ) ≤ Real.exp v) (hHθExp : (Hθ : ℝ) ≤ Real.exp v)
    (hqNative : qNative ≤ v)
    (hentries : ∀ i j, RationalHeightLE (bF.repr (φ (bD j)) i) HMap)
    (hsource : (Fintype.card (SymbolBasisIndex (fun _ : Vars => 1) ω) : ℝ) ≤ v)
    (htarget : (Fintype.card (SymbolBasisIndex (fun _ : Vars => 1) ν) : ℝ) ≤ v)
    (hκ : (Fintype.card κ : ℝ) ≤ v) (hχ : (Fintype.card χ : ℝ) ≤ v)
    (hη : (Fintype.card η : ℝ) ≤ v)
    (htags : (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ v)
    (hsampler : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ v)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ v)
    (hbracket : ∀ i j z, RationalHeightLE (bF.repr ⁅bF i, bF j⁆ z) H)
    (vg : χ → Fmark.PolynomialSymbol (fun _ : Vars => 1))
    (hspan : span ℚ (Set.range vg) =
      (Fmark.symbolPointwiseSubalgebra bF ν hF (fun _ : Vars => 1) fast).toSubmodule)
    (hvg : ∀ i z, RationalHeightLE
      ((Fmark.polynomialSymbolBasis bF ν hF (fun _ : Vars => 1)).repr (vg i) z) H)
    (hθ : ∀ j i, RationalHeightLE (((eQ.coord j).comp (fast).toSubmodule.mkQ)
      (Fmark.associatedGradedBasis bF ν hF i)) Hθ)
    (hfactor : ∀ z : P.productive, D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : Vars => (A.sides i.val : ℝ)) qNative l W
      (D.filtration.realification.polynomialOrbitCoordinates _ ((Q).candidate z).orbit))
    (hτ : τ ≤ 1) (hξ : ξ ≤ 1) (hσone : ∀ j, σ j ≤ 1)
    (Cgeo : Fin m → ℝ) (hCgeo : ∀ j, 0 ≤ Cgeo j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖)
    (hsmall : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ 1 / 8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (pSlice pTest sourceNative α : ℝ)
    (hSlice : allocatedCandidateStageSliceLog s m v ≤ pSlice)
    (hkept : ∀ i, keep i → Real.exp pSlice ≤ (A.sides i : ℝ))
    (hfrozen : ∀ i, ¬keep i → (A.sides i : ℝ) ≤ Real.exp pSlice)
    (hsourceNative : 0 ≤ sourceNative)
    (hTest : OrdinaryPolynomialPhase.budget r ≤ pTest)
    (hα : α ≤ (9 / 10 : ℝ) * massThreshold)
    (hdirect : A.NativeDetection r pSlice pTest sourceNative α)
    (hNmajor : ∀ i, Real.exp (((allocatedCandidateNativeMajorBudget (sourceNative + v + 2) v) + C) ^ C) ≤ (N i : ℝ))
    (hRrank : Real.exp (((allocatedCandidateNativeMajorBudget (sourceNative + v + 2) v) + C) ^ C) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j)) :
    HistoryStageData (χ := χ) (instSymbolD := instSymbolD) (instSymbolF := instSymbolF)
      (P := P) (keep := keep) (hkeep := hkeep) (bD := bD) (ω := ω) (hD := hD)
      (bF := bF) (ν := ν) (hF := hF) (hφ := hφ) (W := W)
      eQ r 1 Bstage budget
      (allocatedCandidateNativeMajorBudget (sourceNative + v + 2) v) Rrank C := by
  exact P.historyStageData_of_base_bound keep hkeep bD ω hD bF ν hF hφ W
    eQ r hr Bstage budget (allocatedCandidateNativeMajorBudget (sourceNative + v + 2) v)
    Rrank C v hv hbudget hBstage sliceCost hSliceCost hdense
    HMap l H Hθ qNative hHMap hl hH hHMapExp hlExp hHExp hHθExp hqNative
    hentries hsource htarget hκ hχ hη htags hsampler hJ hbracket vg hspan hvg hθ hfactor
    hτ hξ hσone Cgeo hCgeo hchart hsmall hpoly
    pSlice pTest (sourceNative + v + 2) α hSlice hkept hfrozen
    (by linarith only [hsourceNative]) hTest (by rfl) hα
    (hdirect.mono_native (by linarith only [hv])) hNmajor hRrank hrank

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
