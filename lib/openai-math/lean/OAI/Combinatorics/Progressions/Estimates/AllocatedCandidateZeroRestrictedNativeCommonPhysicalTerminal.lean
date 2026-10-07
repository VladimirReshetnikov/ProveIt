import OAI.Combinatorics.Progressions.Dynamics.CandidatePhysicalOrdinaryBudget

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

theorem exists_zero_restricted_native_common_affine_physical_terminal
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
      (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (hs : 0 < s) (hmass : 0 < massThreshold)
    (separation : ℝ)
    (hseparation : certifiedAffineLongSideBound
      (preparedFiniteForwardCumulative scheduleExponent countConstants s x) ≤ separation) :
    let pFull := allocatedCandidateTerminalFullInput s m Cprimitive x
      (preparedFiniteForwardWork scheduleExponent countConstants s x)
      (preparedFiniteForwardCumulative scheduleExponent countConstants s x)
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
    let pAffine := preparedFiniteForwardCumulative scheduleExponent countConstants s x
    let budget := preparedFiniteForwardWork scheduleExponent countConstants s x
    ∃ history ∈ T.level s,
      FullChartControlledFactors Fmark bF ν hF J poly N history.outer.1 history.outer.2
        (preparedFiniteForwardWork scheduleExponent countConstants s x) ∧
      RationalTaggedConstraintCertificate J Set.univ history.K
        (preparedFiniteForwardCumulative scheduleExponent countConstants s x)
        (s * (Fintype.card (Fin qDim) * m)) ∧
      (∀ point ∈ history.K,
        eval₂ point (Fmark.realGradedSymbolPolynomial bF ν hF (fullTaggedVariableWeight J)
          (history.outer.1⁻¹ * Z * history.outer.2⁻¹).coord) ∈
            (fast).toSubmodule.baseChange ℝ) ∧
      Nonempty (P.AffinePhysicalTerminalData bF ν hF hφ W (eQ.baseChange ℝ) lift
        pAffine budget pAffine pFull 4 history separation) := by
  classical
  intro pFull
  obtain ⟨qDim, hdim, eQ, lift, hfast, hsection, hterminal⟩ :=
    P.exists_early_forward_terminal_of_zero_restricted_native_common_factors keep bD ω hD bF ν hF hφ W
      v hv hW pGeometry Rrank Hbr hpGeometry hιGeometry hκGeometry hγGeometry hsamplerGeometry
      hvGeometry scheduleExponent x gainLog stageLog hx hgain hstage Cprimitive Csource
      sourceNative pTest α hSourceNonneg hSourceBound hBaseExponent hphaseExponent hCprimitive
      hGeometryBase hHbr hTagsBase hmEarly hblocksEarly hHbrBase hcost HMap l qNative hHMap hl
      hHMapGeometry hlExp hqNative hentries hbracket initialLong hstageLong hOriginal hτ hξ hσone Cgeo hCgeo hchart hsmall
      hpoly hkept hfrozen hTest hα hdirect hN hRrank hrank
  refine ⟨qDim, hdim, eQ, lift, hfast, hsection, ?_⟩
  intro hηBase hblocks hXEarly hJEarly hNEarly T pAffine budget
  obtain ⟨history, hmem, hcontrol, hcertificate, hterminalFast⟩ := hterminal
  have hA : 1 ≤ scheduleExponent :=
    (by omega : 1 ≤ 2).trans
      ((allocatedCandidateStageBaseExponent_bounds s m Cprimitive).1.trans hBaseExponent)
  have hxcum := le_preparedFiniteForwardCumulative scheduleExponent countConstants s hx hA hs
  have hcum : 0 ≤ pAffine := hx.trans hxcum
  have hwork : 0 ≤ budget := preparedFiniteForwardWork_nonneg scheduleExponent countConstants s hx
  have hfull := allocatedCandidateTerminalFullInput_bounds s m Cprimitive hx hwork hcum
  have hxFull : x ≤ pFull := hfull.2.2.1
  have hpFull : 0 ≤ pFull := hfull.1
  have hGeometryFull : pGeometry ≤ pFull :=
    ((allocatedCandidateCommonFastBudget_bounds s hpGeometry).2.2.trans hGeometryBase).trans hxFull
  have hvarsX : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ x :=
    hsamplerGeometry.trans ((allocatedCandidateCommonFastBudget_bounds s hpGeometry).2.2.trans hGeometryBase)
  have hdenFull := allocatedCandidateTerminalFullInput_denominator_bound s m Cprimitive hx hwork hcum
  have hmassFull := allocatedCandidateTerminalFullInput_mass_bound s m Cprimitive
    (Fintype.card (X ⊕ (Σ j, J j))) (Fintype.card (LayerSamplerVariables G I n B))
    hx hwork hcum hTagsBase hvarsX
  refine ⟨history, hmem, hcontrol, hcertificate, hterminalFast, ?_⟩
  exact P.exists_affinePhysicalTerminalData bF ν hF hφ W (eQ.baseChange ℝ) lift
    pAffine budget pAffine history hfast hcontrol hcertificate hcum
    (hJEarly.trans hxcum) (hblocks.trans hxcum) hpoly hτ hξ hσone
    Cgeo hCgeo hchart (fun j => (hsmall j).trans (by norm_num)) hmass Hbr 4 pFull
    hHbr hpFull (hκGeometry.trans hGeometryFull) (hTagsBase.trans hxFull)
    (hHbrBase.trans (Real.exp_le_exp.mpr hxFull)) hdenFull hbracket
    (hsamplerGeometry.trans hGeometryFull) hmassFull separation hseparation

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
