import OAI.Combinatorics.Progressions.Dynamics.CandidatePhysicalOrdinaryBudget
import OAI.Combinatorics.Progressions.Lattices.AllocatedAffinePhysicalBoundsSuccessor

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

theorem exists_early_forward_terminal_of_native_common_factors
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
    (hOriginal : ∀ z : P.productive, D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : (P.chart z).Variables => (A.sides i.val : ℝ)) qNative l W
      (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1) (P.candidate z).orbit))
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
  exact P.exists_early_forward_terminal_of_common_fast_generators keep bD ω hD bF ν hF hφ W
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
    fastGenerators hfastSpan hfastHeight hgeneratorCount hθ hOriginal hτ hξ hσone Cgeo hCgeo
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

theorem exists_native_common_affine_physical_terminal
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
    (hOriginal : ∀ z : P.productive, D.filtration.HasCommonRefilteredOrbitFactors bD ω hD
      (fun i : (P.chart z).Variables => (A.sides i.val : ℝ)) qNative l W
      (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1) (P.candidate z).orbit))
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
    P.exists_early_forward_terminal_of_native_common_factors keep bD ω hD bF ν hF hφ W
      v hv hW pGeometry Rrank Hbr hpGeometry hιGeometry hκGeometry hγGeometry hsamplerGeometry
      hvGeometry scheduleExponent x gainLog stageLog hx hgain hstage Cprimitive Csource
      sourceNative pTest α hSourceNonneg hSourceBound hBaseExponent hphaseExponent hCprimitive
      hGeometryBase hHbr hTagsBase hmEarly hblocksEarly hHbrBase hcost HMap l qNative hHMap hl
      hHMapGeometry hlExp hqNative hentries hbracket hOriginal hτ hξ hσone Cgeo hCgeo hchart hsmall
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

section

namespace Erdos3.NilpotentLieFiltration

open Module Submodule VectorPolynomial
open scoped Classical TensorProduct BigOperators

attribute [local irreducible] realPolynomialSymbolHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer

variable {m s : ℕ} {X M κ : Type} [Fintype X] [Fintype κ]
    [LieRing M] [LieAlgebra ℚ M]
    (Fmark : NilpotentLieFiltration M s)
    (bF : Basis κ ℚ M) (ν : κ → ℕ)
    (hF : ∀ j, Fmark.layer j = span ℚ (bF '' {i | j ≤ ν i}))
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (fast : LieSubalgebra ℚ Fmark.AssociatedGraded)
    (marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J))
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ)
    (scheduleExponent : ℕ) (x : ℝ)
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)

local notation "gmark" => Fmark.realification.polynomialOrbitCoordinates
  (fullTaggedVariableWeight J) marked
local notation "Z" => Fmark.realPolynomialSymbolHom bF ν hF (fullTaggedVariableWeight J) gmark
local notation "countConstants" => (fun n => fullChartStageCountConstant (n + 1) 254)

def NativeCommonTerminal : Prop :=
  ∃ (qDim : ℕ) (_hdim : qDim ≤ Fintype.card κ)
    (eQ : Basis (Fin qDim) ℚ (Fmark.AssociatedGraded ⧸ fast.toSubmodule))
    (lift : (Fmark.AssociatedGraded ⧸ fast.toSubmodule) →ₗ[ℚ] Fmark.AssociatedGraded),
  BasisGradedSubmodule (Fmark.associatedGradedBasis bF ν hF) ν fast.toSubmodule ∧
  Function.RightInverse lift fast.toSubmodule.mkQ ∧
  ∃ (hx : 0 ≤ x)
    (hXEarly : (Fintype.card X : ℝ) ≤ x) (hmEarly : (m : ℝ) ≤ x)
    (hJEarly : (Fintype.card (Σ j, J j) : ℝ) ≤ x)
    (hηBase : (Fintype.card (Fin qDim) : ℝ) ≤ x)
    (hblocks : ((s * (Fintype.card (Fin qDim) * m) : ℕ) : ℝ) ≤ x)
    (hNEarly : ∀ i, 1 ≤ N i),
  let T := CertifiedFullChartFiniteHistory.earlyForwardBranchTree
    Fmark bF ν hF J fast.toSubmodule (eQ.baseChange ℝ) lift Z U poly N
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
        (history.outer.1⁻¹ * Z * history.outer.2⁻¹).coord) ∈ fast.toSubmodule.baseChange ℝ

theorem NativeCommonTerminal.of_history
    (qDim : ℕ) (hdim : qDim ≤ Fintype.card κ)
    (eQ : Basis (Fin qDim) ℚ (Fmark.AssociatedGraded ⧸ fast.toSubmodule))
    (lift : (Fmark.AssociatedGraded ⧸ fast.toSubmodule) →ₗ[ℚ] Fmark.AssociatedGraded)
    (hfast : BasisGradedSubmodule (Fmark.associatedGradedBasis bF ν hF) ν fast.toSubmodule)
    (hsection : Function.RightInverse lift fast.toSubmodule.mkQ)
    (hx : 0 ≤ x)
    (hXEarly : (Fintype.card X : ℝ) ≤ x) (hmEarly : (m : ℝ) ≤ x)
    (hJEarly : (Fintype.card (Σ j, J j) : ℝ) ≤ x)
    (hηBase : (Fintype.card (Fin qDim) : ℝ) ≤ x)
    (hblocks : ((s * (Fintype.card (Fin qDim) * m) : ℕ) : ℝ) ≤ x)
    (hNEarly : ∀ i, 1 ≤ N i)
    (hterminal :
      let T := CertifiedFullChartFiniteHistory.earlyForwardBranchTree
        Fmark bF ν hF J fast.toSubmodule (eQ.baseChange ℝ) lift Z U poly N
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
            (history.outer.1⁻¹ * Z * history.outer.2⁻¹).coord) ∈ fast.toSubmodule.baseChange ℝ) :
    Fmark.NativeCommonTerminal bF ν hF J fast marked U poly N scheduleExponent x hm := by
  exact ⟨qDim, hdim, eQ, lift, hfast, hsection, hx, hXEarly, hmEarly, hJEarly,
    hηBase, hblocks, hNEarly, hterminal⟩

theorem NativeCommonTerminal.of_native_common_terminal
    (pGeometry : ℝ) (hpGeometry : 0 ≤ pGeometry)
    (hκGeometry : (Fintype.card κ : ℝ) ≤ pGeometry)
    (hGeometryBase : allocatedCandidateCommonFastBudget s pGeometry ≤ x)
    (hx : 0 ≤ x)
    (hTagsBase : (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ x)
    (hmEarly : (m : ℝ) ≤ x)
    (hblocksEarly : ((s * (Fintype.card κ * m) : ℕ) : ℝ) ≤ x)
    (hN : ∀ i, Real.exp (preparedFiniteForwardCumulative scheduleExponent
      countConstants s x) ≤ (N i : ℝ))
    (hterminal :
      ∃ (qDim : ℕ) (hdim : qDim ≤ Fintype.card κ)
        (eQ : Basis (Fin qDim) ℚ (Fmark.AssociatedGraded ⧸ fast.toSubmodule))
        (lift : (Fmark.AssociatedGraded ⧸ fast.toSubmodule) →ₗ[ℚ] Fmark.AssociatedGraded),
      BasisGradedSubmodule (Fmark.associatedGradedBasis bF ν hF) ν fast.toSubmodule ∧
      Function.RightInverse lift fast.toSubmodule.mkQ ∧
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
        Fmark bF ν hF J fast.toSubmodule (eQ.baseChange ℝ) lift Z U poly N
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
            (history.outer.1⁻¹ * Z * history.outer.2⁻¹).coord) ∈ fast.toSubmodule.baseChange ℝ) :
    Fmark.NativeCommonTerminal bF ν hF J fast marked U poly N scheduleExponent x hm := by
  obtain ⟨qDim, hdim, eQ, lift, hfast, hsection, hterminal⟩ := hterminal
  have hηBase : (Fintype.card (Fin qDim) : ℝ) ≤ x := by
    simpa only [Fintype.card_fin] using (Nat.cast_le.mpr hdim).trans (hκGeometry.trans
      ((allocatedCandidateCommonFastBudget_bounds s hpGeometry).2.2.trans hGeometryBase))
  have hblocks : ((s * (Fintype.card (Fin qDim) * m) : ℕ) : ℝ) ≤ x := by
    simpa only [Fintype.card_fin] using
      (Nat.cast_le.mpr (Nat.mul_le_mul_left s (Nat.mul_le_mul_right m hdim))).trans hblocksEarly
  have hXEarly : (Fintype.card X : ℝ) ≤ x := by
    have hsum : (Fintype.card X : ℝ) + (Fintype.card (Σ j, J j) : ℝ) ≤ x := by
      simpa only [Fintype.card_sum, Nat.cast_add] using hTagsBase
    exact (le_add_of_nonneg_right (Nat.cast_nonneg _)).trans hsum
  have hJEarly : (Fintype.card (Σ j, J j) : ℝ) ≤ x := by
    have hsum : (Fintype.card X : ℝ) + (Fintype.card (Σ j, J j) : ℝ) ≤ x := by
      simpa only [Fintype.card_sum, Nat.cast_add] using hTagsBase
    exact (le_add_of_nonneg_left (Nat.cast_nonneg _)).trans hsum
  have hNEarly : ∀ i, 1 ≤ N i := by
    intro i
    have hpos : 0 < N i := by
      exact_mod_cast ((Real.exp_pos _).trans_le (hN i))
    exact Nat.succ_le_iff.mpr hpos
  exact ⟨qDim, hdim, eQ, lift, hfast, hsection, hx, hXEarly, hmEarly, hJEarly,
    hηBase, hblocks, hNEarly, hterminal⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct BigOperators

attribute [local irreducible] realPolynomialSymbolHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer
  CertifiedFullChartFiniteHistory.earlyForwardBranchTree
  polynomialOrbitCoordinates realGradedSymbolPolynomial

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
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
    {κ : Type} [Fintype κ]
    (bF : Basis κ ℚ M) (ν : κ → ℕ)
    (hF : ∀ j, Fmark.layer j = span ℚ (bF '' {i | j ≤ ν i}))
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (scheduleExponent Cprimitive : ℕ) (x separation : ℝ)

local notation "fast" => W.map (D.filtration.associatedGradedMap Fmark φ hφ)
local notation "gmark" => Fmark.realification.polynomialOrbitCoordinates
  (fullTaggedVariableWeight J) marked
local notation "Z" => Fmark.realPolynomialSymbolHom bF ν hF (fullTaggedVariableWeight J) gmark
local notation "countConstants" => (fun n => fullChartStageCountConstant (n + 1) 254)

def NativeCommonPhysicalTerminal : Prop :=
  let pFull := allocatedCandidateTerminalFullInput s m Cprimitive x
    (preparedFiniteForwardWork scheduleExponent countConstants s x)
    (preparedFiniteForwardCumulative scheduleExponent countConstants s x)
  ∃ (qDim : ℕ) (_hdim : qDim ≤ Fintype.card κ)
    (eQ : Basis (Fin qDim) ℚ (Fmark.AssociatedGraded ⧸ (fast).toSubmodule))
    (lift : (Fmark.AssociatedGraded ⧸ (fast).toSubmodule) →ₗ[ℚ] Fmark.AssociatedGraded),
  BasisGradedSubmodule (Fmark.associatedGradedBasis bF ν hF) ν (fast).toSubmodule ∧
  Function.RightInverse lift (fast).toSubmodule.mkQ ∧
  ∃ (hx : 0 ≤ x)
    (hXEarly : (Fintype.card X : ℝ) ≤ x) (hmEarly : (m : ℝ) ≤ x)
    (hJEarly : (Fintype.card (Σ j, J j) : ℝ) ≤ x)
    (hηBase : (Fintype.card (Fin qDim) : ℝ) ≤ x)
    (hblocks : ((s * (Fintype.card (Fin qDim) * m) : ℕ) : ℝ) ≤ x)
    (hNEarly : ∀ i, 1 ≤ N i),
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
        (history.outer.1⁻¹ * Z * history.outer.2⁻¹).coord) ∈ (fast).toSubmodule.baseChange ℝ) ∧
    Nonempty (P.AffinePhysicalTerminalData bF ν hF hφ W (eQ.baseChange ℝ) lift
      pAffine budget pAffine pFull 4 history separation)

theorem NativeCommonPhysicalTerminal.to_terminal
    (h : P.NativeCommonPhysicalTerminal bF ν hF hφ W scheduleExponent Cprimitive x separation) :
    Fmark.NativeCommonTerminal bF ν hF J fast marked U poly N scheduleExponent x hm := by
  obtain ⟨qDim, hdim, eQ, lift, hfast, hsection, hx, hXEarly, hmEarly, hJEarly,
    hηBase, hblocks, hNEarly, history, hmem, hcontrol, hcertificate, hpointwise, _⟩ := h
  exact ⟨qDim, hdim, eQ, lift, hfast, hsection, hx, hXEarly, hmEarly, hJEarly,
    hηBase, hblocks, hNEarly, history, hmem, hcontrol, hcertificate, hpointwise⟩

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct BigOperators

attribute [local irreducible] realPolynomialSymbolHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer
  CertifiedFullChartFiniteHistory.earlyForwardBranchTree
  polynomialOrbitCoordinates realGradedSymbolPolynomial

noncomputable abbrev nativePhysicalTerminalAffineBudget (s scheduleExponent : ℕ) (x : ℝ) : ℝ :=
  preparedFiniteForwardCumulative scheduleExponent
    (fun n => fullChartStageCountConstant (n + 1) 254) s x

noncomputable abbrev nativePhysicalTerminalWorkBudget (s scheduleExponent : ℕ) (x : ℝ) : ℝ :=
  preparedFiniteForwardWork scheduleExponent
    (fun n => fullChartStageCountConstant (n + 1) 254) s x

noncomputable abbrev nativePhysicalTerminalFullBudget
    (s m Cprimitive scheduleExponent : ℕ) (x : ℝ) : ℝ :=
  allocatedCandidateTerminalFullInput s m Cprimitive x
    (nativePhysicalTerminalWorkBudget s scheduleExponent x)
    (nativePhysicalTerminalAffineBudget s scheduleExponent x)

theorem nativePhysicalTerminalBudgets_nonneg
    (s m Cprimitive scheduleExponent : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ nativePhysicalTerminalAffineBudget s scheduleExponent x ∧
    0 ≤ nativePhysicalTerminalWorkBudget s scheduleExponent x ∧
    0 ≤ nativePhysicalTerminalFullBudget s m Cprimitive scheduleExponent x := by
  have hcum := (preparedFiniteForward_prefix_bounds scheduleExponent
    (fun n => fullChartStageCountConstant (n + 1) 254) s hx).1.1
  have hwork := preparedFiniteForwardWork_nonneg scheduleExponent
    (fun n => fullChartStageCountConstant (n + 1) 254) s hx
  exact ⟨hcum, hwork,
    (allocatedCandidateTerminalFullInput_bounds s m Cprimitive hx hwork hcum).1⟩

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
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
    {κ : Type} [Fintype κ]
    (bF : Basis κ ℚ M) (ν : κ → ℕ)
    (hF : ∀ j, Fmark.layer j = span ℚ (bF '' {i | j ≤ ν i}))
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (scheduleExponent Cprimitive : ℕ) (x separation : ℝ)

local notation "fast" => W.map (D.filtration.associatedGradedMap Fmark φ hφ)
local notation "gmark" => Fmark.realification.polynomialOrbitCoordinates
  (fullTaggedVariableWeight J) marked
local notation "Z" => Fmark.realPolynomialSymbolHom bF ν hF (fullTaggedVariableWeight J) gmark
local notation "countConstants" => (fun n => fullChartStageCountConstant (n + 1) 254)

variable {P bF ν hF hφ W scheduleExponent Cprimitive x separation}

theorem NativeCommonPhysicalTerminal.exists_physicalData
    (hterminal : P.NativeCommonPhysicalTerminal bF ν hF hφ W
      scheduleExponent Cprimitive x separation) :
    0 ≤ nativePhysicalTerminalFullBudget s m Cprimitive scheduleExponent x ∧
    ∃ (qDim : ℕ)
      (eQ : Basis (Fin qDim) ℚ (Fmark.AssociatedGraded ⧸ (fast).toSubmodule))
      (lift : (Fmark.AssociatedGraded ⧸ (fast).toSubmodule) →ₗ[ℚ] Fmark.AssociatedGraded)
      (history : CertifiedFullChartFiniteHistory Fmark bF ν hF J (fast).toSubmodule
        (eQ.baseChange ℝ) lift Z Set.univ U poly N
        (nativePhysicalTerminalAffineBudget s scheduleExponent x) s),
      Nonempty (P.AffinePhysicalTerminalData bF ν hF hφ W (eQ.baseChange ℝ) lift
        (nativePhysicalTerminalAffineBudget s scheduleExponent x)
        (nativePhysicalTerminalWorkBudget s scheduleExponent x)
        (nativePhysicalTerminalAffineBudget s scheduleExponent x)
        (nativePhysicalTerminalFullBudget s m Cprimitive scheduleExponent x)
        4 history separation) := by
  obtain ⟨qDim, _hdim, eQ, lift, _hfast, _hsection, hx, _hXEarly, _hmEarly, _hJEarly,
    _hηBase, _hblocks, _hNEarly, history, _hmem, _hcontrol, _hcertificate, _hpointwise, hdata⟩ :=
      hterminal
  exact ⟨(nativePhysicalTerminalBudgets_nonneg s m Cprimitive scheduleExponent hx).2.2,
    qDim, eQ, lift, history, hdata⟩

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct BigOperators

attribute [local irreducible] realPolynomialSymbolHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer
  CertifiedFullChartFiniteHistory.earlyForwardBranchTree
  polynomialOrbitCoordinates realGradedSymbolPolynomial

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
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
    {s d f : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M s} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := Deck) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)
    (Mmodel : RationalFilteredNilmanifold M s f)
    (ω : Fin d → ℕ)
    (hD : ∀ j, D.filtration.layer j = span ℚ (D.basis '' {i | j ≤ ω i}))
    (ν : Fin f → ℕ)
    (hF : ∀ j, Fmark.layer j = span ℚ (Mmodel.basis '' {i | j ≤ ν i}))
    (hφ : ∀ j, ∀ z ∈ D.filtration.layer j, φ z ∈ Fmark.layer j)

structure OrdinaryLongPhysicalTerminalData
    (p0 : ℝ) (nGenerators : ℕ)
    (initialLong : LayerSamplerVariables G I n B → Prop)
    (scheduleExponent Cprimitive : ℕ) (x separation : ℝ) where
  model_filtration : Mmodel.filtration = Fmark
  nonnegative : 0 ≤ p0
  source_geometry : D.GeometryComplexityLE p0
  marked_geometry : Mmodel.GeometryComplexityLE p0
  marked_basis_height : ∀ i j,
    rationalLogHeight (Mmodel.basis.repr (Mmodel.basis i) j) ≤ p0
  mark_height : ∀ i j, rationalLogHeight (Mmodel.basis.repr (φ (D.basis j)) i) ≤ p0
  generator_count : (nGenerators : ℝ) ≤ p0
  variable_count : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p0
  cost_bound : cost ≤ p0
  short : ∀ i, ¬initialLong i → (A.sides i : ℝ) ≤ Real.exp p0
  W : LieSubalgebra ℚ D.filtration.AssociatedGraded
  generators : Fin nGenerators → D.filtration.AssociatedGraded
  span : Submodule.span ℚ (Set.range generators) = W.toSubmodule
  graded : BasisGradedSubmodule
    (D.filtration.associatedGradedBasis D.basis ω hD) ω W.toSubmodule
  generator_height : ∀ a i, rationalLogHeight
    ((D.filtration.associatedGradedBasis D.basis ω hD).repr (generators a) i) ≤ p0
  q : ℝ
  q_bound : q ≤ p0
  denominator : ℕ
  denominator_pos : 0 < denominator
  denominator_bound : (denominator : ℝ) ≤ Real.exp p0
  zero_factors : ∀ z : P.productive,
    D.filtration.HasCommonRefilteredOrbitFactors D.basis ω hD
      (fun i : {i // initialLong i} => (A.sides i.val : ℝ)) q denominator W
      (D.filtration.weightedAdaptedRealChartHom (fun _ : (P.chart z).Variables => 1)
        (fun _ : {i // initialLong i} => 1)
        ((P.chart z).axisPolynomial initialLong (fun _ => 0))
        ((P.chart z).axisPolynomial_support initialLong (fun _ => 0))
        (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1)
          (P.candidate z).orbit))
  top_kernel : ∀ z ∈ D.filtration.gradedRefiltrationLayer W s, φ z = 0 → z = 0
  surjective : ∀ j, ∀ y ∈ Fmark.layer j,
    ∃ z ∈ D.filtration.layer j, φ z = y
  terminal : P.NativeCommonPhysicalTerminal Mmodel.basis ν hF hφ W
    scheduleExponent Cprimitive x separation

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal
attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  symbolPointwiseSubalgebra realificationLieSubalgebra PolynomialRationalGrid PolynomialSlowBound
  HasCommonRefilteredOrbitFactors polynomialOrbitCoordinates associatedGradedMap realPolynomialGroupMap
  AllocatedExternalCandidateProblem.Refinement.problem
  realSymbolHomogeneousPullbackHom CertifiedFullChartFiniteHistory.outer
  CertifiedFullChartFiniteHistory.earlyForwardBranchTree

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I E J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
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

variable {L M : Type} {nMarkedBasis : ℕ} [LieRing L] [LieAlgebra ℚ L]
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
    (P : AllocatedExternalCandidateProblem (E := E) A D Fmark.filtration φ marked
      observable weight cost massThreshold scoreThreshold)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (c : Basis (Fin nMarkedBasis) ℚ M)
    (ν : Fin nMarkedBasis → ℕ)
    (hF : ∀ j, Fmark.filtration.layer j = span ℚ (c '' {i | j ≤ ν i}))
    (scheduleExponent Cprimitive : ℕ) (x p0 : ℝ)

local notation "fullBudget" => nativePhysicalTerminalFullBudget
  (s + 1) m Cprimitive scheduleExponent x
local notation "affineBudget" => nativePhysicalTerminalAffineBudget (s + 1) scheduleExponent x
local notation "workBudget" => nativePhysicalTerminalWorkBudget (s + 1) scheduleExponent x
local notation "separation" => Real.exp (candidatePrimitiveFreezingCutoff s 1
  (allocatedAffineCanonicalBudget s p0 fullBudget))

theorem conclusion_of_nativeCommonPhysicalTerminal_degreeRule
    {γ : Type} [Fintype γ]
    (hp0 : 0 ≤ p0)
    (hDgeo : D.GeometryComplexityLE p0) (hFgeo : Fmark.GeometryComplexityLE p0)
    (hcForward : ∀ i j, rationalLogHeight (Fmark.basis.repr (c i) j) ≤ p0)
    (hMap : ∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p0)
    (ω : Fin d → ℕ)
    (hD : ∀ j, D.filtration.layer j = span ℚ (D.basis '' {i | j ≤ ω i}))
    (v : γ → D.filtration.AssociatedGraded)
    (hW : BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis ω hD) ω W.toSubmodule)
    (hvspan : span ℚ (Set.range v) = W.toSubmodule)
    (hγ : (Fintype.card γ : ℝ) ≤ p0)
    (hvHeight : ∀ j i, rationalLogHeight
      ((D.filtration.associatedGradedBasis D.basis ω hD).repr (v j) i) ≤ p0)
    (hvariables : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p0)
    (q : ℝ) (l : ℕ) (hq0 : q ≤ p0) (hl : 0 < l) (hlBound : (l : ℝ) ≤ Real.exp p0)
    (hcost0 : cost ≤ p0)
    (initialLong : LayerSamplerVariables G I n B → Prop)
    (hshort : ∀ i, ¬initialLong i → (A.sides i : ℝ) ≤ Real.exp p0)
    (hzero : ∀ z : P.productive,
      D.filtration.HasCommonRefilteredOrbitFactors D.basis ω hD
        (fun i : {i // initialLong i} => (A.sides i.val : ℝ)) q l W
        (D.filtration.weightedAdaptedRealChartHom (fun _ : (P.chart z).Variables => 1)
          (fun _ : {i // initialLong i} => 1) ((P.chart z).axisPolynomial initialLong (fun _ => 0))
          ((P.chart z).axisPolynomial_support initialLong (fun _ => 0))
          (D.filtration.realification.polynomialOrbitCoordinates (fun _ => 1) (P.candidate z).orbit)))
    (hσ1 : ∀ j, σ j ≤ 1)
    (Hchart : Fin m → ℝ) (hHchart : ∀ j, 0 ≤ Hchart j)
    (hchart : ∀ j v,
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Hchart j * ‖v‖)
    (hsmall : ∀ j, Hchart j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1 / 8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hweight : ∀ x, ‖weight x‖ ≤ Real.exp p0)
    (hscore : Real.exp (-p0) ≤ scoreThreshold)
    (hmass : Real.exp (-p0) ≤
      Real.exp (-((2 * certifiedAffineCenterBudget affineBudget + 3) ^ 3)) * massThreshold)
    (hsurj : ∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (hξ1 : ξ ≤ 1) (ℓ : ℝ≥0) (hℓ : (ℓ : ℝ) ≤ Real.exp p0)
    (hLip : ∀ x, letI := D.metricSpace; LipschitzWith ℓ (observable x))
    (hpositive : ∀ x y, (observable x y).im = 0 ∧
      0 ≤ (observable x y).re ∧ (observable x y).re ≤ 1)
    (hmark : ∀ i j, rationalLogHeight (Fmark.basis.repr (φ (D.basis i)) j) ≤ p0)
    (htop : ∀ x : L, x ∈ D.filtration.gradedRefiltrationLayer W (s + 1) → φ x = 0 → x = 0)
    {e : ℕ}
    (hnet : ∀ accuracy : ℝ, 0 < accuracy → accuracy ≤ 1 → ∃ count : ℕ,
      (count : ℝ) ≤ Real.exp ((p0 + Real.log (1 / accuracy) + e) ^ e) ∧
      ∃ centers : Fin count → integerBox N,
        ∀ x ∈ integerBox N, ∃ i, ∀ y,
          ‖observable x y - observable (centers i).val y‖ ≤ accuracy)
    (outputCost : ℝ)
    (lowerIH : A.DegreeGlobalizationAt (E := E) weight s
      (RationalFilteredNilmanifold.refilteredQuotientNetExponent.{0, 0, 0} s 1 e + 2)
      (finiteFreezingRecursiveParameter (candidatePrimitivePhysicalBudgetExponent s 1)
        (allocatedAffineCanonicalBudget s p0 fullBudget)) outputCost)
    (houtput : finiteFreezingRecursiveParameter (candidatePrimitivePhysicalBudgetExponent s 1)
      (allocatedAffineCanonicalBudget s p0 fullBudget) ≤ outputCost)
    (hterminal : P.NativeCommonPhysicalTerminal c ν hF hφ W
      scheduleExponent Cprimitive x separation) :
    Nonempty (P.Conclusion outputCost (Real.exp (-outputCost)) (Real.exp (-outputCost))) := by
  obtain ⟨hpFull, qDim, eQ, lift, history, ⟨data⟩⟩ := hterminal.exists_physicalData
  obtain ⟨out⟩ := P.conclusion_of_affinePhysicalTerminal_bounds_degreeRule
    Fmark φ hφ W c ν hF (eQ.baseChange ℝ) lift
    affineBudget workBudget affineBudget fullBudget separation history data
    p0 hp0 hpFull hDgeo hFgeo hcForward hMap ω hD v hW hvspan hγ hvHeight hvariables
    q l hq0 hl hlBound hcost0 initialLong hshort hzero rfl hσ1 Hchart hHchart hchart hsmall
    hpoly hweight hscore hmass hsurj hξ1 ℓ hℓ hLip hpositive hmark htop hnet outputCost lowerIH
  have hcost : candidateSideCutoffCost separation ≤ outputCost :=
    (allocatedAffineCanonical_cutoffCost_le_recursive s hp0 hpFull).trans houtput
  exact ⟨by simpa only [max_eq_left hcost] using out⟩

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct BigOperators NNReal

attribute [local irreducible] realPolynomialSymbolHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer
  CertifiedFullChartFiniteHistory.earlyForwardBranchTree
  polynomialOrbitCoordinates realGradedSymbolPolynomial weightedAdaptedRealChartHom
  HasCommonRefilteredOrbitFactors associatedGradedMap

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I Deck J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {Rad σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U btag Rad σ}
    {hb : ∀ j, Submodule.span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (U j))}
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
    {s d f : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L (s + 1) d}
    {Fmark : NilpotentLieFiltration M (s + 1)} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {observable : (X → ℤ) → D.Space → ℂ} {weight : (X → ℤ) → ℂ}

namespace AllocatedExternalCandidateProblem

variable {cost massThreshold scoreThreshold : ℝ}
    (P : AllocatedExternalCandidateProblem (E := Deck) A D Fmark φ marked observable weight
      cost massThreshold scoreThreshold)
    (Mmodel : RationalFilteredNilmanifold M (s + 1) f)
    (ω : Fin d → ℕ)
    (hD : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (ν : Fin f → ℕ)
    (hF : ∀ j, Fmark.layer j = Submodule.span ℚ (Mmodel.basis '' {i | j ≤ ν i}))
    (hφ : ∀ j, ∀ z ∈ D.filtration.layer j, φ z ∈ Fmark.layer j)

variable {P Mmodel ω hD ν hF hφ}
    {p0 x separation : ℝ} {nGenerators scheduleExponent Cprimitive : ℕ}
    {initialLong : LayerSamplerVariables G I n B → Prop}

local notation "fullBudget" => nativePhysicalTerminalFullBudget
  (s + 1) m Cprimitive scheduleExponent x
local notation "affineBudget" => nativePhysicalTerminalAffineBudget (s + 1) scheduleExponent x
local notation "backendBudget" => allocatedAffineCanonicalBudget s p0 fullBudget
local notation "recursiveBudget" => finiteFreezingRecursiveParameter
  (candidatePrimitivePhysicalBudgetExponent s 1) backendBudget

include hD hF in

theorem OrdinaryLongPhysicalTerminalData.conclusion_of_bounds
    (packet : P.OrdinaryLongPhysicalTerminalData Mmodel ω hD ν hF hφ p0 nGenerators
      initialLong scheduleExponent Cprimitive x separation)
    (hseparation : separation = Real.exp (candidatePrimitiveFreezingCutoff s 1 backendBudget))
    (hσ1 : ∀ j, σ j ≤ 1)
    (Hchart : Fin m → ℝ) (hHchart : ∀ j, 0 ≤ Hchart j)
    (hchart : ∀ j v,
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (btag j)).symm v‖ ≤ Hchart j * ‖v‖)
    (hsmall : ∀ j, Hchart j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ 1 / 8)
    (hpoly : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hweight : ∀ y, ‖weight y‖ ≤ Real.exp p0)
    (hscore : Real.exp (-p0) ≤ scoreThreshold)
    (hmass : Real.exp (-p0) ≤
      Real.exp (-((2 * certifiedAffineCenterBudget affineBudget + 3) ^ 3)) * massThreshold)
    (hξ1 : ξ ≤ 1) (ℓ : ℝ≥0) (hℓ : (ℓ : ℝ) ≤ Real.exp p0)
    (hLip : ∀ y, letI := D.metricSpace; LipschitzWith ℓ (observable y))
    (hpositive : ∀ y z, (observable y z).im = 0 ∧
      0 ≤ (observable y z).re ∧ (observable y z).re ≤ 1)
    {e : ℕ}
    (hnet : ∀ accuracy : ℝ, 0 < accuracy → accuracy ≤ 1 → ∃ count : ℕ,
      (count : ℝ) ≤ Real.exp ((p0 + Real.log (1 / accuracy) + e) ^ e) ∧
      ∃ centers : Fin count → integerBox N,
        ∀ y ∈ integerBox N, ∃ i, ∀ z,
          ‖observable y z - observable (centers i).val z‖ ≤ accuracy)
    (outputCost : ℝ)
    (lowerIH : A.DegreeGlobalizationAt (E := Deck) weight s
      (RationalFilteredNilmanifold.refilteredQuotientNetExponent.{0, 0, 0} s 1 e + 2)
      recursiveBudget outputCost)
    (houtput : recursiveBudget ≤ outputCost) :
    Nonempty (P.Conclusion outputCost (Real.exp (-outputCost)) (Real.exp (-outputCost))) := by
  have hD' := hD
  have hF' := hF
  have hmodel := packet.model_filtration
  cases hmodel
  exact P.conclusion_of_nativeCommonPhysicalTerminal_degreeRule Mmodel φ hφ packet.W
    Mmodel.basis ν hF' scheduleExponent Cprimitive x p0
    packet.nonnegative packet.source_geometry packet.marked_geometry packet.marked_basis_height
    packet.mark_height ω hD' packet.generators packet.graded packet.span
    (by simpa only [Fintype.card_fin] using packet.generator_count)
    packet.generator_height packet.variable_count packet.q packet.denominator packet.q_bound
    packet.denominator_pos packet.denominator_bound packet.cost_bound initialLong packet.short
    packet.zero_factors hσ1 Hchart hHchart hchart hsmall hpoly hweight hscore hmass
    packet.surjective hξ1 ℓ hℓ hLip hpositive (fun i j => packet.mark_height j i)
    packet.top_kernel hnet outputCost lowerIH houtput
    (by simpa only [hseparation] using packet.terminal)

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
