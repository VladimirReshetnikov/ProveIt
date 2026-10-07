import OAI.Combinatorics.Progressions.Dynamics.NativeAdaptedOrdinaryResetGeometry
import OAI.Combinatorics.Progressions.Estimates.AllocatedCandidateZeroRestrictedNativeCommonPhysicalTerminal
import OAI.Combinatorics.Progressions.Estimates.AllocatedOrdinaryLongPhysicalTerminalConclusion
import OAI.Combinatorics.Progressions.Estimates.AllocatedPrimitiveFrontInitialLong
import OAI.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateSpatialNativeAutomaticLongGeometry

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

attribute [local irreducible] polynomialOrbitRealChart piRealOrbit
  weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer
  CertifiedFullChartFiniteHistory.earlyForwardBranchTree realGradedSymbolPolynomial

noncomputable section

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X] [DecidableEq X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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

namespace AllocatedExternalCandidateSpatialNativeFamily

variable {Deck : Fin m → Type} {Pivot : Type} [Fintype Pivot]
    {LG LM : Type}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {s d₀ : ℕ} {D : RationalFilteredNilmanifold LG s d₀}
    {Fmark : NilpotentLieFiltration LM s} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p pLocal pNative r periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateSpatialNativeFamily A Deck A.Path Pivot D Fmark φ marked
      keep cost p pLocal pNative r periodCap coverCap Lip)

    (keepLong : LayerSamplerVariables G I n B → Prop)
    (H : Finset A.Path)
    (sourceCenter : ∀ j, U j)
    (hpath : ∀ a ∈ H, (F.sourceChart a).path = a)
    (hcenter : ∀ a ∈ H, (F.sourceChart a).centerLift = sourceCenter)
    (hfrozen : ∀ a ∈ H, ∀ i : {i // ¬keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (observable : (X → ℤ) → D.Space → ℂ) (weight : (X → ℤ) → ℂ)
    (scoreThreshold : ℝ)
    (hscore : ∀ a ∈ H, scoreThreshold ≤ (F.sourceCandidate a).score observable weight)

variable {α : Type} [Fintype α]
    (e : Basis α ℚ (∀ i : Option Pivot, optionLieSpace LG (fun j => (F.native j).L) i))
    (ω : α → ℕ)
    (hF : ∀ k, (optionProduct D (fun j => (F.native j).model)).filtration.layer k =
      Submodule.span ℚ (e '' {i | k ≤ ω i}))
    (js : List Pivot)
    {dQ : ℕ}
    (Q : RationalFilteredNilmanifold (LG ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η js) s dQ)
    (hQ : Q.filtration = D.filtration.pivotQuotientFiltration φ F.η js)
    (hker : ∀ x ∈ D.filtration.pivotAnnihilatorIdeal φ F.η js, φ x = 0)
    (descended : (X → ℤ) → Q.Space → ℂ)
    (hrecovery : ∀ x (g : D.RealGroup),
      descended x (QuotientGroup.mk
        (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot)
          (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js)) g)) =
        observable x (QuotientGroup.mk g))
    (adapted : (optionProduct Q (fun j => (F.native j).model)).AdaptedModelData)

local notation "countConstants" => (fun n => fullChartStageCountConstant (n + 1) 254)

def ActualAdaptedPivotQuotientLongPhysicalTerminal
    {κ : Type} [Fintype κ]
    (bMark : Basis κ ℚ (∀ i : Option Pivot, optionLieSpace LM (fun j => (F.native j).L) i))
    (ν : κ → ℕ)
    (hMark : ∀ k, (NilpotentLieFiltration.pi (optionFiltrations Fmark (fun j => ((fun j => (F.native j).model) j).filtration))).layer k = Submodule.span ℚ (bMark '' {i | k ≤ ν i}))
    (hmarkΦ : ∀ k, ∀ z ∈ (adapted.model.filtration).layer k, (optionMarkedLieMap (L := fun j => (F.native j).L) (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal φ F.η js) φ hker)) z ∈ (NilpotentLieFiltration.pi (optionFiltrations Fmark (fun j => ((fun j => (F.native j).model) j).filtration))).layer k)
    (scheduleExponent Cprimitive : ℕ) (x separation qVertical qCommon pProj : ℝ) : Prop :=
  ∃ (retained : Finset A.Path) (hsub : retained ⊆ H)
    (hmass : Real.exp (-(verticalDecompositionBudget qVertical * Fintype.card Pivot +
      ((qCommon + 2) ^ 5 + qCommon))) * A.law.mass H ≤ A.law.mass retained),
    0 < A.law.mass retained ∧
    ∃ (theta : ∀ j, (F.native j).L →ₗ[ℚ] ℚ)
      (W : LieSubalgebra ℚ (optionProduct D (fun j => (F.native j).model)).filtration.AssociatedGraded)
      (v : Fin (Fintype.card α) →
        (optionProduct D (fun j => (F.native j).model)).filtration.AssociatedGraded)
      (den : ℕ),
      Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
      BasisGradedSubmodule
        ((optionProduct D (fun j => (F.native j).model)).filtration.associatedGradedBasis e ω hF)
        ω W.toSubmodule ∧
      (∀ i k, rationalLogHeight
        (((optionProduct D (fun j => (F.native j).model)).filtration.associatedGradedBasis
          e ω hF).repr (v i) k) ≤ qCommon) ∧
      (∀ j x, x ∈ (optionProduct D (fun j => (F.native j).model)).filtration.realGradedRefiltrationLayer W s →
        realifyFunctional ((pairFrequency (F.η j) (theta j)).comp
          (optionPairProjection j).toLinearMap) x = 0) ∧
      0 < den ∧ (den : ℝ) ≤ Real.exp qCommon ∧
      let source := F.actualSourceProblemOn H sourceCenter hpath hcenter hfrozen observable weight
        scoreThreshold hscore retained hsub hmass
      let target := (source.withKeep keep (fun _ => rfl)).adaptedOptionQuotient
        (fun j => (F.native j).model) (fun j => ((F.native j).test.fullTaggedSpatial J).orbit)
        (D.filtration.pivotAnnihilatorIdeal φ F.η js)
        (by rw [D.filtration.terminal]; exact bot_le) Q hQ hker descended hrecovery adapted
      let F₀ := (optionProduct D (fun j => (F.native j).model)).filtration
      let FQ := adapted.model.filtration
      let ψ := optionMarkedLieMap (L := fun j => (F.native j).L)
        (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js))
      let hψ := D.optionQuotientMap_mem_layer
        (D.filtration.pivotAnnihilatorIdeal φ F.η js)
        (by rw [D.filtration.terminal]; exact bot_le) Q hQ (fun j => (F.native j).model)
      let V := W.map (F₀.associatedGradedMap FQ ψ hψ)
      let vQ := F₀.gradedImageSpanningFamily FQ ψ hψ v
      ∃ denQ : ℕ, 0 < denQ ∧ (denQ : ℝ) ≤ Real.exp ((pProj + 2) ^ 4) ∧ den ∣ denQ ∧
        Submodule.span ℚ (Set.range vQ) = V.toSubmodule ∧
        BasisGradedSubmodule
          (FQ.associatedGradedBasis adapted.model.basis adapted.weight adapted.model_layers)
          adapted.weight V.toSubmodule ∧
        (∀ a i, rationalLogHeight
          ((FQ.associatedGradedBasis adapted.model.basis adapted.weight adapted.model_layers).repr
            (vQ a) i) ≤ (pProj + 2) ^ 4) ∧
        (∀ z : target.productive,
          FQ.HasCommonRefilteredOrbitFactors adapted.model.basis adapted.weight adapted.model_layers
            (fun i : {i // keepLong i} => (A.sides i.val : ℝ)) ((pProj + 2) ^ 3 + qCommon) denQ V
            (FQ.weightedAdaptedRealChartHom
              (fun _ : {i // keep i} => 1) (fun _ : {i // keepLong i} => 1)
              ((target.chart z).axisPolynomial keepLong (fun _ => 0))
              ((target.chart z).axisPolynomial_support keepLong (fun _ => 0))
              (FQ.realification.polynomialOrbitCoordinates (fun _ => 1)
                (target.candidate z).orbit))) ∧
        (∀ x ∈ FQ.gradedRefiltrationLayer V s,
          optionMarkedLieMap (L := fun j => (F.native j).L)
            (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal φ F.η js) φ hker) x = 0 →
          x = 0) ∧
        (∀ (Gmark : NilpotentLieFiltration
            (∀ i : Option Pivot, optionLieSpace LM (fun j => (F.native j).L) i) s)
          (hmarked : ∀ k, ∀ x ∈ FQ.layer k,
            optionMarkedLieMap (L := fun j => (F.native j).L)
              (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal φ F.η js) φ hker) x ∈
                Gmark.layer k),
          ∀ a ∈ V,
            basisGradeProjection
              (FQ.associatedGradedBasis adapted.model.basis adapted.weight adapted.model_layers)
              adapted.weight s a = a →
            FQ.associatedGradedMap Gmark
              (optionMarkedLieMap (L := fun j => (F.native j).L)
                (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal φ F.η js) φ hker))
              hmarked a = 0 → a = 0) ∧
        target.NativeCommonPhysicalTerminal bMark ν hMark hmarkΦ V
          scheduleExponent Cprimitive x separation

theorem ActualAdaptedPivotQuotientLongFactors.exists_affine_physical_terminal
    {qVertical qCommon pProj : ℝ}
    (hproduced : F.ActualAdaptedPivotQuotientLongFactors keepLong H sourceCenter hpath hcenter hfrozen
      observable weight scoreThreshold hscore e ω hF js Q hQ hker descended hrecovery adapted
      qVertical qCommon pProj)
    (stageKeep : ℕ → LayerSamplerVariables G I n B → Prop)
    (hstageLong : ∀ r < s, ∀ i, stageKeep r i → keepLong i)
    {κ : Type} [Fintype κ]
    (bMark : Basis κ ℚ (∀ i : Option Pivot, optionLieSpace LM (fun j => (F.native j).L) i))
    (ν : κ → ℕ)
    (hMark : ∀ k, (NilpotentLieFiltration.pi (optionFiltrations Fmark (fun j => ((fun j => (F.native j).model) j).filtration))).layer k = Submodule.span ℚ (bMark '' {i | k ≤ ν i}))
    (hmarkΦ : ∀ k, ∀ z ∈ (adapted.model.filtration).layer k, (optionMarkedLieMap (L := fun j => (F.native j).L) (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal φ F.η js) φ hker)) z ∈ (NilpotentLieFiltration.pi (optionFiltrations Fmark (fun j => ((fun j => (F.native j).model) j).filtration))).layer k)
    [Fintype (SymbolBasisIndex (fun _ : LayerSamplerVariables G I n B => 1) adapted.weight)]
    [Fintype (SymbolBasisIndex (fun _ : LayerSamplerVariables G I n B => 1) ν)]
    [∀ r, Fintype (SymbolBasisIndex
      (fun _ : {i : LayerSamplerVariables G I n B // stageKeep r i} => 1) adapted.weight)]
    [∀ r, Fintype (SymbolBasisIndex
      (fun _ : {i : LayerSamplerVariables G I n B // stageKeep r i} => 1) ν)]
    [∀ r, TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [∀ r, IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [∀ r, ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    [∀ r, T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
    (pGeometry Rrank : ℝ) (Hbr : ℕ)
    (hpGeometry : 0 ≤ pGeometry)
    (hSourceGeometry : (finrank ℚ (∀ i : Option Pivot,
      optionLieSpace (LG ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η js)
        (fun j => (F.native j).L) i) : ℝ) ≤ pGeometry)
    (hMarkedGeometry : (Fintype.card κ : ℝ) ≤ pGeometry)
    (hGeneratorGeometry : (Fintype.card α : ℝ) ≤ pGeometry)
    (hSamplerGeometry : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pGeometry)
    (hQuotientGeometry : (pProj + 2) ^ 4 ≤ pGeometry)
    (scheduleExponent : ℕ) (x gainLog stageLog : ℝ)
    (hx : 0 ≤ x) (hgain : gainLog ∈ Set.Icc 0 x) (hstage : stageLog ∈ Set.Icc 0 x)
    (Cprimitive Csource : ℕ) (sourceNative pTest detectionLoss : ℕ → ℝ)
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
    (HMap : ℕ) (hHMap : 1 ≤ HMap)
    (hHMapGeometry : (HMap : ℝ) ≤ Real.exp pGeometry)
    (hNativeBase : (pProj + 2) ^ 3 + qCommon ≤ (x + Cprimitive) ^ Cprimitive)
    (hentries : ∀ i j, RationalHeightLE (bMark.repr ((optionMarkedLieMap (L := fun j => (F.native j).L) (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal φ F.η js) φ hker)) (adapted.model.basis j)) i) HMap)
    (hbracket : ∀ i j z, RationalHeightLE (bMark.repr ⁅bMark i, bMark j⁆ z) Hbr)
    (hkept : ∀ r, ∀ i, stageKeep r i → Real.exp (allocatedCandidateStageSlice s m Cprimitive
      (preparedFiniteForwardParameter scheduleExponent countConstants r x)) ≤ (A.sides i : ℝ))
    (hfrozenStage : ∀ r, ∀ i, ¬stageKeep r i → (A.sides i : ℝ) ≤ Real.exp
      (allocatedCandidateStageSlice s m Cprimitive
        (preparedFiniteForwardParameter scheduleExponent countConstants r x)))
    (hTest : ∀ r < s, OrdinaryPolynomialPhase.budget r ≤ pTest r)
    (hDetectionLoss : ∀ r < s, detectionLoss r ≤ (9 / 10 : ℝ) *
      (Real.exp (-(verticalDecompositionBudget qVertical * Fintype.card Pivot +
        ((qCommon + 2) ^ 5 + qCommon))) * A.law.mass H))
    (hdirect : ∀ r < s, A.NativeDetection r (allocatedCandidateStageSlice s m Cprimitive
      (preparedFiniteForwardParameter scheduleExponent countConstants r x))
      (pTest r) (sourceNative r) (detectionLoss r))
    (hN : ∀ i, Real.exp (preparedFiniteForwardCumulative scheduleExponent countConstants s x) ≤ (N i : ℝ))
    (hRrank : Real.exp (preparedFiniteForwardCumulative scheduleExponent countConstants s x) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (hs : 0 < s) (separation : ℝ)
    (hseparation : certifiedAffineLongSideBound
      (preparedFiniteForwardCumulative scheduleExponent countConstants s x) ≤ separation) :
    F.ActualAdaptedPivotQuotientLongPhysicalTerminal keepLong H sourceCenter hpath hcenter hfrozen
      observable weight scoreThreshold hscore e ω hF js Q hQ hker descended hrecovery adapted
      bMark ν hMark hmarkΦ scheduleExponent Cprimitive x separation qVertical qCommon pProj := by
  classical
  obtain ⟨retained, hsub, hmass, hpos, theta, W, v, den, hv, hW, hvH, hzero,
    hden, hdenBound, denQ, hdenQ, hdenQBound, hdiv, hvQ, hWQ, hvQH, hfactorQ,
    htop, hgradedTop⟩ := hproduced
  let source := F.actualSourceProblemOn H sourceCenter hpath hcenter hfrozen observable weight
    scoreThreshold hscore retained hsub hmass
  let target := (source.withKeep keep (fun _ => rfl)).adaptedOptionQuotient
    (fun j => (F.native j).model) (fun j => ((F.native j).test.fullTaggedSpatial J).orbit) (D.filtration.pivotAnnihilatorIdeal φ F.η js)
    (by rw [D.filtration.terminal]; exact bot_le) Q hQ hker descended hrecovery adapted
  let V := W.map (((optionProduct D (fun j => (F.native j).model)).filtration).associatedGradedMap (adapted.model.filtration) (optionMarkedLieMap (L := fun j => (F.native j).L) (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js))) (D.optionQuotientMap_mem_layer (D.filtration.pivotAnnihilatorIdeal φ F.η js) (by rw [D.filtration.terminal]; exact bot_le) Q hQ (fun j => (F.native j).model)))
  let vQ := ((optionProduct D (fun j => (F.native j).model)).filtration).gradedImageSpanningFamily (adapted.model.filtration) (optionMarkedLieMap (L := fun j => (F.native j).L) (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js))) (D.optionQuotientMap_mem_layer (D.filtration.pivotAnnihilatorIdeal φ F.η js) (by rw [D.filtration.terminal]; exact bot_le) Q hQ (fun j => (F.native j).model)) v
  have hpGeometryX : pGeometry ≤ x :=
    (allocatedCandidateCommonFastBudget_bounds s hpGeometry).2.2.trans hGeometryBase
  have hprimitive : x ≤ (x + Cprimitive) ^ Cprimitive := by
    have hC : (1 : ℝ) ≤ Cprimitive := by exact_mod_cast hCprimitive
    have hbase : 1 ≤ x + Cprimitive := by linarith
    exact (le_add_of_nonneg_right (Nat.cast_nonneg Cprimitive)).trans
      (by simpa only [pow_one] using pow_le_pow_right₀ hbase hCprimitive)
  have hdenQBase : (denQ : ℝ) ≤ Real.exp ((x + Cprimitive) ^ Cprimitive) :=
    hdenQBound.trans (Real.exp_le_exp.mpr
      ((hQuotientGeometry.trans hpGeometryX).trans hprimitive))
  have hOriginal (z : target.productive) :
      (adapted.model.filtration).HasCommonRefilteredOrbitFactors adapted.model.basis adapted.weight adapted.model_layers
        (fun i : {i : LayerSamplerVariables G I n B // keepLong i} => (A.sides i.val : ℝ))
        ((pProj + 2) ^ 3 + qCommon) denQ V
        ((adapted.model.filtration).weightedAdaptedRealChartHom
          (fun _ : (target.chart z).Variables => 1)
          (fun _ : {i : LayerSamplerVariables G I n B // keepLong i} => 1)
          ((target.chart z).axisPolynomial keepLong (fun _ => 0))
          ((target.chart z).axisPolynomial_support keepLong (fun _ => 0))
          ((adapted.model.filtration).realification.polynomialOrbitCoordinates
            (fun _ => 1) (target.candidate z).orbit)) :=
    hfactorQ z
  have hselectedMass : 0 < Real.exp
      (-(verticalDecompositionBudget qVertical * Fintype.card Pivot +
        ((qCommon + 2) ^ 5 + qCommon))) * A.law.mass H := by
    apply mul_pos (Real.exp_pos _)
    apply hpos.trans_le
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun a _ _ => A.law.nonneg a)
  have ht := target.exists_zero_restricted_native_common_affine_physical_terminal stageKeep
    adapted.model.basis adapted.weight adapted.model_layers bMark ν hMark hmarkΦ V
    vQ hvQ hWQ pGeometry Rrank Hbr hpGeometry
    (by simpa only [Fintype.card_fin] using hSourceGeometry) hMarkedGeometry
    (by simpa only [Fintype.card_fin] using hGeneratorGeometry) hSamplerGeometry
    (fun a i => (hvQH a i).trans hQuotientGeometry)
    scheduleExponent x gainLog stageLog hx hgain hstage Cprimitive Csource
    sourceNative pTest detectionLoss hSourceNonneg hSourceBound hBaseExponent hphaseExponent
    hCprimitive hGeometryBase hHbr hTagsBase hmEarly hblocksEarly hHbrBase hcost
    HMap denQ ((pProj + 2) ^ 3 + qCommon) hHMap hdenQ hHMapGeometry hdenQBase
    hNativeBase hentries hbracket keepLong hstageLong hOriginal F.hτ1 F.hξ F.hσ1 F.Cgeo F.hCgeo F.hchart F.hsmall
    F.hpoly hkept hfrozenStage hTest hDetectionLoss hdirect hN hRrank hrank
    hs hselectedMass separation hseparation
  obtain ⟨qDim, hdim, eQ, lift, hfast, hsection, hterminal⟩ := ht
  refine ⟨retained, hsub, hmass, hpos, theta, W, v, den, hv, hW, hvH, hzero,
    hden, hdenBound, denQ, hdenQ, hdenQBound, hdiv, hvQ, hWQ, hvQH, hfactorQ,
    htop, hgradedTop, ?_⟩
  have hηBase : (Fintype.card (Fin qDim) : ℝ) ≤ x := by
    simpa only [Fintype.card_fin] using
      (Nat.cast_le.mpr hdim).trans (hMarkedGeometry.trans hpGeometryX)
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
    have hpositive : 0 < N i := by exact_mod_cast ((Real.exp_pos _).trans_le (hN i))
    exact Nat.succ_le_iff.mpr hpositive
  refine ⟨qDim, hdim, eQ, lift, hfast, hsection, hx, hXEarly, hmEarly, hJEarly,
    hηBase, hblocks, hNEarly, ?_⟩
  dsimp only at hterminal ⊢
  exact hterminal

end AllocatedExternalCandidateSpatialNativeFamily

end

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

attribute [local irreducible] polynomialOrbitRealChart piRealOrbit
  weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer
  CertifiedFullChartFiniteHistory.earlyForwardBranchTree realGradedSymbolPolynomial

noncomputable section

theorem exists_allocatedExternalCandidateSpatialNativeFamily_actual_physical_terminal
    (s : ℕ) (hs : 1 ≤ s) :
    ∃ Cgeometry C Cbasis K T : ℕ, 2 ≤ Cgeometry ∧ 2 ≤ C ∧ 2 ≤ Cbasis ∧ 2 ≤ K ∧ 2 ≤ T ∧
    ∀ {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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

    {Deck : Fin m → Type} {Pivot : Type} [Fintype Pivot]
    {LG LM : Type}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {d₀ : ℕ} {D : RationalFilteredNilmanifold LG s d₀}
    {dMark : ℕ} {Mmark : RationalFilteredNilmanifold LM s dMark} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Mmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p pLocal pNative r periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateSpatialNativeFamily A Deck A.Path Pivot D Mmark.filtration φ marked
      keep cost p pLocal pNative r periodCap coverCap Lip),
    ∀ {qVertical : ℝ}, pNative ≤ qVertical → pLocal + r + 1 ≤ qVertical →
      verticalDecompositionBudget qVertical ≤ p →
      r + verticalDecompositionBudget qVertical + 2 ≤ p →
    ∀ (H : Finset A.Path), 0 < A.law.mass H →
      (∀ a ∈ H, ∀ j, Real.exp (-r) ≤ ‖F.correlation a j‖) →
    ∀ (pGeometry : ℝ), 2 ≤ pGeometry → D.GeometryComplexityLE pGeometry →
      Mmark.GeometryComplexityLE pGeometry →
      ∀ (hφ : ∀ k, ∀ z ∈ D.filtration.layer k, φ z ∈ Mmark.filtration.layer k),
      (∀ i j, rationalLogHeight (Mmark.basis.repr (φ (D.basis j)) i) ≤ pGeometry) →
      pNative ≤ pGeometry → (Fintype.card Pivot : ℝ) ≤ pGeometry →
    ∀ (js : List Pivot) {dQ : ℕ}
      (Q : RationalFilteredNilmanifold
        (LG ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η js) s dQ)
      (hQ : Q.filtration = D.filtration.pivotQuotientFiltration φ F.η js)
      (hker : ∀ x ∈ D.filtration.pivotAnnihilatorIdeal φ F.η js, φ x = 0),
      Q.GeometryComplexityLE pGeometry →
      (∀ i j, rationalLogHeight
        (Q.basis.repr (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js)
          (D.basis j)) i) ≤ pGeometry) →
      let pGeo := (pGeometry + 2) ^ 2
      let jointGeo := (pGeometry + 3) ^ 2
      let adaptedBudget := (jointGeo + 2) ^ Cgeometry
      let bnd := adaptedBudget + (pGeo + 3) ^ 5 + pGeo + jointGeo + pGeometry + p + 2
      let localCost := allocatedFrozenTaggedPairBudget s C Cbasis pGeo p
      let jointCost := allocatedFrozenTaggedFamilyInputBudget bnd localCost
      let P := jointCost + (jointCost + K) ^ K
      let initialShortLog := max ((p + 2 + C) ^ C + 7 * p + 22) ((P + 2) ^ T)
      let keepLong := fun i => keep i ∧ Real.exp initialShortLog ≤ (A.sides i : ℝ)
    ∀ [Nonempty {i // keepLong i}],
      let qCommon := (P + 2) ^ T + (((P + 2) ^ 2 + 2) ^ 63 + 1) + P + 1
      let pProj := max qCommon 0 + adaptedBudget + 1
      let markInput := nativeOptionFixedSourceQuotientMarkInput pGeometry
      let markBudget := (markInput + 2) ^ nativeOptionFixedSourceMarkExponent.{0, 0}
      let pTerminal := (pProj + 2) ^ 4 + markInput + markBudget + jointGeo +
        (Fintype.card (LayerSamplerVariables G I n B) : ℝ) + 2
    ∀ (source : A.InnerSourceProfile s)
      (_hFastInput : allocatedCandidateCommonFastBudget s pTerminal ≤ source.x)
      (_hblocks : (s : ℝ) * (markInput * m) ≤ source.x)
      (_hShortInput : max cost initialShortLog ≤ (source.x + source.Cprimitive) ^ source.Cprimitive)
      (_hNativeInput : (pProj + 2) ^ 3 + qCommon ≤
        (source.x + source.Cprimitive) ^ source.Cprimitive)
      (massLog : ℝ) (hmass : Real.exp (-massLog) ≤ A.law.mass H)
      (_hMassInput : verticalDecompositionBudget qVertical * (Fintype.card Pivot : ℝ) +
        ((qCommon + 2) ^ 5 + qCommon) + massLog ≤ source.gainLog)
      (separation : ℝ)
      (_hseparation : certifiedAffineLongSideBound
        (preparedFiniteForwardCumulative source.scheduleExponent
          AllocatedExternalCandidateSampler.degreeSourceCountConstants s source.x) ≤ separation)
      [∀ r, TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
      [∀ r, IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
      [∀ r, ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
      [∀ r, T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
      (sourceCenter : ∀ j, U j)
      (hpath : ∀ a ∈ H, (F.sourceChart a).path = a)
      (hcenter : ∀ a ∈ H, (F.sourceChart a).centerLift = sourceCenter)
      (hfrozen : ∀ a ∈ H, ∀ i : {i // ¬keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
      (observable : (X → ℤ) → D.Space → ℂ) (weight : (X → ℤ) → ℂ)
      (scoreThreshold : ℝ)
      (hscore : ∀ a ∈ H, scoreThreshold ≤ (F.sourceCandidate a).score observable weight)
      (descended : (X → ℤ) → Q.Space → ℂ)
      (hrecovery : ∀ x (g : D.RealGroup),
        descended x (QuotientGroup.mk
          (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := Q.filtration.lowerCentralSeries_eq_bot)
            (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js)) g)) =
          observable x (QuotientGroup.mk g)),
      ∃ geometry : (optionProduct D (fun j => (F.native j).model)).AdaptedMapGeometryData
          (optionProduct Q (fun j => (F.native j).model))
          (optionMarkedLieMap (L := fun j => (F.native j).L)
            (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js)))
          jointGeo adaptedBudget,
      ∃ markGeometry : (optionProduct Q (fun j => (F.native j).model)).FixedSourceAdaptedMarkGeometryData
          (optionProduct Mmark (fun j => (F.native j).model)) geometry.target
          (optionMarkedLieMap (L := fun j => (F.native j).L)
            (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal φ F.η js) φ hker))
          markInput markBudget,
      let hmarkΦ := D.nativeOptionFixedSourceQuotientMark_mem_layer Mmark
        (D.filtration.pivotAnnihilatorIdeal φ F.η js)
        (by rw [D.filtration.terminal]; exact bot_le) Q hQ
        (fun j => (F.native j).model) φ hker hφ geometry.target
      let hMark : ∀ k, (NilpotentLieFiltration.pi (optionFiltrations Mmark.filtration
          (fun j => (F.native j).model.filtration))).layer k =
          Submodule.span ℚ (markGeometry.target.basis '' {i | k ≤ markGeometry.target.weight i}) := by
        intro k
        exact Mmark.optionAdaptedModel_layers (fun j => (F.native j).model) markGeometry.target k
      F.ActualAdaptedPivotQuotientLongPhysicalTerminal keepLong H sourceCenter hpath hcenter hfrozen
        observable weight scoreThreshold hscore geometry.source.basis geometry.source.weight
        geometry.source.layers js Q hQ hker descended hrecovery geometry.target
        markGeometry.target.basis markGeometry.target.weight hMark hmarkΦ
        source.scheduleExponent source.Cprimitive source.x separation qVertical qCommon pProj := by
  obtain ⟨Cgeometry, C, Cbasis, K, T, hCgeometry, hC, hCbasis, hK, hT, hfactor⟩ :=
    exists_allocatedExternalCandidateSpatialNativeFamily_native_long_geometry_factors s hs
  refine ⟨Cgeometry, C, Cbasis, K, T, hCgeometry, hC, hCbasis, hK, hT, ?_⟩
  intro m G X _ _ I J _ _ n B _ U b R σ S hb o hR hσ N poly hm τ ξ stride cells center
    _ A Deck Pivot _ LG LM _ _ _ _ _ _ _ _ d₀ D dMark Mmark φ marked
    keep cost p pLocal pNative r periodCap coverCap Lip F
    qVertical hpq hprecision hfrequency hbudget H hH hcorr
    pGeometry hpGeometry hD hMmark hφ hmark hpNative hPivot js dQ Q hQ hker hQGeometry hmap
    pGeo jointGeo adaptedBudget bnd localCost jointCost P initialShortLog keepLong _ qCommon pProj
    markInput markBudget pTerminal source hFastInput hblocks hShortInput hNativeInput
    massLog hmass hMassInput separation hseparation _ _ _ _
    sourceCenter hpath hcenter hfrozen observable weight scoreThreshold hscore descended hrecovery
  classical
  have hpGeometry0 : 0 ≤ pGeometry := (by norm_num : (0 : ℝ) ≤ 2).trans hpGeometry
  have hlong (i : {i // keepLong i}) :
      Real.exp ((p + 2 + C) ^ C + 7 * p + 22) ≤ (A.sides i.val : ℝ) :=
    (Real.exp_le_exp.mpr (le_max_left _ _)).trans i.property.2
  have hcommonLong (i : {i // keepLong i}) :
      Real.exp ((P + 2) ^ T) ≤ (A.sides i.val : ℝ) :=
    (Real.exp_le_exp.mpr (le_max_right _ _)).trans i.property.2
  obtain ⟨geometry, hproduced⟩ := hfactor F hpq hprecision hfrequency hbudget H hH hcorr
    pGeometry hpGeometry hD hpNative hPivot js Q hQ hker hQGeometry hmap
    keepLong (fun _ hi => hi.1) hlong hcommonLong sourceCenter hpath hcenter hfrozen
    observable weight scoreThreshold hscore descended hrecovery
  have hAtoms (j : Pivot) : (F.native j).model.GeometryComplexityLE pGeometry :=
    (F.native j).complexity.1.mono (F.native j).model hpNative
  obtain ⟨markGeometry, hmarkFiltration, hmarked⟩ :=
    D.exists_nativeOptionFixedSourceQuotientMarkGeometry Mmark
      (D.filtration.pivotAnnihilatorIdeal φ F.η js)
      (by rw [D.filtration.terminal]; exact bot_le) Q hQ
      (fun j => (F.native j).model) φ hker hφ geometry.target
      hpGeometry0 hD hMmark hQGeometry hAtoms hPivot hmap hmark geometry.target_forward
  refine ⟨geometry, markGeometry, ?_⟩
  intro hmarkΦ hMark
  let stageKeep := source.stageKeep
  let Hbr := ⌈Real.exp markBudget⌉₊
  have hMarkInput0 : 0 ≤ markInput :=
    (nativeOptionFixedSourceQuotientMarkInput_bounds hpGeometry0).1
  have hMarkBudget0 : 0 ≤ markBudget := by dsimp only [markBudget]; positivity
  have hJoint0 : 0 ≤ jointGeo := by dsimp only [jointGeo]; positivity
  have hProj0 : 0 ≤ (pProj + 2) ^ 4 := by positivity
  have hSampler0 : (0 : ℝ) ≤ Fintype.card (LayerSamplerVariables G I n B) := Nat.cast_nonneg _
  have hTerminal0 : 0 ≤ pTerminal := by
    dsimp only [pTerminal]
    linarith only [hProj0, hMarkInput0, hMarkBudget0, hJoint0, hSampler0]
  have hJointTerminal : jointGeo ≤ pTerminal := by
    dsimp only [pTerminal]
    linarith only [hProj0, hMarkInput0, hMarkBudget0, hSampler0]
  have hMarkInputTerminal : markInput ≤ pTerminal := by
    dsimp only [pTerminal]
    linarith only [hProj0, hMarkBudget0, hJoint0, hSampler0]
  have hMarkBudgetTerminal : markBudget + 1 ≤ pTerminal := by
    dsimp only [pTerminal]
    linarith only [hProj0, hMarkInput0, hJoint0, hSampler0]
  have hProjTerminal : (pProj + 2) ^ 4 ≤ pTerminal := by
    dsimp only [pTerminal]
    linarith only [hMarkInput0, hMarkBudget0, hJoint0, hSampler0]
  have hSamplerTerminal : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ pTerminal := by
    dsimp only [pTerminal]
    linarith only [hProj0, hMarkInput0, hMarkBudget0, hJoint0]
  have hTerminalX : pTerminal ≤ source.x :=
    (allocatedCandidateCommonFastBudget_bounds s hTerminal0).2.2.trans hFastInput
  have hHbr := source.markHeight_bounds hMarkBudget0 (hMarkBudgetTerminal.trans hTerminalX)
  have hHnonempty : H.Nonempty := by
    by_contra he
    have hzero : A.law.mass H = 0 := by
      rw [Finset.not_nonempty_iff_eq_empty.mp he]
      simp [FiniteProbabilityWeights.mass]
    linarith only [hH, hzero]
  obtain ⟨a, ha⟩ := hHnonempty
  have hshort : ∀ i, ¬keepLong i →
      (A.sides i : ℝ) ≤ Real.exp (max cost initialShortLog) :=
    allocatedCandidate_initialLong_excluded_bound (fun i => (A.sides i : ℝ)) keep
      (fun i hi => hfrozen a ha ⟨i, hi⟩)
  have hstageLong := source.stageKeep_subset_initialLong keepLong hShortInput hshort
  have hcost : cost ≤ (source.x + source.Cprimitive) ^ source.Cprimitive :=
    (le_max_left _ _).trans hShortInput
  let : Fintype (SymbolBasisIndex (fun _ : LayerSamplerVariables G I n B => 1)
      geometry.target.weight) := symbolBasisIndexFintype _ _ s (fun _ => Nat.zero_lt_one)
        (geometry.target.model.filtration.adaptedBasis_weight_le_step
          geometry.target.model.basis geometry.target.weight geometry.target.model_layers)
  let : Fintype (SymbolBasisIndex (fun _ : LayerSamplerVariables G I n B => 1)
      markGeometry.target.weight) := symbolBasisIndexFintype _ _ s (fun _ => Nat.zero_lt_one)
        (markGeometry.target.model.filtration.adaptedBasis_weight_le_step
          markGeometry.target.model.basis markGeometry.target.weight markGeometry.target.model_layers)
  let (r : ℕ) : Fintype (SymbolBasisIndex (fun _ : {i // stageKeep r i} => 1)
      geometry.target.weight) := symbolBasisIndexFintype _ _ s (fun _ => Nat.zero_lt_one)
        (geometry.target.model.filtration.adaptedBasis_weight_le_step
          geometry.target.model.basis geometry.target.weight geometry.target.model_layers)
  let (r : ℕ) : Fintype (SymbolBasisIndex (fun _ : {i // stageKeep r i} => 1)
      markGeometry.target.weight) := symbolBasisIndexFintype _ _ s (fun _ => Nat.zero_lt_one)
        (markGeometry.target.model.filtration.adaptedBasis_weight_le_step
          markGeometry.target.model.basis markGeometry.target.weight markGeometry.target.model_layers)
  have hblocksActual : ((s * (Fintype.card (Fin (finrank ℚ
      (∀ i : Option Pivot, optionLieSpace LM (fun j => (F.native j).L) i))) * m) : ℕ) : ℝ) ≤
      source.x := by
    simpa only [Fintype.card_fin, Nat.cast_mul] using
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right markGeometry.target_dimension (Nat.cast_nonneg m))
        (Nat.cast_nonneg s)).trans hblocks
  exact AllocatedExternalCandidateSpatialNativeFamily.ActualAdaptedPivotQuotientLongFactors.exists_affine_physical_terminal
    F keepLong H sourceCenter hpath hcenter hfrozen
    observable weight scoreThreshold hscore geometry.source.basis geometry.source.weight
    geometry.source.layers js Q hQ hker descended hrecovery geometry.target hproduced
    stageKeep (fun r _ => hstageLong r)
    markGeometry.target.basis markGeometry.target.weight hMark hmarkΦ
    pTerminal source.rankThreshold Hbr hTerminal0
    (geometry.target_dimension.trans hJointTerminal)
    (by simpa only [Fintype.card_fin] using markGeometry.target_dimension.trans hMarkInputTerminal)
    (by simpa only [Fintype.card_fin] using geometry.source_dimension.trans hJointTerminal)
    hSamplerTerminal hProjTerminal
    source.scheduleExponent source.x source.gainLog source.stageLog source.x_nonneg
    source.gain_range source.stage_range source.Cprimitive source.Csource
    source.sourceNative source.pTest source.detectionLoss source.source_nonneg source.source_bound
    source.base_exponent source.phase_exponent source.primitive_pos hFastInput hHbr.1
    source.tags_input source.layers_input hblocksActual hHbr.2 hcost
    markGeometry.entries_height (Nat.one_le_of_lt markGeometry.entries_height_pos)
    (markGeometry.entries_bound.trans (Real.exp_le_exp.mpr
      ((le_add_of_nonneg_right zero_le_one).trans hMarkBudgetTerminal)))
    hNativeInput markGeometry.entries
    (fun i j k => rationalHeightLE_ceil_exp (markGeometry.target_structure i j k))
    source.stageKeep_kept source.stageKeep_frozen source.test_floor
    (source.detectionLoss_le_spatialNativeMass (Pivot := Pivot) hmass hMassInput)
    source.detection source.size_floor source.rank_floor source.sampling_rank hs
    separation hseparation

end
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

attribute [local irreducible] polynomialOrbitRealChart piRealOrbit
  weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom realSymbolGradeEvaluation
  CertifiedFullChartFiniteHistory.outer
  CertifiedFullChartFiniteHistory.earlyForwardBranchTree realGradedSymbolPolynomial

noncomputable section

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
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

namespace AllocatedExternalCandidateSpatialNativeFamily

variable {Deck : Fin m → Type} {Pivot : Type} [Fintype Pivot]
    {LG LM : Type}
    [LieRing LG] [LieAlgebra ℚ LG] [LieRing LM] [LieAlgebra ℚ LM]
    [TopologicalSpace (ℝ ⊗[ℚ] LG)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] LG)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] LG)] [T2Space (ℝ ⊗[ℚ] LG)]
    {s d₀ : ℕ} {D : RationalFilteredNilmanifold LG s d₀}
    {dMark : ℕ} {Mmark : RationalFilteredNilmanifold LM s dMark} {φ : LG →ₗ⁅ℚ⁆ LM}
    {marked : Mmark.filtration.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    {keep : LayerSamplerVariables G I n B → Prop}
    {cost p pLocal pNative r periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (F : AllocatedExternalCandidateSpatialNativeFamily A Deck A.Path Pivot D Mmark.filtration φ marked
      keep cost p pLocal pNative r periodCap coverCap Lip)

    (keepLong : LayerSamplerVariables G I n B → Prop)
    (H : Finset A.Path)
    (sourceCenter : ∀ j, U j)
    (hpath : ∀ a ∈ H, (F.sourceChart a).path = a)
    (hcenter : ∀ a ∈ H, (F.sourceChart a).centerLift = sourceCenter)
    (hfrozen : ∀ a ∈ H, ∀ i : {i // ¬keep i}, (A.sides i.val : ℝ) ≤ Real.exp cost)
    (observable : (X → ℤ) → D.Space → ℂ) (weight : (X → ℤ) → ℂ)
    (scoreThreshold : ℝ)
    (hscore : ∀ a ∈ H, scoreThreshold ≤ (F.sourceCandidate a).score observable weight)

variable (js : List Pivot) {dQ : ℕ}
    (Q : RationalFilteredNilmanifold
      (LG ⧸ D.filtration.pivotAnnihilatorIdeal φ F.η js) s dQ)
    (hQ : Q.filtration = D.filtration.pivotQuotientFiltration φ F.η js)
    (hker : ∀ z ∈ D.filtration.pivotAnnihilatorIdeal φ F.η js, φ z = 0)
    (descended : (X → ℤ) → Q.Space → ℂ)
    (hrecovery : ∀ x (g : D.RealGroup),
      descended x (QuotientGroup.mk
        (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := Q.filtration.lowerCentralSeries_eq_bot)
          (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js)) g)) =
        observable x (QuotientGroup.mk g))
    {jointGeo adaptedBudget markInput markBudget : ℝ}
    (geometry : (optionProduct D (fun j => (F.native j).model)).AdaptedMapGeometryData
      (optionProduct Q (fun j => (F.native j).model))
      (optionMarkedLieMap (L := fun j => (F.native j).L)
        (lieQuotientMap (D.filtration.pivotAnnihilatorIdeal φ F.η js))) jointGeo adaptedBudget)
    (markGeometry : (optionProduct Q (fun j => (F.native j).model)).FixedSourceAdaptedMarkGeometryData
      (optionProduct Mmark (fun j => (F.native j).model)) geometry.target
      (optionMarkedLieMap (L := fun j => (F.native j).L)
        (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal φ F.η js) φ hker))
      markInput markBudget)

theorem ordinaryData_of_actualAdaptedPivotQuotientLongPhysicalTerminal
    (hφ : ∀ k, ∀ z ∈ D.filtration.layer k, φ z ∈ Mmark.filtration.layer k)
    (hsurj : ∀ k, ∀ y ∈ Mmark.filtration.layer k,
      ∃ z ∈ D.filtration.layer k, φ z = y)
    {scheduleExponent Cprimitive : ℕ} {x separation qVertical qCommon pProj p0 : ℝ}
    (hp0 : 0 ≤ p0) (hgeometry : adaptedBudget ≤ p0) (hmark : markBudget ≤ p0)
    (hgenerator : jointGeo ≤ p0)
    (hvariables : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p0)
    (hprojection : (pProj + 2) ^ 4 ≤ p0)
    (hfactor : (pProj + 2) ^ 3 + qCommon ≤ p0)
    (hcost : cost ≤ p0)
    (hshort : ∀ i, ¬keepLong i → (A.sides i : ℝ) ≤ Real.exp p0) :
    let hmarkΦ := D.nativeOptionFixedSourceQuotientMark_mem_layer Mmark
      (D.filtration.pivotAnnihilatorIdeal φ F.η js)
      (by rw [D.filtration.terminal]; exact bot_le) Q hQ
      (fun j => (F.native j).model) φ hker hφ geometry.target
    F.ActualAdaptedPivotQuotientLongPhysicalTerminal keepLong H sourceCenter hpath hcenter hfrozen
      observable weight scoreThreshold hscore geometry.source.basis geometry.source.weight
      geometry.source.layers js Q hQ hker descended hrecovery geometry.target
      markGeometry.target.basis markGeometry.target.weight
      (Mmark.optionAdaptedModel_layers (fun j => (F.native j).model) markGeometry.target) hmarkΦ
      scheduleExponent Cprimitive x separation qVertical qCommon pProj →
    ∃ (retained : Finset A.Path) (hsub : retained ⊆ H)
      (hmass : Real.exp (-(verticalDecompositionBudget qVertical * Fintype.card Pivot +
        ((qCommon + 2) ^ 5 + qCommon))) * A.law.mass H ≤ A.law.mass retained),
      0 < A.law.mass retained ∧
      let source := F.actualSourceProblemOn H sourceCenter hpath hcenter hfrozen observable weight
        scoreThreshold hscore retained hsub hmass
      let target := (source.withKeep keep (fun _ => rfl)).adaptedOptionQuotient
        (fun j => (F.native j).model) (fun j => ((F.native j).test.fullTaggedSpatial J).orbit)
        (D.filtration.pivotAnnihilatorIdeal φ F.η js)
        (by rw [D.filtration.terminal]; exact bot_le) Q hQ hker descended hrecovery geometry.target
      Nonempty (AllocatedExternalCandidateProblem.OrdinaryLongPhysicalTerminalData
        (D := geometry.target.model)
        (Fmark := NilpotentLieFiltration.pi
          (optionFiltrations Mmark.filtration (fun j => (F.native j).model.filtration)))
        (φ := optionMarkedLieMap (L := fun j => (F.native j).L)
          (quotientInducedMark (D.filtration.pivotAnnihilatorIdeal φ F.η js) φ hker))
        target markGeometry.target.model
        geometry.target.weight geometry.target.model_layers
        markGeometry.target.weight
        (Mmark.optionAdaptedModel_layers (fun j => (F.native j).model) markGeometry.target) hmarkΦ p0
        (Fintype.card (Fin (finrank ℚ
          (∀ i : Option Pivot, optionLieSpace LG (fun j => (F.native j).L) i))))
        keepLong scheduleExponent Cprimitive x separation) := by
  intro hmarkΦ hproduced
  obtain ⟨retained, hsub, hmass, hpos, theta, W, v, den, hv, hW, hvH, hzero,
    hden, hdenBound, denQ, hdenQ, hdenQBound, hdiv, hvQ, hWQ, hvQH, hfactorQ,
    htop, hgradedTop, hterminal⟩ := hproduced
  obtain ⟨hsourceGeo, hmarkedGeo, hforward, hentries, hnativeEntries, hcount, _, _⟩ :=
    geometry.ordinaryResetGeometry markGeometry hp0 hgeometry hmark hgenerator
  refine ⟨retained, hsub, hmass, hpos, ?_⟩
  refine ⟨{
    model_filtration := by
      change NilpotentLieFiltration.pi
        (fun i => (optionFactors Mmark (fun j => (F.native j).model) i).filtration) = _
      congr 1
      funext i
      cases i <;> rfl
    nonnegative := hp0
    source_geometry := hsourceGeo
    marked_geometry := hmarkedGeo
    marked_basis_height := ?_
    mark_height := hnativeEntries
    generator_count := ?_
    variable_count := hvariables
    cost_bound := hcost
    short := hshort
    W := _
    generators := _
    span := hvQ
    graded := hWQ
    generator_height := fun a i => (hvQH a i).trans hprojection
    q := (pProj + 2) ^ 3 + qCommon
    q_bound := hfactor
    denominator := denQ
    denominator_pos := hdenQ
    denominator_bound := hdenQBound.trans (Real.exp_le_exp.mpr hprojection)
    zero_factors := hfactorQ
    top_kernel := htop
    surjective := ?_
    terminal := hterminal
  }⟩
  · intro i j
    exact hforward j i
  · exact hcount
  · exact D.nativeOptionFixedSourceQuotientMark_layer_surjective Mmark
      (D.filtration.pivotAnnihilatorIdeal φ F.η js)
      (by rw [D.filtration.terminal]; exact bot_le) Q hQ
      (fun j => (F.native j).model) φ hker geometry.target hsurj

end AllocatedExternalCandidateSpatialNativeFamily
end
end Erdos3.VectorPolynomial

end

end OAI
