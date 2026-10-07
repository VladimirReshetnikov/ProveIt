import OAI.Combinatorics.Progressions.Estimates.AllocatedFrozenPrefixStageData
import OAI.Combinatorics.Progressions.Geometry.CertifiedFullChartForwardEarlyTree
import OAI.Combinatorics.Progressions.Polynomial.PreparedFiniteForwardPolynomialCap

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

theorem ordinarySymbolSubtype_card_le {σ ι : Type*}
    (keep : σ → Prop) (ω : ι → ℕ)
    [Fintype (SymbolBasisIndex (fun _ : {i // keep i} => 1) ω)]
    [Fintype (SymbolBasisIndex (fun _ : σ => 1) ω)] :
    Fintype.card (SymbolBasisIndex (fun _ : {i // keep i} => 1) ω) ≤
      Fintype.card (SymbolBasisIndex (fun _ : σ => 1) ω) := by
  let embed : SymbolBasisIndex (fun _ : {i // keep i} => 1) ω →
      SymbolBasisIndex (fun _ : σ => 1) ω := fun z =>
    ⟨(z.val.1.mapDomain Subtype.val, z.val.2), by
      simpa only [← Finsupp.degree_eq_weight_one, Finsupp.degree_mapDomain] using z.property⟩
  apply Fintype.card_le_of_injective embed
  intro x y hxy
  apply Subtype.ext
  apply Prod.ext
  · exact Finsupp.mapDomain_injective Subtype.val_injective
      (congrArg (fun z => z.val.1) hxy)
  · exact congrArg (fun z => z.val.2) hxy

end Erdos3.NilpotentLieFiltration

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
    (stageCost stageMass stageScore : ℕ → ℝ)
    (Pstage : ∀ r, AllocatedExternalCandidateProblem (E := Deck) A D Fmark φ marked observable weight
      (stageCost r) (stageMass r) (stageScore r))
    (keep : ℕ → LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ r, ∀ z : (Pstage r).productive, ((Pstage r).chart z).keep = keep r)
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

theorem exists_budgeted_tree_terminal_of_stage_refinements
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
    (aControl aLocal : ℕ)
    (Bphase Bbound pTree Rrank : ℝ) (Hbr qS : ℕ)
    (cap cumulative pControl pPhase : ℕ → ℝ)
    (T : CertifiedFullChartFiniteHistory.BudgetedBranchTree Fmark bF ν hF J
      (fast).toSubmodule (eQ.baseChange ℝ) lift Z U poly N Bphase cap s pTree)
    (hHbr : 1 ≤ Hbr) (hqS : 0 < qS)
    (hpControl : ∀ r ≤ s, 0 ≤ pControl r)
    (hcumulative : ∀ r ≤ s, 0 ≤ cumulative r)
    (hmono : ∀ r < s, cumulative r ≤ cumulative (r + 1))
    (hcap : ∀ r < s, cap r ≤ cumulative (r + 1))
    (hprefix : ∀ r ≤ s, ∀ j < r, cap j ≤ cumulative r)
    (hdetect : ∀ r < s,
      (pPhase r + allocatedCandidateTerminalPhaseConstant s m aControl r) ^
        allocatedCandidateTerminalPhaseConstant s m aControl r ≤ cap r)
    (hκControl : ∀ r ≤ s, (Fintype.card κ : ℝ) ≤ pControl r)
    (hTagsControl : ∀ r ≤ s, (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ pControl r)
    (hHbrExp : ∀ r ≤ s, (Hbr : ℝ) ≤ Real.exp (pControl r))
    (hstructure : ∀ i j z, RationalHeightLE ((Fmark.associatedGradedBasis bF ν hF).repr
      ⁅Fmark.associatedGradedBasis bF ν hF i, Fmark.associatedGradedBasis bF ν hF j⁆ z) Hbr)
    (hden : ∀ r ≤ s, (qS : ℝ) * Real.exp ((s : ℝ) * (Fintype.card η : ℝ) * cumulative r) ≤
      Real.exp (pControl r))
    (hcost : ∀ r ≤ s, (Fintype.card η : ℝ) * Bbound * Real.exp (cumulative r) ≤
      Real.exp ((pControl r + 2) ^ aControl))
    (hentry : ∀ i j, |((Fmark.associatedGradedBasis bF ν hF).baseChange ℝ).repr
      (lift.baseChange ℝ ((eQ.baseChange ℝ) j)) i| ≤ Bbound)
    (hgrid : ∀ j, (fun i => ((Fmark.associatedGradedBasis bF ν hF).baseChange ℝ).repr
      (lift.baseChange ℝ ((eQ.baseChange ℝ) j)) i) ∈ realDenominatorGrid qS)
    (hdata : ∀ r, r < s → Nonempty
      (HistoryStageData (χ := χ r) (P := Pstage r) (keep := keep r) (hkeep := hkeep r)
        (bD := bD) (ω := ω) (hD := hD) (bF := bF) (ν := ν) (hF := hF) (hφ := hφ) (W := W) eQ r aLocal
        (cumulative r)
        ((pControl r + allocatedCandidateTerminalControlConstant s m aControl) ^
          allocatedCandidateTerminalControlConstant s m aControl)
        (pPhase r) Rrank (allocatedCandidateTerminalPhaseConstant s m aControl r))) :
    ∃ history ∈ T.level s,
      FullChartControlledFactors Fmark bF ν hF J poly N history.outer.1 history.outer.2
        ((pControl s + allocatedCandidateTerminalControlConstant s m aControl) ^
          allocatedCandidateTerminalControlConstant s m aControl) ∧
      RationalTaggedConstraintCertificate J Set.univ history.K (cumulative s)
        (s * (Fintype.card η * m)) ∧
      ∀ point ∈ history.K,
        eval₂ point (Fmark.realGradedSymbolPolynomial bF ν hF (fullTaggedVariableWeight J)
          (history.outer.1⁻¹ * Z * history.outer.2⁻¹).coord) ∈
            (fast).toSubmodule.baseChange ℝ := by
  have hconstants := Classical.choose_spec (Classical.choose_spec
    (exists_certified_budgeted_tree_terminal_constants s m aControl)).2
  obtain ⟨hcontrolled, hterminal⟩ := hconstants.2
    Fmark bF ν hF J (fast).toSubmodule (eQ.baseChange ℝ) lift hfast hsection
    Z U poly N Bphase Bbound pTree Rrank Hbr qS cap cumulative pControl pPhase T
    hHbr hqS hpControl hcumulative hmono hcap hprefix hdetect hκControl hTagsControl
    hHbrExp hstructure hden hcost hentry hgrid
  apply hterminal
  intro r hr history hmem
  obtain ⟨data⟩ := hdata r hr
  exact (Pstage r).exists_history_full_chart_major_correlation_witness_of_lengths (keep r) (hkeep r) bD ω hD bF ν hF hφ W
    eQ lift r aLocal data.hr Bphase (cumulative r)
    ((pControl r + allocatedCandidateTerminalControlConstant s m aControl) ^
      allocatedCandidateTerminalControlConstant s m aControl)
    history (hcontrolled r (Nat.le_of_lt hr) history hmem)
    (T.stage_bounds hmono hcap r (Nat.le_of_lt hr) history hmem).certificate
    data.HMap data.l data.pMap data.hHMap data.hl data.hpMap data.hentries data.hsource
    data.htarget data.hHMapExp data.hlExp data.H data.p data.qNative data.hH data.hp
    data.hκ data.hVars data.hχ data.hHExp data.hbracket data.hcommon data.hmapSlow
    data.hallowance data.hNreset data.vg data.hspan data.hvg data.hτ data.hξ data.hσone
    data.Cgeo data.hCgeo data.hchart data.hsmall data.hpoly data.pK data.Mbound data.LongSide
    data.hpK data.hBstage data.hJ data.hM data.hcap data.hLong data.hlong data.hthreshold
    data.hlength data.hfactor data.Hθ data.pLocal data.hθ data.hpLocal data.hLocalDim
    data.hLocalSize data.hLocalDen data.hNLocal data.pSlice data.pTest data.pNative (pPhase r)
    Rrank (allocatedCandidateTerminalPhaseConstant s m aControl r) data.hpNative data.hη
    data.hNativeMajor data.hproduct data.hdim data.hNmajor data.hRrank data.hrank
    data.Bshort data.hBshort data.hshort data.α data.hα data.hdirect data.hslice data.htest

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct BigOperators

noncomputable def allocatedCandidateCompositePhaseConstant
    (s m a Cnative r : ℕ) : ℕ :=
  Classical.choose (exists_preparedFiniteForward_composed_phase_cap Cnative
    (allocatedCandidateTerminalPhaseConstant s m a r))

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
    (stageCost stageMass stageScore : ℕ → ℝ)
    (Pstage : ∀ r, AllocatedExternalCandidateProblem (E := Deck) A D Fmark φ marked observable weight
      (stageCost r) (stageMass r) (stageScore r))
    (keep : ℕ → LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ r, ∀ z : (Pstage r).productive, ((Pstage r).chart z).keep = keep r)
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

theorem exists_forward_controlled_terminal_of_stage_refinements
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
    (aLocal : ℕ)
    (Bphase Bbound pTree Rrank : ℝ) (Hbr qS : ℕ)
    (scheduleExponent : ℕ) (x gainLog stageLog : ℝ)
    (T : CertifiedFullChartFiniteHistory.BudgetedBranchTree Fmark bF ν hF J
      (fast).toSubmodule (eQ.baseChange ℝ) lift Z U poly N Bphase
      (fun r => preparedFiniteForwardCap scheduleExponent countConstants r x) s pTree)
    (hx : 0 ≤ x) (hgain : gainLog ∈ Set.Icc 0 x) (hstage : stageLog ∈ Set.Icc 0 x)
    (Cnative : ℕ) (pMajor : ℕ → ℝ)
    (hMajorNonneg : ∀ r < s, 0 ≤ pMajor r)
    (hMajorBound : ∀ r < s, pMajor r ≤
      (preparedFiniteForwardSourcePrecision scheduleExponent countConstants r x gainLog stageLog +
        preparedFiniteForwardWork scheduleExponent countConstants r x + Cnative) ^ Cnative)
    (hphaseExponent : ∀ r < s,
      allocatedCandidateCompositePhaseConstant s m 1 Cnative r ≤ scheduleExponent)
    (hSchedule : 2 ≤ scheduleExponent) (hsSchedule : s + 3 ≤ scheduleExponent)
    (hControlSchedule : 4 * allocatedCandidateTerminalControlConstant s m 1 ≤ scheduleExponent)
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
    (hdata : ∀ r, r < s → Nonempty
      (HistoryStageData (χ := χ r) (P := Pstage r) (keep := keep r) (hkeep := hkeep r)
        (bD := bD) (ω := ω) (hD := hD) (bF := bF) (ν := ν) (hF := hF) (hφ := hφ) (W := W) eQ r aLocal
        (preparedFiniteForwardCumulative scheduleExponent countConstants r x)
        ((allocatedCandidateForwardControlInput s (Fintype.card η)
          (preparedFiniteForwardParameter scheduleExponent countConstants r x) +
          allocatedCandidateTerminalControlConstant s m 1) ^
          allocatedCandidateTerminalControlConstant s m 1)
        (pMajor r) Rrank (allocatedCandidateTerminalPhaseConstant s m 1 r))) :
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
  let pControl : ℕ → ℝ := fun r => allocatedCandidateForwardControlInput s (Fintype.card η)
    (preparedFiniteForwardParameter scheduleExponent countConstants r x)
  have hinput (r : ℕ) := allocatedCandidateForwardControlInput_bounds s (Fintype.card η)
    (preparedFiniteForwardParameter_nonneg scheduleExponent countConstants r hx)
  have hbase (r : ℕ) : x ≤ pControl r :=
    (le_preparedFiniteForwardParameter scheduleExponent countConstants r hx).trans (hinput r).2.1
  have hwork (r : ℕ) :
      (pControl r + allocatedCandidateTerminalControlConstant s m 1) ^
        allocatedCandidateTerminalControlConstant s m 1 ≤
      preparedFiniteForwardWork scheduleExponent countConstants r x := by
    rw [preparedFiniteForwardWork_eq]
    exact allocatedCandidateForwardControlInput_power_bound s (Fintype.card η)
      (allocatedCandidateTerminalControlConstant s m 1) scheduleExponent
      (preparedFiniteForwardParameter_nonneg scheduleExponent countConstants r hx)
      (hηBase.trans (le_preparedFiniteForwardParameter scheduleExponent countConstants r hx))
      hSchedule hsSchedule hControlSchedule
  have hden : ∀ r ≤ s, (qS : ℝ) * Real.exp ((s : ℝ) * (Fintype.card η : ℝ) *
      preparedFiniteForwardCumulative scheduleExponent countConstants r x) ≤ Real.exp (pControl r) := by
    intro r hr
    exact allocatedCandidateForwardControlInput_denominator_bound s (Fintype.card η) qS
      (preparedFiniteForwardParameter_nonneg scheduleExponent countConstants r hx)
      (le_preparedFiniteForwardParameter scheduleExponent countConstants r hx)
      (preparedFiniteForward_prefix_bounds scheduleExponent countConstants r hx).1.2 hqSBase
  have hcost : ∀ r ≤ s, (Fintype.card η : ℝ) * Bbound *
      Real.exp (preparedFiniteForwardCumulative scheduleExponent countConstants r x) ≤
        Real.exp ((pControl r + 2) ^ (1 : ℕ)) := by
    intro r hr
    simpa only [pow_one] using allocatedCandidateForwardControlInput_cost_bound s (Fintype.card η)
      (le_preparedFiniteForwardParameter scheduleExponent countConstants r hx)
      (preparedFiniteForward_prefix_bounds scheduleExponent countConstants r hx).1.2 hηBase hBboundBase
  have hdetect (r : ℕ) (hr : r < s) :
      (pMajor r + allocatedCandidateTerminalPhaseConstant s m 1 r) ^
        allocatedCandidateTerminalPhaseConstant s m 1 r ≤
      preparedFiniteForwardCap scheduleExponent countConstants r x := by
    have h := Classical.choose_spec (exists_preparedFiniteForward_composed_phase_cap Cnative
      (allocatedCandidateTerminalPhaseConstant s m 1 r))
    exact h.2 scheduleExponent countConstants r (hphaseExponent r hr) hx hgain hstage
      (hMajorNonneg r hr) (hMajorBound r hr)
  obtain ⟨history, hmem, hcontrol, hcertificate, hterminal⟩ :=
    exists_budgeted_tree_terminal_of_stage_refinements stageCost stageMass stageScore Pstage keep hkeep
      bD ω hD bF ν hF hφ W eQ lift hfast hsection 1 aLocal Bphase Bbound pTree Rrank Hbr qS
      (fun r => preparedFiniteForwardCap scheduleExponent countConstants r x)
      (fun r => preparedFiniteForwardCumulative scheduleExponent countConstants r x)
      pControl pMajor T hHbr hqS (fun r _ => (hinput r).1)
      (fun r _ => (preparedFiniteForward_prefix_bounds scheduleExponent countConstants r hx).1.1)
      (fun r _ => preparedFiniteForwardCumulative_le_succ scheduleExponent countConstants r hx)
      (fun r _ => preparedFiniteForwardCap_le_cumulative_succ scheduleExponent countConstants r hx)
      (fun r _ j hj => preparedFiniteForwardCap_le_cumulative scheduleExponent countConstants hx hj)
      hdetect (fun r _ => hκBase.trans (hbase r)) (fun r _ => hTagsBase.trans (hbase r))
      (fun r _ => hHbrBase.trans (Real.exp_le_exp.mpr (hbase r))) hstructure hden hcost hentry hgrid hdata
  exact ⟨history, hmem,
    FullChartControlledFactors.mono Fmark bF ν hF J poly N history.outer.1 history.outer.2 hcontrol (hwork s),
    hcertificate, hterminal⟩

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct BigOperators

noncomputable def allocatedCandidatePromotedMajorConstant (Csource : ℕ) : ℕ :=
  Classical.choose (exists_allocated_candidate_promoted_native_major_budget Csource)

noncomputable def allocatedCandidateForwardScheduleExponent
    (s m Cprimitive Csource extra : ℕ) : ℕ :=
  max extra (max (allocatedCandidateStageBaseExponent s m Cprimitive)
    (max (allocatedCandidateStageSliceExponent s m Cprimitive + 1)
      ((Finset.range s).sup fun r => allocatedCandidateCompositePhaseConstant s m 1
        (allocatedCandidatePromotedMajorConstant Csource) r)))

theorem allocatedCandidateForwardScheduleExponent_bounds
    (s m Cprimitive Csource extra : ℕ) :
    extra ≤ allocatedCandidateForwardScheduleExponent s m Cprimitive Csource extra ∧
    allocatedCandidateStageBaseExponent s m Cprimitive ≤
      allocatedCandidateForwardScheduleExponent s m Cprimitive Csource extra ∧
    allocatedCandidateStageSliceExponent s m Cprimitive + 1 ≤
      allocatedCandidateForwardScheduleExponent s m Cprimitive Csource extra ∧
    ∀ r < s, allocatedCandidateCompositePhaseConstant s m 1
      (allocatedCandidatePromotedMajorConstant Csource) r ≤
        allocatedCandidateForwardScheduleExponent s m Cprimitive Csource extra := by
  unfold allocatedCandidateForwardScheduleExponent
  refine ⟨le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _), ?_⟩
  intro r hr
  exact (Finset.le_sup (f := fun r => allocatedCandidateCompositePhaseConstant s m 1
    (allocatedCandidatePromotedMajorConstant Csource) r) (Finset.mem_range.mpr hr)).trans
      (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _))

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
    (stageCost stageMass stageScore : ℕ → ℝ)
    (Pstage : ∀ r, AllocatedExternalCandidateProblem (E := Deck) A D Fmark φ marked observable weight
      (stageCost r) (stageMass r) (stageScore r))
    (keep : ℕ → LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ r, ∀ z : (Pstage r).productive, ((Pstage r).chart z).keep = keep r)
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

theorem exists_forward_terminal_of_native_stage_data
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
    (Cprimitive Csource : ℕ) (sourceNative : ℕ → ℝ)
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
    (hdata : ∀ r, r < s → Nonempty
      (HistoryStageData (χ := χ r) (P := Pstage r) (keep := keep r) (hkeep := hkeep r)
        (bD := bD) (ω := ω) (hD := hD) (bF := bF) (ν := ν) (hF := hF) (hφ := hφ) (W := W) eQ r 1
        (preparedFiniteForwardCumulative scheduleExponent countConstants r x)
        ((allocatedCandidateForwardControlInput s (Fintype.card η)
          (preparedFiniteForwardParameter scheduleExponent countConstants r x) +
          allocatedCandidateTerminalControlConstant s m 1) ^
          allocatedCandidateTerminalControlConstant s m 1)
        (allocatedCandidateNativeMajorBudget
          (sourceNative r + allocatedCandidateStageBase s m Cprimitive
            (preparedFiniteForwardParameter scheduleExponent countConstants r x) + 2)
          (allocatedCandidateStageBase s m Cprimitive
            (preparedFiniteForwardParameter scheduleExponent countConstants r x))) Rrank (allocatedCandidateTerminalPhaseConstant s m 1 r))) :
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
  let v : ℕ → ℝ := fun r => allocatedCandidateStageBase s m Cprimitive
    (preparedFiniteForwardParameter scheduleExponent countConstants r x)
  let pMajor : ℕ → ℝ := fun r =>
    allocatedCandidateNativeMajorBudget (sourceNative r + v r + 2) (v r)
  have hv (r : ℕ) : 0 ≤ v r := (by norm_num : (0 : ℝ) ≤ 2).trans
    (allocatedCandidateStageBase_bounds s m Cprimitive
      (preparedFiniteForwardParameter_nonneg scheduleExponent countConstants r hx)).1
  have ht (r : ℕ) : 0 ≤ preparedFiniteForwardSourcePrecision scheduleExponent countConstants r x gainLog stageLog +
      preparedFiniteForwardWork scheduleExponent countConstants r x :=
    add_nonneg (preparedFiniteForward_model_precision_bounds scheduleExponent countConstants r hx hgain hstage).2.1
      (preparedFiniteForwardWork_nonneg scheduleExponent countConstants r hx)
  have hvt (r : ℕ) : v r ≤ preparedFiniteForwardSourcePrecision scheduleExponent countConstants r x gainLog stageLog +
      preparedFiniteForwardWork scheduleExponent countConstants r x :=
    (allocatedCandidateStageBase_le_forwardWork s m Cprimitive scheduleExponent countConstants r hx hBaseExponent).trans
      (le_add_of_nonneg_left
        (preparedFiniteForward_model_precision_bounds scheduleExponent countConstants r hx hgain hstage).2.1)
  have hMajorNonneg (r : ℕ) (hr : r < s) : 0 ≤ pMajor r := by
    apply allocatedCandidateNativeMajorBudget_nonneg _ (hv r)
    linarith only [hSourceNonneg r hr, hv r]
  have hMajorBound (r : ℕ) (hr : r < s) : pMajor r ≤
      (preparedFiniteForwardSourcePrecision scheduleExponent countConstants r x gainLog stageLog +
        preparedFiniteForwardWork scheduleExponent countConstants r x +
        allocatedCandidatePromotedMajorConstant Csource) ^ allocatedCandidatePromotedMajorConstant Csource := by
    exact (Classical.choose_spec
      (exists_allocated_candidate_promoted_native_major_budget Csource)).2 _ _ _
      (ht r) (hv r) (hvt r) (hSourceNonneg r hr) (hSourceBound r hr)
  have hBase := allocatedCandidateStageBaseExponent_bounds s m Cprimitive
  exact exists_forward_controlled_terminal_of_stage_refinements stageCost stageMass stageScore Pstage keep hkeep
    bD ω hD bF ν hF hφ W eQ lift hfast hsection 1 Bphase Bbound pTree Rrank Hbr qS
    scheduleExponent x gainLog stageLog T hx hgain hstage
    (allocatedCandidatePromotedMajorConstant Csource) pMajor hMajorNonneg hMajorBound hphaseExponent
    (hBase.1.trans hBaseExponent) (hBase.2.1.trans hBaseExponent)
    (hBase.2.2.1.trans hBaseExponent) hHbr hqS hκBase hTagsBase hηBase hHbrBase hqSBase
    hBboundBase hstructure hentry hgrid hdata

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

local notation "countConstants" =>
  (fun n => NilpotentLieFiltration.fullChartStageCountConstant (n + 1) 254)

theorem allocatedCandidateForwardMajor_cap
    (s m Cprimitive Csource A r : ℕ)
    {x gainLog stageLog sourceNative : ℝ}
    (hx : 0 ≤ x) (hgain : gainLog ∈ Set.Icc 0 x) (hstage : stageLog ∈ Set.Icc 0 x)
    (hSourceNonneg : 0 ≤ sourceNative)
    (hSourceBound : sourceNative ≤
      (preparedFiniteForwardSourcePrecision A countConstants r x gainLog stageLog +
        preparedFiniteForwardWork A countConstants r x + Csource) ^ Csource)
    (hBaseExponent : allocatedCandidateStageBaseExponent s m Cprimitive ≤ A)
    (hphaseExponent : allocatedCandidateCompositePhaseConstant s m 1
      (allocatedCandidatePromotedMajorConstant Csource) r ≤ A) :
    (allocatedCandidateNativeMajorBudget
        (sourceNative + allocatedCandidateStageBase s m Cprimitive
          (preparedFiniteForwardParameter A countConstants r x) + 2)
        (allocatedCandidateStageBase s m Cprimitive
          (preparedFiniteForwardParameter A countConstants r x)) +
      allocatedCandidateTerminalPhaseConstant s m 1 r) ^
        allocatedCandidateTerminalPhaseConstant s m 1 r ≤
      preparedFiniteForwardCap A countConstants r x := by
  let v := allocatedCandidateStageBase s m Cprimitive
    (preparedFiniteForwardParameter A countConstants r x)
  let pMajor := allocatedCandidateNativeMajorBudget (sourceNative + v + 2) v
  have hv : 0 ≤ v := (by norm_num : (0 : ℝ) ≤ 2).trans
    (allocatedCandidateStageBase_bounds s m Cprimitive
      (preparedFiniteForwardParameter_nonneg A countConstants r hx)).1
  have hprecision :=
    (preparedFiniteForward_model_precision_bounds A countConstants r hx hgain hstage).2.1
  have ht : 0 ≤ preparedFiniteForwardSourcePrecision A countConstants r x gainLog stageLog +
      preparedFiniteForwardWork A countConstants r x :=
    add_nonneg hprecision (preparedFiniteForwardWork_nonneg A countConstants r hx)
  have hvt : v ≤ preparedFiniteForwardSourcePrecision A countConstants r x gainLog stageLog +
      preparedFiniteForwardWork A countConstants r x :=
    (allocatedCandidateStageBase_le_forwardWork s m Cprimitive A countConstants r hx
      hBaseExponent).trans (le_add_of_nonneg_left hprecision)
  have hMajorNonneg : 0 ≤ pMajor := by
    apply allocatedCandidateNativeMajorBudget_nonneg _ hv
    linarith only [hSourceNonneg, hv]
  have hMajorBound : pMajor ≤
      (preparedFiniteForwardSourcePrecision A countConstants r x gainLog stageLog +
        preparedFiniteForwardWork A countConstants r x +
        allocatedCandidatePromotedMajorConstant Csource) ^ allocatedCandidatePromotedMajorConstant Csource :=
    (Classical.choose_spec
      (exists_allocated_candidate_promoted_native_major_budget Csource)).2 _ _ _
      ht hv hvt hSourceNonneg hSourceBound
  exact (Classical.choose_spec
    (exists_preparedFiniteForward_composed_phase_cap
      (allocatedCandidatePromotedMajorConstant Csource)
      (allocatedCandidateTerminalPhaseConstant s m 1 r))).2
    A countConstants r hphaseExponent hx hgain hstage hMajorNonneg hMajorBound

theorem allocatedCandidateForwardMajor_exp_le_cumulative
    (s m Cprimitive Csource A r : ℕ)
    {x gainLog stageLog sourceNative : ℝ}
    (hx : 0 ≤ x) (hgain : gainLog ∈ Set.Icc 0 x) (hstage : stageLog ∈ Set.Icc 0 x)
    (hSourceNonneg : 0 ≤ sourceNative)
    (hSourceBound : sourceNative ≤
      (preparedFiniteForwardSourcePrecision A countConstants r x gainLog stageLog +
        preparedFiniteForwardWork A countConstants r x + Csource) ^ Csource)
    (hBaseExponent : allocatedCandidateStageBaseExponent s m Cprimitive ≤ A)
    (hphaseExponent : allocatedCandidateCompositePhaseConstant s m 1
      (allocatedCandidatePromotedMajorConstant Csource) r ≤ A)
    (hr : r < s) :
    Real.exp ((allocatedCandidateNativeMajorBudget
        (sourceNative + allocatedCandidateStageBase s m Cprimitive
          (preparedFiniteForwardParameter A countConstants r x) + 2)
        (allocatedCandidateStageBase s m Cprimitive
          (preparedFiniteForwardParameter A countConstants r x)) +
      allocatedCandidateTerminalPhaseConstant s m 1 r) ^
        allocatedCandidateTerminalPhaseConstant s m 1 r) ≤
      Real.exp (preparedFiniteForwardCumulative A countConstants s x) := by
  exact Real.exp_le_exp.mpr
    ((allocatedCandidateForwardMajor_cap s m Cprimitive Csource A r hx hgain hstage
      hSourceNonneg hSourceBound hBaseExponent hphaseExponent).trans
      (preparedFiniteForwardCap_le_cumulative A countConstants hx hr))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open NilpotentLieFiltration

local notation "countConstants" => (fun r => fullChartStageCountConstant (r + 1) 254)

noncomputable def allocatedCandidateForwardTerminalScaleConstant
    (s m Cprimitive Csource extra : ℕ) : ℕ :=
  Classical.choose (exists_preparedFiniteForwardStage_budget s
    (allocatedCandidateForwardScheduleExponent s m Cprimitive Csource extra) countConstants)

theorem allocatedCandidateForwardTerminalScaleConstant_ge_two
    (s m Cprimitive Csource extra : ℕ) :
    2 ≤ allocatedCandidateForwardTerminalScaleConstant s m Cprimitive Csource extra :=
  (Classical.choose_spec (exists_preparedFiniteForwardStage_budget s
    (allocatedCandidateForwardScheduleExponent s m Cprimitive Csource extra) countConstants)).1

theorem allocatedCandidateForwardTerminalScale_bounds
    (s m Cprimitive Csource extra : ℕ) {x : ℝ} (hx : 0 ≤ x)
    (n : ℕ) (hn : n ≤ s) :
    let A := allocatedCandidateForwardScheduleExponent s m Cprimitive Csource extra
    let C := allocatedCandidateForwardTerminalScaleConstant s m Cprimitive Csource extra
    preparedFiniteForwardCumulative A countConstants n x ∈ Set.Icc 0 ((x + C) ^ C) ∧
      preparedFiniteForwardWork A countConstants n x ∈ Set.Icc 0 ((x + C) ^ C) ∧
      allocatedCandidateStageSlice s m Cprimitive
        (preparedFiniteForwardParameter A countConstants n x) ∈ Set.Icc 0 ((x + C) ^ C) := by
  let A := allocatedCandidateForwardScheduleExponent s m Cprimitive Csource extra
  let C := allocatedCandidateForwardTerminalScaleConstant s m Cprimitive Csource extra
  obtain ⟨_hp, hw, _hcap, _hcount, _hbranch, hcum, _hprefix, _hmodel, _hsource⟩ :=
    (Classical.choose_spec (exists_preparedFiniteForwardStage_budget s A countConstants)).2
      x 0 0 hx ⟨le_rfl, hx⟩ ⟨le_rfl, hx⟩ n hn
  have hA := allocatedCandidateForwardScheduleExponent_bounds s m Cprimitive Csource extra
  obtain ⟨hslice0, hsliceWork, _⟩ :=
    allocatedCandidateStageSlice_forward_bounds s m Cprimitive A countConstants n 0 hx
      (by simpa using hx) hA.2.2.1
  exact ⟨hcum, hw, hslice0, hsliceWork.trans hw.2⟩

theorem exists_allocatedCandidateForwardTerminalScale_budget
    (s m Cprimitive Csource extra : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ x : ℝ, 0 ≤ x →
      let A := allocatedCandidateForwardScheduleExponent s m Cprimitive Csource extra
      ∀ n : ℕ, n ≤ s →
        preparedFiniteForwardCumulative A countConstants n x ∈ Set.Icc 0 ((x + C) ^ C) ∧
        preparedFiniteForwardWork A countConstants n x ∈ Set.Icc 0 ((x + C) ^ C) ∧
        allocatedCandidateStageSlice s m Cprimitive
          (preparedFiniteForwardParameter A countConstants n x) ∈ Set.Icc 0 ((x + C) ^ C) := by
  refine ⟨allocatedCandidateForwardTerminalScaleConstant s m Cprimitive Csource extra,
    allocatedCandidateForwardTerminalScaleConstant_ge_two s m Cprimitive Csource extra, ?_⟩
  intro x hx
  dsimp only
  intro n hn
  exact allocatedCandidateForwardTerminalScale_bounds s m Cprimitive Csource extra hx n hn

theorem allocatedCandidateForwardTerminalScale_thresholds
    (s m Cprimitive Csource extra : ℕ) {x scale : ℝ} (hx : 0 ≤ x)
    (hscale : Real.exp ((x + allocatedCandidateForwardTerminalScaleConstant
      s m Cprimitive Csource extra) ^
        allocatedCandidateForwardTerminalScaleConstant s m Cprimitive Csource extra) ≤ scale)
    (n : ℕ) (hn : n ≤ s) :
    let A := allocatedCandidateForwardScheduleExponent s m Cprimitive Csource extra
    Real.exp (preparedFiniteForwardCumulative A countConstants n x) ≤ scale ∧
      Real.exp (preparedFiniteForwardWork A countConstants n x) ≤ scale ∧
      Real.exp (allocatedCandidateStageSlice s m Cprimitive
        (preparedFiniteForwardParameter A countConstants n x)) ≤ scale := by
  obtain ⟨hcum, hwork, hslice⟩ :=
    allocatedCandidateForwardTerminalScale_bounds s m Cprimitive Csource extra hx n hn
  exact ⟨(Real.exp_le_exp.mpr hcum.2).trans hscale,
    (Real.exp_le_exp.mpr hwork.2).trans hscale,
    (Real.exp_le_exp.mpr hslice.2).trans hscale⟩

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

theorem exists_forward_terminal_of_frozen_candidates
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
  exact ⟨(freezing r).historyStageData_of_original_factors (χ := χ r) (keep r) (hkeep r)
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
    (vg r) (hspan r hr) (hvg r hr) hθ hOriginal hτ hξ hσone Cgeo hCgeo hchart hsmall hpoly
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

theorem exists_early_forward_terminal_of_frozen_candidates
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
  exact P.exists_forward_terminal_of_frozen_candidates keep bD ω hD bF ν hF hφ W
    eQ lift hfast hsection (preparedFiniteForwardCumulative scheduleExponent countConstants s x) Bbound
    (preparedFiniteForwardParameter scheduleExponent countConstants s x) Rrank Hbr qS scheduleExponent x
    gainLog stageLog T hx hgain hstage Cprimitive Csource sourceNative pTest α hSourceNonneg hSourceBound
    hBaseExponent hphaseExponent hHbr hqS hκBase hTagsBase hηBase hHbrBase hqSBase hBboundBase hstructure
    hentry hgrid hcost HMap l H Hθ qNative hHMap hl hH hHMapExp hlExp hHExp hHθExp hqNative hentries
    hsource htarget hκ hχ htags hsampler hJ hbracket vg hspan hvg hθ hOriginal hτ hξ hσone Cgeo hCgeo
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

theorem exists_early_forward_terminal_of_common_fast_generators
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
  exact P.exists_early_forward_terminal_of_frozen_candidates keep bD ω hD bF ν hF hφ W
    eQ lift hfast hsection Bbound Rrank Hbr qS scheduleExponent x
    gainLog stageLog hx hgain hstage Cprimitive Csource sourceNative pTest α hSourceNonneg hSourceBound
    hBaseExponent hphaseExponent hHbr hqS hκBase hTagsBase hηBase hmEarly hblocksEarly
    hHbrBase hqSBase hBboundBase hstructure hentry hgrid hcost HMap l H Hθ qNative
    hHMap hl hH hHMapExp hlExp hHExp hHθExp hqNative hentries hsource htarget hκ hχ htags
    hsampler hJ hbracket vg hspan hvg hθ hOriginal hτ hξ hσone Cgeo hCgeo hchart hsmall
    hpoly hkept hfrozen hTest hα hdirect hN hRrank hrank

end AllocatedExternalCandidateProblem
end Erdos3.VectorPolynomial

end

end OAI
