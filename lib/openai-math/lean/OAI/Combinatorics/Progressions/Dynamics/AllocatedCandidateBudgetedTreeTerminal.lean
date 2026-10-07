import OAI.Combinatorics.Progressions.Estimates.AllocatedCandidateStageDataConstruction
import OAI.Combinatorics.Progressions.Geometry.CertifiedFullChartBudgetedTreeTerminal

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped Classical TensorProduct BigOperators

noncomputable def allocatedCandidateTerminalControlConstant (s m a : ℕ) : ℕ :=
  Classical.choose (exists_certified_budgeted_tree_terminal_constants s m a)

noncomputable def allocatedCandidateTerminalPhaseConstant (s m a : ℕ) : ℕ → ℕ :=
  Classical.choose (Classical.choose_spec
    (exists_certified_budgeted_tree_terminal_constants s m a)).2

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

theorem exists_budgeted_tree_terminal_of_stage_data
    [Fintype (SymbolBasisIndex (fun _ : Vars => 1) ω)]
    [Fintype (SymbolBasisIndex (fun _ : Vars => 1) ν)]
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
      (HistoryStageData (χ := χ) (P := P) (keep := keep) (hkeep := hkeep)
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
  exact P.exists_history_full_chart_major_correlation_witness_of_lengths keep hkeep bD ω hD bF ν hF hφ W
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

end OAI
