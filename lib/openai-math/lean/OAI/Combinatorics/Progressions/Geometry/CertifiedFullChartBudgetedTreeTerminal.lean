import OAI.Combinatorics.Progressions.Geometry.CertifiedFullChartBudgetedTreeBounds

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory
open Module VectorPolynomial
open scoped TensorProduct Classical

attribute [local irreducible] FullChartAdmissibleStageCorrection
  realSymbolGradeEvaluation restrictedMajorCorrection outer

theorem exists_budgeted_reached_child_of_major_correlation_witness (m n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {X L ι η : Type} [Fintype X] [DecidableEq X] [Fintype η]
        [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
        (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
        (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
        (J : Fin m → Type) [∀ j, Fintype (J j)]
        (fast : Submodule ℚ F.AssociatedGraded)
        (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
        (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded),
      BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω fast →
      (∀ y, fast.mkQ (lift y) = y) →
      ∀ (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ)
        (Bphase pTree pPhase Rrank : ℝ) (stageBudget : ℕ → ℝ) (depth : ℕ)
        (T : BudgetedBranchTree F b ω hF J fast basis lift Z U poly N Bphase stageBudget depth pTree)
        (H : CertifiedFullChartFiniteHistory F b ω hF J fast basis lift Z
          Set.univ U poly N Bphase n),
      n < depth → H ∈ T.level n → (pPhase + C) ^ C ≤ stageBudget n →
      Nonempty (FullChartMajorCorrelationWitness F b ω hF J (n + 1) fast basis
        Z H.outer.1 H.outer.2 N poly U pPhase Rrank C) →
      ∃ (q : ℕ) (K : Set ((X ⊕ (Σ j, J j)) → ℝ))
        (pair : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)) ×
          VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))),
        FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
          Z H.outer.1 H.outer.2 H.K U poly N ((pPhase + C) ^ C) q K pair ∧
        ∃ Hnext ∈ T.level (n + 1),
          AdmissibleChildAt F b ω hF J fast basis lift Z U poly N Bphase (stageBudget n) H Hnext ∧
          RepresentsCorrection F b ω hF J fast basis lift Z U poly N Bphase Hnext q K pair := by
  obtain ⟨C, hC, hsource⟩ :=
    exists_certified_full_chart_decomposition_of_major_correlation_witness m (n + 1) (by omega)
  refine ⟨C, hC, ?_⟩
  intro X L ι η _ _ _ _ _ s F b ω hF J _ fast basis lift hfast hsection
    Z U poly N Bphase pTree pPhase Rrank stageBudget depth T H hn hH hbudget hcorrelation
  have hlower : ∀ t ∈ H.K, ∀ j < n + 1,
      F.realSymbolGradeEvaluation b ω hF (fullTaggedVariableWeight J) j t
        (H.outer.1⁻¹ * Z * H.outer.2⁻¹).coord ∈ fast.baseChange ℝ := by
    intro t ht j hj
    exact H.invariant_outer t ht j (by omega)
  have hdecomposition := hsource F b ω hF J fast basis lift hfast hsection
    Z H.outer.1 H.outer.2 H.K H.dilation hlower N poly U pPhase Rrank hcorrelation
  obtain ⟨q, K, pair, hpair⟩ :=
    CertifiedFullChartDetectedDecomposition.exists_admissible_stage
      F b ω hF J (n + 1) fast basis lift Z H.outer.1 H.outer.2 H.K U poly N
      ((pPhase + C) ^ C) hdecomposition
  refine ⟨q, K, pair, hpair, ?_⟩
  have hpairB := FullChartAdmissibleStageCorrection.mono_budget hpair hbudget
  exact T.exists_representative_child hn hH q K pair hpairB

end Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial
open scoped TensorProduct Classical

attribute [local irreducible] FullChartAdmissibleStageCorrection
  realSymbolGradeEvaluation restrictedMajorCorrection
  CertifiedFullChartFiniteHistory.outer

theorem exists_certified_budgeted_tree_terminal_constants (s m a : ℕ) :
    ∃ Ccontrol : ℕ, 2 ≤ Ccontrol ∧ ∃ Cphase : ℕ → ℕ,
      (∀ n, 2 ≤ Cphase n) ∧
    ∀ {X L ι η : Type} [Fintype X] [DecidableEq X] [Fintype ι] [Fintype η]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (J : Fin m → Type) [∀ j, Fintype (J j)]
      (fast : Submodule ℚ F.AssociatedGraded)
      (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
      (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded),
      BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω fast →
      (∀ y, fast.mkQ (lift y) = y) →
    ∀ (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
      (Utag : ∀ j, Submodule ℝ (J j → ℝ))
      (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ)
      (Bphase B pTree Rrank : ℝ) (H qS : ℕ)
      (cap cumulative pControl pPhase : ℕ → ℝ)
      (T : CertifiedFullChartFiniteHistory.BudgetedBranchTree F b ω hF J fast basis lift
        Z Utag poly N Bphase cap s pTree),
      1 ≤ H → 0 < qS →
      (∀ n ≤ s, 0 ≤ pControl n) →
      (∀ n ≤ s, 0 ≤ cumulative n) →
      (∀ n < s, cumulative n ≤ cumulative (n + 1)) →
      (∀ n < s, cap n ≤ cumulative (n + 1)) →
      (∀ n ≤ s, ∀ j < n, cap j ≤ cumulative n) →
      (∀ n < s, (pPhase n + Cphase n) ^ Cphase n ≤ cap n) →
      (∀ n ≤ s, (Fintype.card ι : ℝ) ≤ pControl n) →
      (∀ n ≤ s, (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ pControl n) →
      (∀ n ≤ s, (H : ℝ) ≤ Real.exp (pControl n)) →
      (∀ i j z, RationalHeightLE ((F.associatedGradedBasis b ω hF).repr
        ⁅F.associatedGradedBasis b ω hF i, F.associatedGradedBasis b ω hF j⁆ z) H) →
      (∀ n ≤ s, (qS : ℝ) * Real.exp ((s : ℝ) * (Fintype.card η : ℝ) * cumulative n) ≤
        Real.exp (pControl n)) →
      (∀ n ≤ s, (Fintype.card η : ℝ) * B * Real.exp (cumulative n) ≤
        Real.exp ((pControl n + 2) ^ a)) →
      (∀ i j, |((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
        (lift.baseChange ℝ (basis j)) i| ≤ B) →
      (∀ j, (fun i => ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
        (lift.baseChange ℝ (basis j)) i) ∈ realDenominatorGrid qS) →
      (∀ n, n ≤ s → ∀ history ∈ T.level n,
        FullChartControlledFactors F b ω hF J poly N history.outer.1 history.outer.2
          ((pControl n + Ccontrol) ^ Ccontrol)) ∧
      ((∀ n, n < s → ∀ history ∈ T.level n,
        Nonempty (FullChartMajorCorrelationWitness F b ω hF J (n + 1) fast basis
          Z history.outer.1 history.outer.2 N poly Utag (pPhase n) Rrank (Cphase n))) →
    ∃ history ∈ T.level s,
      FullChartControlledFactors F b ω hF J poly N history.outer.1 history.outer.2
        ((pControl s + Ccontrol) ^ Ccontrol) ∧
      RationalTaggedConstraintCertificate J Set.univ history.K (cumulative s)
        (s * (Fintype.card η * m)) ∧
      ∀ point ∈ history.K,
        eval₂ point (F.realGradedSymbolPolynomial b ω hF (fullTaggedVariableWeight J)
          (history.outer.1⁻¹ * Z * history.outer.2⁻¹).coord) ∈ fast.baseChange ℝ) := by
  obtain ⟨Ccontrol, hCcontrol, hcontrol⟩ := exists_certified_full_chart_history_control s a
  let Cphase : ℕ → ℕ := fun n => Classical.choose
    (CertifiedFullChartFiniteHistory.exists_budgeted_reached_child_of_major_correlation_witness m n)
  have hphase (n : ℕ) := Classical.choose_spec
    (CertifiedFullChartFiniteHistory.exists_budgeted_reached_child_of_major_correlation_witness m n)
  refine ⟨Ccontrol, hCcontrol, Cphase, fun n => (hphase n).1, ?_⟩
  intro X L ι η _ _ _ _ _ _ F b ω hF J _ fast basis lift hfast hsection
    Z Utag poly N Bphase B pTree Rrank H qS cap cumulative pControl pPhase T hH hqS
    hp hcumulative hmono hcap hprefix hdetect hι hσ hHp hstructure hden hcost hentry hgrid
  have hbounds := T.stage_bounds hmono hcap
  have hcontrolled (n : ℕ) (hn : n ≤ s)
      (history : CertifiedFullChartFiniteHistory F b ω hF J fast basis lift
        Z Set.univ Utag poly N Bphase n) (hmem : history ∈ T.level n) :
      FullChartControlledFactors F b ω hF J poly N history.outer.1 history.outer.2
        ((pControl n + Ccontrol) ^ Ccontrol) := by
    let hsmall := (hbounds n hn history hmem).to_budget (hprefix n hn)
    have hactual := hcontrol F b ω hF J fast basis lift Z Set.univ Utag poly N
      (cumulative n) B (pControl n) H qS n hH (hp n hn) (hcumulative n hn) hqS hn
      (hι n hn) (hσ n hn) (hHp n hn) hstructure (hden n hn) (hcost n hn)
      hentry hgrid hsmall
    dsimp only [hsmall] at hactual
    rw [(hbounds n hn history hmem).to_budget_outer (hprefix n hn)] at hactual
    exact hactual
  refine ⟨hcontrolled, ?_⟩
  intro hsource
  have hreached : ∀ n, n ≤ s → (T.level n).Nonempty := by
    intro n
    induction n with
    | zero =>
      intro _
      exact ⟨CertifiedFullChartFiniteHistory.univInitialHistory F b ω hF J fast basis lift
        Z Utag poly N Bphase, by
          change _ ∈ finiteGradedBranchLevel _ _ 0
          exact (finiteGradedBranchLevel_mem_zero _ _ _).mpr rfl⟩
    | succ n ih =>
      intro hn
      have hns : n < s := Nat.lt_of_succ_le hn
      obtain ⟨history, hmem⟩ := ih (Nat.le_of_succ_le hn)
      have hcorr := hsource n hns history hmem
      obtain ⟨q, K, pair, _, next, hnext, _, _⟩ := (hphase n).2
        F b ω hF J fast basis lift hfast hsection Z Utag poly N Bphase pTree
        (pPhase n) Rrank cap s T history hns hmem (hdetect n hns) hcorr
      exact ⟨next, hnext⟩
  obtain ⟨history, hmem⟩ := hreached s le_rfl
  exact ⟨history, hmem, hcontrolled s le_rfl history hmem,
    (hbounds s le_rfl history hmem).certificate, history.terminal_mem_fast hfast⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
