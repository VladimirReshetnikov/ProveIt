import OAI.Combinatorics.Progressions.Dynamics.FastTerminalBudget
import OAI.Combinatorics.Progressions.Dynamics.FormalGeometryBudget
import OAI.Combinatorics.Progressions.Dynamics.UniformFormalInductionIteration
import OAI.Combinatorics.Progressions.Linear.BoundedSpanningPadding
import OAI.Combinatorics.Progressions.Linear.FullFastRelativeSpanning
import OAI.Combinatorics.Progressions.Linear.StepDropBasisBudget

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype ι] [Fintype κ] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "ωW" => (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val a))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)

theorem exists_full_fast_quotient_bases
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded)
    (hspan : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    {H : ℕ} (hH : 1 ≤ H) (hv : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H)
    {p : ℝ} (hp : 0 ≤ p)
    (hdim : 2 * (Fintype.card ι : ℝ) + (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) :
    ∃ H' : ℕ, H ≤ H' ∧ 1 ≤ H' ∧ (H' : ℝ) ≤ Real.exp ((p + 2) ^ 294) ∧
      ∃ dU : ℕ, dU ≤ Fintype.card ι ∧
      ∃ fU : Basis (Fin dU) ℚ (F.AssociatedGraded ⧸ (F.fullFastGradedDiagonal W).toSubmodule),
      ∃ dV : ℕ, dV ≤ Fintype.card ι ∧
      ∃ fV : Basis (Fin dV) ℚ (F.AssociatedGraded ⧸ F.fullFastGradedRelative e ω hF W),
        (∀ i j, RationalHeightLE (fU.repr ((F.fullFastGradedDiagonal W).toSubmodule.mkQ
          (F.associatedGradedBasis e ω hF j)) i) H') ∧
        (∀ i j, RationalHeightLE (fV.repr ((F.fullFastGradedRelative e ω hF W).mkQ
          (F.associatedGradedBasis e ω hF j)) i) H') := by
  have hn0 : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have hm0 : 0 ≤ (Fintype.card κ : ℝ) := Nat.cast_nonneg _
  have hm : (Fintype.card κ : ℝ) ≤ p := by linarith
  have hUcard : (Fintype.card (κ ⊕ TopGradedBasisIndex s ω) : ℝ) ≤ p := by
    have h := Nat.cast_le (α := ℝ).mpr (fullFastDiagonalGenerators_card (κ := κ) (s := s) ω)
    push_cast at h
    linarith
  obtain ⟨HU, hHU, hHUp, dU, hdU, fU, hfU⟩ := exists_submodule_quotient_basis_exp
    (F.associatedGradedBasis e ω hF) (F.fullFastGradedDiagonal W).toSubmodule
    (F.fullFastDiagonalGenerators e ω hF v) (F.fullFastDiagonalGenerators_span e ω hF W v hspan)
    hH (F.fullFastDiagonalGenerators_height e ω hF v hH hv) hp hUcard hHp
  have hn : (Fintype.card (ReducedSquareBasisIndex s ω) : ℝ) ≤ p := by
    have hcard : Fintype.card (ReducedSquareBasisIndex s ω) ≤ 2 * Fintype.card ι :=
      (Fintype.card_subtype_le _).trans (card_squareBasis_index_le ω)
    have h := Nat.cast_le (α := ℝ).mpr hcard
    push_cast at h
    linarith
  have hq : (Fintype.card (QuotientTopBasisIndex s ω) : ℝ) ≤ p := by
    have h := Nat.cast_le (α := ℝ).mpr
      (Fintype.card_subtype_le (fun i : ι => ¬ s + 1 ≤ ω i))
    linarith
  obtain ⟨Hz, hHz, hHzp, z, hz, hzh⟩ :=
    F.exists_full_fast_relative_generators_exp e ω hF W v hspan hH hv hp hn hm hq hHp
  obtain ⟨HV, hHV, hHVp, dV, hdV, fV, hfV⟩ := exists_submodule_quotient_basis_exp
    (F.associatedGradedBasis e ω hF) (F.fullFastGradedRelative e ω hF W) z hz hHz hzh
    (by positivity : 0 ≤ (p + 2) ^ 40)
    (hm.trans (le_power_budget hp (by decide : 1 ≤ 40))) hHzp
  have hVbudget : (HV : ℝ) ≤ Real.exp ((p + 2) ^ 294) :=
    exponential_budget_comp hp (by positivity) 40 7 le_rfl hHVp
  have hUbudget : (HU : ℝ) ≤ Real.exp ((p + 2) ^ 294) := hHUp.trans
    (Real.exp_le_exp.mpr (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + 2) (by decide : 7 ≤ 294)))
  have hbudget : (H : ℝ) ≤ Real.exp ((p + 2) ^ 294) :=
    hHp.trans (Real.exp_le_exp.mpr (le_power_budget hp (by decide : 1 ≤ 294)))
  refine ⟨max H (max HU HV), Nat.le_max_left _ _, hH.trans (Nat.le_max_left _ _), ?_,
    dU, hdU, fU, dV, hdV, fV, ?_, ?_⟩
  · rw [Nat.cast_max, Nat.cast_max]
    exact max_le hbudget (max_le hUbudget hVbudget)
  · intro i j
    exact (hfU i j).mono ((Nat.le_max_left HU HV).trans (Nat.le_max_right _ _))
  · intro i j
    exact (hfV i j).mono ((Nat.le_max_right HU HV).trans (Nat.le_max_right _ _))

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_uniform_formal_induction_factorization (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧
    ∀ {L μ ι κ σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [Fintype μ] [Fintype ι] [Fintype κ] [Fintype σ]
    (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
    (_hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
    (_hgraded : BasisHomogeneousBrackets b w) (_hs : 2 ≤ s)
    (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)) (V K : Submodule ℚ L)
    (_hUV : ∀ u ∈ U, ∀ v ∈ V.baseChange ℝ, ⁅u, v⁆ ∈ V.baseChange ℝ)
    (_hU : BasisGradedSubmodule (b.baseChange ℝ) w U.toSubmodule)
    (_hV : BasisGradedSubmodule (b.baseChange ℝ) w (V.baseChange ℝ))
    (eK : Basis κ ℚ K) (f : Basis ι ℚ (L ⧸ V))
    (_hK : ∀ x ∈ K.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w 1 x = x)
    {H : ℕ} (_hH : 1 ≤ H)
    (G : ∀ j, 2 ≤ j → j ≤ s → FormalStageGeometry b w U V K eK f j H)
    (_hKernelBasis : ∀ i z, RationalHeightLE (b.repr (eK z : L) i) H)
    (_hQuotient : ∀ i z, RationalHeightLE (f.repr (V.mkQ (b z)) i) H)
    (_hStructure : ∀ i z r, RationalHeightLE (b.repr ⁅b i, b z⁆ r) H)
    {p : ℝ} (_hp : 0 ≤ p)
    (_hμ : (Fintype.card μ : ℝ) ≤ p) (_hι : (Fintype.card ι : ℝ) ≤ p)
    (_hκ : (Fintype.card κ : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hRanks : ∀ j hj hjs, ((G j hj hjs).bracketRank : ℝ) ≤ p ∧
      ((G j hj hjs).currentRank : ℝ) ≤ p)
    (_hsp : (s : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + E) ^ E) ≤ T i)
    (X : F.FormalInductionState b w U V K eK T 2 p),
    ∃ q : ℝ, p ≤ q ∧ 0 ≤ q ∧ q ≤ (p + E) ^ E ∧
      ∃ W : F.FormalInductionRun b w U V K eK T X.P (s - 1) q,
        (W.denominator : ℝ) ≤ Real.exp ((p + E) ^ E) ∧
        ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + E) ^ E) ∧ W.denominator ∣ m ∧
          CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + E) ^ E)) W.left.prod.coord ∧
          CoefficientGrid (b.baseChange ℝ) m W.right.prod.coord ∧
          F.FormalCorrectionProperty b w U W.left.prod ∧
          F.FormalCorrectionProperty b w U W.right.prod := by
  obtain ⟨D, _, hiteration⟩ := exists_uniform_formal_induction_iteration s
  obtain ⟨C, _, hproducts⟩ := exists_formal_induction_run_product_controls s
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C D) ^ D
  obtain ⟨E, hE, hbudget⟩ := exists_natPolynomial_eval_budget (Q + (Q + Polynomial.C C) ^ C)
  refine ⟨E, hE, ?_⟩
  intro L μ ι κ σ _ _ _ _ _ _ F b w hF hgraded hs U V K hUV hU hV eK f hK H hH G
    hKernelBasis hQuotient hStructure p hp hμ hι hκ hσ hRanks hsp hHp T hT X
  let t := (p + D) ^ D
  let z := (t + C) ^ C
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have htotal : t + z ≤ (p + E) ^ E := by
    simpa [Q, t, z, Polynomial.eval₂_pow] using hbudget p hp
  have htcap : t ≤ (p + E) ^ E := by linarith
  have hzcap : z ≤ (p + E) ^ E := by linarith
  have hT' : ∀ i, Real.exp ((p + D) ^ D) ≤ T i :=
    fun i => (Real.exp_le_exp.mpr htcap).trans (hT i)
  obtain ⟨q, hpq, hq, hqt, W, hWden⟩ :=
    hiteration F b w hF hgraded hs U V K hUV hU hV eK f hK hH G
      hKernelBasis hQuotient hStructure hp hμ hι hκ hσ hRanks hsp hHp T hT' X
  have hpt : p ≤ t := hpq.trans hqt
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  obtain ⟨m, hm, hmp, hdm, hleft, hright, hleftGood, hrightGood⟩ :=
    hproducts F b w hF hgraded hTpos (Nat.sub_le s 1) W hH hStructure ht hqt
      (hμ.trans hpt) (hσ.trans hpt) (hHp.trans (Real.exp_le_exp.mpr hpt)) hWden
  exact ⟨q, hpq, hq, hqt.trans htcap, W,
    hWden.trans (Real.exp_le_exp.mpr htcap), m, hm,
    hmp.trans (Real.exp_le_exp.mpr hzcap), hdm,
    hleft.mono _ T hTpos (Real.exp_le_exp.mpr hzcap), hright, hleftGood, hrightGood⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_formal_stepDrop_subalgebra_factorization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L μ υ χ ι κ σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [Fintype μ] [Fintype υ] [Fintype χ] [Fintype ι] [Fintype κ] [Fintype σ]
    (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
    (_hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
    (_hgraded : BasisHomogeneousBrackets b w) (_hs : 2 ≤ s)
    (U : LieSubalgebra ℚ L) (V K : Submodule ℚ L)
    (_hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (_hU : BasisGradedSubmodule b w U.toSubmodule) (_hV : BasisGradedSubmodule b w V)
    (η : L →ₗ[ℚ] ℚ) (_hη : ∀ x ∈ V, basisGradeProjection b w s x = x → η x = 0)
    (eK : Basis κ ℚ K) (f : Basis ι ℚ (L ⧸ V))
    (fU : Basis υ ℚ (L ⧸ U.toSubmodule)) (fK : Basis χ ℚ (L ⧸ K))
    (_hK : ∀ x ∈ K.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w 1 x = x)
    {H : ℕ} (_hH : 1 ≤ H)
    (G : ∀ j, 2 ≤ j → j ≤ s →
      FormalStageGeometry b w (realificationLieSubalgebra U) V K eK f j H)
    (_hKernelBasis : ∀ i z, RationalHeightLE (b.repr (eK z : L) i) H)
    (_hQuotient : ∀ i z, RationalHeightLE (f.repr (V.mkQ (b z)) i) H)
    (_hQuotientU : ∀ i z, RationalHeightLE (fU.repr (U.toSubmodule.mkQ (b z)) i) H)
    (_hQuotientK : ∀ i z, RationalHeightLE (fK.repr (K.mkQ (b z)) i) H)
    (_hStructure : ∀ i z r, RationalHeightLE (b.repr ⁅b i, b z⁆ r) H)
    {p : ℝ} (_hp : 0 ≤ p)
    (_hμ : (Fintype.card μ : ℝ) ≤ p) (_hυ : (Fintype.card υ : ℝ) ≤ p)
    (_hχ : (Fintype.card χ : ℝ) ≤ p) (_hι : (Fintype.card ι : ℝ) ≤ p)
    (_hκ : (Fintype.card κ : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hRanks : ∀ j hj hjs, ((G j hj hjs).bracketRank : ℝ) ≤ p ∧
      ((G j hj hjs).currentRank : ℝ) ≤ p)
    (_hsp : (s : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (X : F.FormalInductionState b w (realificationLieSubalgebra U) V K eK T 2 p),
    ∃ Z : LieSubalgebra ℚ L, BasisGradedSubmodule b w Z.toSubmodule ∧
      (∀ x ∈ Z, η (basisGradeProjection b w s x) = 0) ∧
      ∃ e : Basis (Fin (Module.finrank ℚ Z)) ℚ Z,
        (∀ i j, ((b.repr (e i : L) j).num.natAbs : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ((b.repr (e i : L) j).den : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
        ∃ A P B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot,
          A * P * B = X.P ∧
          F.FormalCorrectionProperty b w (realificationLieSubalgebra U) A ∧
          F.FormalCorrectionProperty b w (realificationLieSubalgebra U) B ∧
          coefficients P.coord 0 = 0 ∧
          P.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) ∧
          (∀ α, coefficients P.coord α ∈ realificationLieSubalgebra Z) ∧
          CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + C) ^ C)) A.coord ∧
          ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
            CoefficientGrid (b.baseChange ℝ) m B.coord := by
  obtain ⟨E, hE, hfactor⟩ := exists_uniform_formal_induction_factorization s
  obtain ⟨D, hD, hbasis⟩ := exists_stepDrop_basis_uniform_budget
  let C := max E D
  refine ⟨C, hE.trans (Nat.le_max_left E D), ?_⟩
  intro L μ υ χ ι κ σ _ _ _ _ _ _ _ _ F b w hF hgraded hs U V K hUV hU hV η hη eK f
    fU fK hK H hH G hKernelBasis hQuotient hQuotientU hQuotientK hStructure
    p hp hμ hυ hχ hι hκ hσ hRanks hsp hHp T hT X
  have hEC : (p + E) ^ E ≤ (p + C) ^ C :=
    shifted_power_self_mono hp (by omega) (Nat.le_max_left E D)
  have hDC : (p + D) ^ D ≤ (p + C) ^ C :=
    shifted_power_self_mono hp (by omega) (Nat.le_max_right E D)
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hRU : BasisGradedSubmodule (b.baseChange ℝ) w (realificationLieSubalgebra U).toSubmodule :=
    hU.baseChange b w U.toSubmodule
  have hRV := hV.baseChange b w V
  have hRUV : ∀ u ∈ realificationLieSubalgebra U, ∀ v ∈ V.baseChange ℝ, ⁅u, v⁆ ∈ V.baseChange ℝ :=
    fun _ hu _ hv => lie_mem_real_baseChange U.toSubmodule V V hUV hu hv
  obtain ⟨q, _, _, _, W, _, m, hm, hmbound, _, hleft, hright, hleftGood, hrightGood⟩ :=
    hfactor F b w hF hgraded hs (realificationLieSubalgebra U) V K hRUV hRU hRV eK f hK hH G
      hKernelBasis hQuotient hStructure hp hμ hι hκ hσ hRanks hsp hHp T
      (fun i => (Real.exp_le_exp.mpr hEC).trans (hT i)) X
  obtain ⟨e, he⟩ := hbasis b w U V K fU fK f eK hH hQuotientU hQuotientK hQuotient
    hKernelBasis hStructure hp hμ hυ hχ hκ hι hHp
  let Z := stepDropSubalgebra b w (F.adaptedBasis_weight_pos b w hF) hgraded U V K hU hUV
  have hcoeff : ∀ α, coefficients W.state.P.coord α ∈ realificationLieSubalgebra Z := by
    intro α
    exact W.terminal_coefficients_mem_rational_stepDrop hs hF α
  refine ⟨Z, stepDropSubmodule_graded b w U V K hU hV,
    (fun _ hx => stepDropSubmodule_top_frequency b w U V K hU hV η hs hη hx), e, ?_,
    W.left.prod, W.state.P, W.right.prod, W.factorization, hleftGood, hrightGood,
    W.state.constant_zero, W.state.graded, hcoeff,
    hleft.mono _ T hTpos (Real.exp_le_exp.mpr hEC), m, hm,
    hmbound.trans (Real.exp_le_exp.mpr hEC), hright⟩
  intro i j
  exact ⟨(he i j).1.trans (Real.exp_le_exp.mpr hDC), (he i j).2.trans (Real.exp_le_exp.mpr hDC)⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_stepDrop_from_formal_state (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L μ υ χ ι κ σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [Fintype μ] [Fintype υ] [Fintype χ] [Fintype ι] [Fintype κ] [Fintype σ]
    (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
    (_hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
    (_hgraded : BasisHomogeneousBrackets b w) (_hs : 2 ≤ s)
    (U : LieSubalgebra ℚ L) (V K : Submodule ℚ L)
    (_hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (_hU : BasisGradedSubmodule b w U.toSubmodule) (_hV : BasisGradedSubmodule b w V)
    (η : L →ₗ[ℚ] ℚ) (_hη : ∀ x ∈ V, basisGradeProjection b w s x = x → η x = 0)
    (eK : Basis κ ℚ K) (f : Basis ι ℚ (L ⧸ V))
    (fU : Basis υ ℚ (L ⧸ U.toSubmodule)) (fK : Basis χ ℚ (L ⧸ K))
    (_hK : ∀ x ∈ K.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w 1 x = x)
    {H : ℕ} (_hH : 1 ≤ H)
    (_hKernelBasis : ∀ i z, RationalHeightLE (b.repr (eK z : L) i) H)
    (_hQuotient : ∀ i z, RationalHeightLE (f.repr (V.mkQ (b z)) i) H)
    (_hQuotientU : ∀ i z, RationalHeightLE (fU.repr (U.toSubmodule.mkQ (b z)) i) H)
    (_hQuotientK : ∀ i z, RationalHeightLE (fK.repr (K.mkQ (b z)) i) H)
    (_hStructure : ∀ i z r, RationalHeightLE (b.repr ⁅b i, b z⁆ r) H)
    {p : ℝ} (_hp : 0 ≤ p)
    (_hμ : (Fintype.card μ : ℝ) ≤ p) (_hυ : (Fintype.card υ : ℝ) ≤ p)
    (_hχ : (Fintype.card χ : ℝ) ≤ p) (_hι : (Fintype.card ι : ℝ) ≤ p)
    (_hκ : (Fintype.card κ : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hsp : (s : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (X : F.FormalInductionState b w (realificationLieSubalgebra U) V K eK T 2 p),
    ∃ Z : LieSubalgebra ℚ L, BasisGradedSubmodule b w Z.toSubmodule ∧
      (∀ x ∈ Z, η (basisGradeProjection b w s x) = 0) ∧
      ∃ e : Basis (Fin (Module.finrank ℚ Z)) ℚ Z,
        (∀ i j, ((b.repr (e i : L) j).num.natAbs : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ((b.repr (e i : L) j).den : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
        ∃ A P B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot,
          A * P * B = X.P ∧
          F.FormalCorrectionProperty b w (realificationLieSubalgebra U) A ∧
          F.FormalCorrectionProperty b w (realificationLieSubalgebra U) B ∧
          coefficients P.coord 0 = 0 ∧
          P.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) ∧
          (∀ α, coefficients P.coord α ∈ realificationLieSubalgebra Z) ∧
          CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + C) ^ C)) A.coord ∧
          ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
            CoefficientGrid (b.baseChange ℝ) m B.coord := by
  classical
  obtain ⟨E, _, hfinal⟩ := exists_formal_stepDrop_subalgebra_factorization s
  obtain ⟨D, hD, hgeometryBudget⟩ := exists_formal_geometry_uniform_budget
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((Polynomial.X + Polynomial.C D) ^ D + Polynomial.C E) ^ E)
  refine ⟨C, hC, ?_⟩
  intro L μ υ χ ι κ σ _ _ _ _ _ _ _ _ F b w hF hgraded hs U V K hUV hU hV η hη eK f
    fU fK hK H hH hKernelBasis hQuotient hQuotientU hQuotientK hStructure
    p hp hμ hυ hχ hι hκ hσ hsp hHp T hT X
  let u := (p + D) ^ D
  let r := 2 * Fintype.card υ + Fintype.card χ + Fintype.card ι + Fintype.card μ
  let J := formalGeometryHeight (Fintype.card μ) r H
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hpu : p ≤ u := by
    calc
      p ≤ p + D := le_add_of_nonneg_right (Nat.cast_nonneg D)
      _ ≤ (p + D) ^ D := by
        have hDr : (2 : ℝ) ≤ D := Nat.cast_le.mpr hD
        simpa only [pow_one] using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + D)
          (show 1 ≤ D by omega)
  have hr : (r : ℝ) ≤ 5 * p := by
    dsimp [r]
    push_cast
    linarith
  have hHJ : H ≤ J := formalGeometryHeight_ge_input _ _ _
  have hJ : 1 ≤ J := hH.trans hHJ
  have hJu : (J : ℝ) ≤ Real.exp u := hgeometryBudget _ _ _ p hp hμ hr hHp
  have hcap : (u + E) ^ E ≤ (p + C) ^ C := by
    simpa [u, Polynomial.eval₂_pow] using hbudget p hp
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hgeometry (j : ℕ) (hj : 2 ≤ j) :
      ∃ G : FormalStageGeometry b w (realificationLieSubalgebra U) V K eK f j J,
        G.bracketRank ≤ Fintype.card μ ∧ G.currentRank ≤ Fintype.card μ := by
    apply exists_rational_formal_stage_geometry b w U V K hU fU fK f eK hH
    · dsimp [r]; omega
    · dsimp [r]; omega
    · dsimp [r]; omega
    · exact hQuotientU
    · exact hQuotientK
    · exact hQuotient
    · exact hKernelBasis
    · exact hStructure
    · exact hj
  choose G hG using hgeometry
  obtain ⟨Z, hZ, hZη, e, he, A, P, B, hfactor, hA, hB, hzero, hdegree, hcoeff,
    hbound, m, hm, hmbound, hgrid⟩ :=
    hfinal F b w hF hgraded hs U V K hUV hU hV η hη eK f fU fK hK hJ
      (fun j hj _ => G j hj)
      (fun i z => (hKernelBasis i z).mono hHJ)
      (fun i z => (hQuotient i z).mono hHJ)
      (fun i z => (hQuotientU i z).mono hHJ)
      (fun i z => (hQuotientK i z).mono hHJ)
      (fun i z k => (hStructure i z k).mono hHJ)
      hu (hμ.trans hpu) (hυ.trans hpu) (hχ.trans hpu) (hι.trans hpu) (hκ.trans hpu) (hσ.trans hpu)
      (fun j hj _ => ⟨(Nat.cast_le.mpr (hG j hj).1).trans (hμ.trans hpu),
        (Nat.cast_le.mpr (hG j hj).2).trans (hμ.trans hpu)⟩)
      (hsp.trans hpu) hJu T (fun i => (Real.exp_le_exp.mpr hcap).trans (hT i))
      (X.enlarge hpu hTpos)
  refine ⟨Z, hZ, hZη, e, ?_, A, P, B, hfactor, hA, hB, hzero, hdegree, hcoeff,
    hbound.mono _ T hTpos (Real.exp_le_exp.mpr hcap), m, hm,
    hmbound.trans (Real.exp_le_exp.mpr hcap), hgrid⟩
  intro i j
  exact ⟨(he i j).1.trans (Real.exp_le_exp.mpr hcap), (he i j).2.trans (Real.exp_le_exp.mpr hcap)⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

universe uσ uι uτ uL

variable {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
  [Fintype σ] [Fintype ι] [Fintype τ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "bG" => F.associatedGradedBasis e ω hF
local notation "FG" => F.associatedGradedFiltration
local notation "U" => F.fullFastGradedDiagonal W
local notation "V" => F.fullFastGradedRelative e ω hF W
local notation "PG" => PolynomialGroup σ F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot

def FastTerminalFactorization (η : F.AssociatedGraded →ₗ[ℚ] ℚ)
    (T : σ → ℝ) (original : PG) (p : ℝ) : Prop :=
  ∃ Z : LieSubalgebra ℚ F.AssociatedGraded, BasisGradedSubmodule bG ω Z.toSubmodule ∧
    (∀ x ∈ Z, η (basisGradeProjection bG ω (s + 1) x) = 0) ∧
    ∃ bZ : Basis (Fin (Module.finrank ℚ Z)) ℚ Z,
      (∀ i j, (((bG).repr (bZ i : F.AssociatedGraded) j).num.natAbs : ℝ) ≤ Real.exp p ∧
        (((bG).repr (bZ i : F.AssociatedGraded) j).den : ℝ) ≤ Real.exp p) ∧
      ∃ A P B : PG, A * P * B = original ∧
        (FG).FormalCorrectionProperty bG ω (realificationLieSubalgebra U) A ∧
        (FG).FormalCorrectionProperty bG ω (realificationLieSubalgebra U) B ∧
        coefficients P.coord 0 = 0 ∧
        P.coord ∈ gradedPolynomialSubmodule ((bG).baseChange ℝ) ω (fun _ : σ => 1) ∧
        (∀ α, coefficients P.coord α ∈ realificationLieSubalgebra Z) ∧
        CoefficientBound ((bG).baseChange ℝ) T (Real.exp p) A.coord ∧
        ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp p ∧ CoefficientGrid ((bG).baseChange ℝ) m B.coord

omit [Fintype σ] [Fintype ι] in
theorem FastTerminalFactorization.mono
    {η : F.AssociatedGraded →ₗ[ℚ] ℚ} {T : σ → ℝ} {original : PG} {p q : ℝ}
    (h : F.FastTerminalFactorization e ω hF W η T original p)
    (hpq : p ≤ q) (hT : ∀ i, 0 < T i) :
    F.FastTerminalFactorization e ω hF W η T original q := by
  obtain ⟨Z, hZ, hη, bZ, hbZ, A, P, B, hfactor, hA, hB, hzero, hdegree, hcoeff,
    hbound, m, hm, hmp, hgrid⟩ := h
  have hepq := Real.exp_le_exp.mpr hpq
  exact ⟨Z, hZ, hη, bZ, fun i j => ⟨(hbZ i j).1.trans hepq, (hbZ i j).2.trans hepq⟩,
    A, P, B, hfactor, hA, hB, hzero, hdegree, hcoeff, hbound.mono _ T hT hepq,
    m, hm, hmp.trans hepq, hgrid⟩

def FastTerminalStateSpec (C : ℕ) : Prop :=
  ∀ (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p) (_hs : 1 ≤ s)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hτ : (Fintype.card τ : ℝ) ≤ p) (_hsp : (s + 1 : ℕ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hstructure : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (_hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (v : τ → F.squareFiltration.quotientTop.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hheight : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H)
    (k : ℕ) (_hk : (k : ℝ) ≤ p) (K : Submodule ℚ (L ⧸ F.layer 2)) (bK : Basis (Fin k) ℚ K)
    (_hKb : ∀ i j, RationalHeightLE ((F.layerOneBasis e ω hF).repr (bK j).val i) H)
    (η : F.AssociatedGraded →ₗ[ℚ] ℚ)
    (_hη : ∀ x ∈ V, basisGradeProjection bG ω (s + 1) x = x → η x = 0)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (X : (FG).FormalInductionState bG ω (realificationLieSubalgebra U) V
      (F.gradedHorizontalKernel e ω hF K) (F.gradedHorizontalKernelBasis e ω hF K bK) T 2 p),
    F.FastTerminalFactorization e ω hF W η T X.P ((p + C) ^ C)

theorem exists_fast_terminalState_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
        [Fintype σ] [Fintype ι] [Fintype τ] [LieRing L] [LieAlgebra ℚ L]
        (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
        (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
        (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded),
        F.FastTerminalStateSpec (σ := σ) (τ := τ) e ω hF W C := by
  have h := exists_stepDrop_from_formal_state.{uL, uι, 0, 0, 0, 0, uσ} (s + 1)
  obtain ⟨c, _, hformal⟩ := h
  obtain ⟨C, hC, hbudget⟩ := exists_fastTerminalParameter_budget c
  refine ⟨C, hC, ?_⟩
  intro σ ι τ L _ _ _ _ _ F e ω hF W H p hH hp hs hι hσ hτ hsp hHp hstructure
    hW v hv hheight k hk K bK hKb η hη T hT X
  have hTpos (i : σ) : 0 < T i := (Real.exp_pos _).trans_le (hT i)
  have hthree : 0 ≤ 3 * p := by positivity
  have hp3 : p ≤ 3 * p := by linarith
  have hsize : 2 * (Fintype.card ι : ℝ) + (Fintype.card τ : ℝ) ≤ 3 * p := by linarith
  have hUV := F.exists_full_fast_quotient_bases e ω hF W v hv hH hheight hthree hsize
    (hHp.trans (Real.exp_le_exp.mpr hp3))
  obtain ⟨Huv, hHHuv, hHuv, hHuvp, dU, hdU, fU, dV, hdV, fV, hfU, hfV⟩ := hUV
  have hkcard : (Fintype.card (Fin k) : ℝ) ≤ p := by simpa only [Fintype.card_fin] using hk
  have hK := F.exists_gradedHorizontalKernel_quotient_basis e ω hF K bK hH
    (fun j i => hKb i j) hp hkcard hHp
  obtain ⟨Hk, _, hHkp, dK, hdK, fK, hfK⟩ := hK
  let q := fastTerminalParameter p
  have hcontrol := fastTerminalParameter_controls hp
  have hpq : p ≤ q := hcontrol.1
  have hq : 0 ≤ q := hp.trans hpq
  have hHH : H ≤ max Huv Hk := hHHuv.trans (le_max_left _ _)
  have hcommon : ((max Huv Hk : ℕ) : ℝ) ≤ Real.exp q := by
    rw [Nat.cast_max]
    exact max_le (hHuvp.trans (Real.exp_le_exp.mpr hcontrol.2.1))
      (hHkp.trans (Real.exp_le_exp.mpr hcontrol.2.2))
  have hdim (d : ℕ) (hd : d ≤ Fintype.card ι) : (Fintype.card (Fin d) : ℝ) ≤ q := by
    rw [Fintype.card_fin]
    exact (Nat.cast_le.mpr hd).trans (hι.trans hpq)
  have hstructureG (i j r : ι) :
      RationalHeightLE ((F.associatedGradedBasis e ω hF).repr
        ⁅F.associatedGradedBasis e ω hF i, F.associatedGradedBasis e ω hF j⁆ r) (max Huv Hk) := by
    rw [F.associatedGradedBasis_bracket e ω hF]
    split_ifs
    · exact (hstructure i j r).mono hHH
    · exact rationalHeightLE_zero (hH.trans hHH)
  have hout : F.FastTerminalFactorization e ω hF W η T X.P ((q + c) ^ c) :=
    hformal F.associatedGradedFiltration (F.associatedGradedBasis e ω hF) ω
      (F.associatedGradedFiltration_layer e ω hF) (F.associatedGradedBasis_homogeneous_brackets e ω hF)
      (by omega) (F.fullFastGradedDiagonal W) (F.fullFastGradedRelative e ω hF W)
      (F.gradedHorizontalKernel e ω hF K)
      (fun _ hu _ hv => F.fullFastGradedRelative_lie_mem e ω hF W hu hv)
      (F.fullFastGradedDiagonal_graded e ω hF W hW) (F.fullFastGradedRelative_graded e ω hF W hW)
      η hη (F.gradedHorizontalKernelBasis e ω hF K bK) fV fU fK
      (F.gradedHorizontalKernel_real_pure e ω hF K) (hHuv.trans (le_max_left _ _))
      (fun i j => (F.gradedHorizontalKernelBasis_height e ω hF K bK hH (fun z r => hKb r z) j i).mono hHH)
      (fun i j => (hfV i j).mono (le_max_left _ _))
      (fun i j => (hfU i j).mono (le_max_left _ _))
      (fun i j => (hfK i j).mono (le_max_right _ _)) hstructureG hq
      (hι.trans hpq) (hdim dU hdU) (hdim dK hdK) (hdim dV hdV) (hkcard.trans hpq)
      (hσ.trans hpq) (hsp.trans hpq) hcommon T
      (fun i => (Real.exp_le_exp.mpr (hbudget p hp)).trans (hT i)) (X.enlarge hpq hTpos)
  exact hout.mono F e ω hF W (hbudget p hp) hTpos

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "bG" => F.associatedGradedBasis e ω hF
local notation "SG" => F.RealPolynomialSymbolGroup (fun _ : σ => 1)
local notation "φ" => F.realGradedSymbolPolynomialHom e ω hF (fun _ : σ => 1)

def SymbolTerminalFactorization (η : F.AssociatedGraded →ₗ[ℚ] ℚ)
    (T : σ → ℝ) (original : SG) (p : ℝ) : Prop :=
  ∃ Z : LieSubalgebra ℚ F.AssociatedGraded, BasisGradedSubmodule bG ω Z.toSubmodule ∧
    (∀ x ∈ Z, η (basisGradeProjection bG ω (s + 1) x) = 0) ∧
    ∃ bZ : Basis (Fin (Module.finrank ℚ Z)) ℚ Z,
      (∀ i j, (((bG).repr (bZ i : F.AssociatedGraded) j).num.natAbs : ℝ) ≤ Real.exp p ∧
        (((bG).repr (bZ i : F.AssociatedGraded) j).den : ℝ) ≤ Real.exp p) ∧
      ∃ A P B : SG, A * P * B = original ∧
        A.coord ∈ realificationLieSubalgebra
          (F.symbolPointwiseSubalgebra e ω hF (fun _ : σ => 1) (F.fullFastGradedDiagonal W)) ∧
        B.coord ∈ realificationLieSubalgebra
          (F.symbolPointwiseSubalgebra e ω hF (fun _ : σ => 1) (F.fullFastGradedDiagonal W)) ∧
        P.coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra e ω hF (fun _ : σ => 1) Z) ∧
        F.SymbolSlowBound e ω hF (fun _ : σ => 1) T (Real.exp p) A ∧
        ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp p ∧ F.SymbolRationalGrid e ω hF (fun _ : σ => 1) m B

theorem symbolTerminalFactorization_of_graded
    (η : F.AssociatedGraded →ₗ[ℚ] ℚ) (T : σ → ℝ) (original : SG) (p : ℝ)
    (h : F.FastTerminalFactorization e ω hF W η T (φ original) p) :
    F.SymbolTerminalFactorization e ω hF W η T original p := by
  obtain ⟨Z, hZ, hZη, bZ, hbZ, A, P, B, hfactor, hA, hB, _, hdegree, hcoeff,
    hbound, m, hm, hmp, hgrid⟩ := h
  obtain ⟨a, ha⟩ := F.exists_symbol_of_gradedPolynomial e ω hF (fun _ : σ => 1) A hA.2.1
  obtain ⟨c, hc⟩ := F.exists_symbol_of_gradedPolynomial e ω hF (fun _ : σ => 1) P hdegree
  obtain ⟨b, hb⟩ := F.exists_symbol_of_gradedPolynomial e ω hF (fun _ : σ => 1) B hB.2.1
  refine ⟨Z, hZ, hZη, bZ, hbZ, a, c, b, ?_, ?_, ?_, ?_, ?_, m, hm, hmp, ?_⟩
  · apply F.realGradedSymbolPolynomialHom_injective e ω hF (fun _ : σ => 1)
    rw [map_mul, map_mul, ha, hc, hb]
    exact hfactor
  · apply (F.mem_real_symbolPointwiseSubalgebra_iff_coefficients e ω hF (fun _ : σ => 1)
      (F.fullFastGradedDiagonal W) a.coord).mpr
    intro α
    change coefficients (φ a).coord α ∈ _
    rw [ha]
    exact hA.1 α
  · apply (F.mem_real_symbolPointwiseSubalgebra_iff_coefficients e ω hF (fun _ : σ => 1)
      (F.fullFastGradedDiagonal W) b.coord).mpr
    intro α
    change coefficients (φ b).coord α ∈ _
    rw [hb]
    exact hB.1 α
  · apply (F.mem_real_symbolPointwiseSubalgebra_iff_coefficients e ω hF (fun _ : σ => 1) Z c.coord).mpr
    intro α
    change coefficients (φ c).coord α ∈ _
    rw [hc]
    exact hcoeff α
  · apply F.symbolSlowBound_of_gradedPolynomial e ω hF (fun _ : σ => 1) T (Real.exp p) a
    rw [ha]
    exact hbound
  · apply F.symbolRationalGrid_of_gradedPolynomial e ω hF (fun _ : σ => 1) m b
    rw [hb]
    exact hgrid

theorem symbolTerminalFactorization_of_native
    (η : F.AssociatedGraded →ₗ[ℚ] ℚ) (T : σ → ℝ)
    (g : F.RealAdaptedPolynomialGroup (fun _ : σ => 1)) (p : ℝ)
    (h : F.FastTerminalFactorization e ω hF W η T
      (F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1) g) p) :
    F.SymbolTerminalFactorization e ω hF W η T
      (F.realPolynomialSymbolHom e ω hF (fun _ : σ => 1) (F.realAdaptedPolynomialGroupHom (fun _ => 1) g)) p := by
  apply F.symbolTerminalFactorization_of_graded e ω hF W η T _ p
  rw [F.realGradedSymbolPolynomialHom_native]
  exact h

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem SymbolTerminalFactorization.mono
    {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    {η : F.AssociatedGraded →ₗ[ℚ] ℚ} {T : σ → ℝ}
    {X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)} {p q : ℝ}
    (h : F.SymbolTerminalFactorization b ω hF W η T X p) (hpq : p ≤ q)
    (hT : ∀ i, 0 < T i) : F.SymbolTerminalFactorization b ω hF W η T X q := by
  obtain ⟨Z, hZ, hη, bZ, hbZ, A, P, B, hprod, hA, hB, hP, hslow, m, hm, hmp, hgrid⟩ := h
  have he := Real.exp_le_exp.mpr hpq
  exact ⟨Z, hZ, hη, bZ, (fun i j => ⟨(hbZ i j).1.trans he, (hbZ i j).2.trans he⟩),
    A, P, B, hprod, hA, hB, hP,
    F.symbolSlowBound_mono b ω hF (fun _ => 1) T hT he A hslow, m, hm, hmp.trans he, hgrid⟩

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem native_symbol_slow (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (g : F.RealAdaptedPolynomialGroup w) (hg : F.RealAdaptedCoefficientBound b ω hF w T M g.coord) :
    F.SymbolSlowBound b ω hF w T M
      (F.realPolynomialSymbolHom b ω hF w (F.realAdaptedPolynomialGroupHom w g)) :=
  F.polynomialSlowBound_symbol b ω hF w T M (F.realAdaptedPolynomialGroupHom w g)
    ((F.realAdaptedCoefficientBound_polynomial_iff b ω hF w T hT hM g).mp hg)

theorem native_symbol_grid (l : ℕ) (g : F.RealAdaptedPolynomialGroup w)
    (hg : F.RealAdaptedCoefficientGrid b ω hF w l g.coord) :
    F.SymbolRationalGrid b ω hF w l
      (F.realPolynomialSymbolHom b ω hF w (F.realAdaptedPolynomialGroupHom w g)) :=
  F.polynomialRationalGrid_symbol b ω hF w l (F.realAdaptedPolynomialGroupHom w g)
    ((F.realAdaptedCoefficientGrid_polynomial_iff b ω hF w l g).mp hg)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem SymbolTerminalFactorization.controlled
    {σ ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    {η : L →ₗ[ℚ] ℚ} {T : σ → ℝ} {X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)} {p : ℝ}
    (hp : 0 ≤ p) (hT : ∀ i, 0 < T i)
    (h : F.SymbolTerminalFactorization b ω hF W (F.gradedFrequency b ω hF η) T X p) :
    F.ControlledSymbolFactorization b ω hF η T X (p + 1) := by
  classical
  obtain ⟨Z, hZ, hη, bZ, hbZ, A, P, B, hprod, _, _, hP, hslow, m, hm, hmp, hgrid⟩ := h
  let H := ⌈Real.exp p⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp p
  have hb : ∀ i j, RationalHeightLE
      ((F.associatedGradedBasis b ω hF).repr (bZ i : F.AssociatedGraded) j) H := by
    intro i j
    exact rationalHeightLE_ceil_exp ((rationalLogHeight_le_iff _ p).mpr (hbZ i j))
  obtain ⟨w, hw, hheight⟩ := exists_bounded_ambient_spanning
    (F.associatedGradedBasis b ω hF) Z bZ bZ.span_eq hH hb
  let v : ι → F.AssociatedGraded := fun i => w (Fintype.equivFin ι i)
  have hrange : Set.range v = Set.range w := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨Fintype.equivFin ι i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨(Fintype.equivFin ι).symm i, congrArg w ((Fintype.equivFin ι).apply_symm_apply i)⟩
  have he : Real.exp p ≤ Real.exp (p + 1) := Real.exp_le_exp.mpr (by linarith)
  refine ⟨m, A, P, B, Z, v, hm, hmp.trans he, hprod,
    F.symbolSlowBound_mono b ω hF (fun _ => 1) T hT he A hslow, hgrid, ?_, hZ, ?_, ?_, hP⟩
  · rw [hrange]
    exact hw
  · intro i j
    exact rationalLogHeight_le_of_height (hheight (Fintype.equivFin ι i) j) (ceil_exp_le_exp_add_one hp)
  · intro x hx hproj
    have hz := hη x hx
    rw [hproj] at hz
    exact hz

end Erdos3.NilpotentLieFiltration

end

end OAI
