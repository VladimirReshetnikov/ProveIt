import OAI.Combinatorics.Progressions.Estimates.FormalInductionStage

namespace OAI

section

namespace Erdos3

noncomputable def formalIterationBudget (C : ℕ) (p : ℝ) : ℕ → ℝ
  | 0 => p
  | n + 1 => (formalIterationBudget C p n + C) ^ C

@[simp] theorem formalIterationBudget_zero (C : ℕ) (p : ℝ) : formalIterationBudget C p 0 = p := rfl

@[simp] theorem formalIterationBudget_succ (C : ℕ) (p : ℝ) (n : ℕ) :
    formalIterationBudget C p (n + 1) = (formalIterationBudget C p n + C) ^ C := rfl

theorem formalIterationBudget_nonneg (C : ℕ) {p : ℝ} (hp : 0 ≤ p) (n : ℕ) :
    0 ≤ formalIterationBudget C p n := by
  induction n with
  | zero => exact hp
  | succ n ih => exact pow_nonneg (add_nonneg ih (Nat.cast_nonneg C)) C

theorem formalIterationBudget_monotone {C : ℕ} (hC : 2 ≤ C) {p : ℝ} (hp : 0 ≤ p) :
    Monotone (formalIterationBudget C p) := by
  apply monotone_nat_of_le_succ
  intro n
  have hn := formalIterationBudget_nonneg C hp n
  have hCr : (2 : ℝ) ≤ C := Nat.cast_le.mpr hC
  calc
    formalIterationBudget C p n ≤ formalIterationBudget C p n + C := le_add_of_nonneg_right (Nat.cast_nonneg C)
    _ ≤ (formalIterationBudget C p n + C) ^ C := by
      simpa only [pow_one] using pow_le_pow_right₀
        (by linarith : (1 : ℝ) ≤ formalIterationBudget C p n + C) (show 1 ≤ C by omega)

theorem formalIterationBudget_ge {C : ℕ} (hC : 2 ≤ C) {p : ℝ} (hp : 0 ≤ p) (n : ℕ) :
    p ≤ formalIterationBudget C p n := formalIterationBudget_monotone hC hp (Nat.zero_le n)

noncomputable def formalIterationPolynomial (C : ℕ) : ℕ → Polynomial ℕ
  | 0 => Polynomial.X
  | n + 1 => (formalIterationPolynomial C n + Polynomial.C C) ^ C

theorem formalIterationPolynomial_eval (C n : ℕ) (p : ℝ) :
    (formalIterationPolynomial C n).eval₂ (Nat.castRingHom ℝ) p = formalIterationBudget C p n := by
  induction n with
  | zero => simp [formalIterationPolynomial]
  | succ n ih => simp [formalIterationPolynomial, Polynomial.eval₂_pow, ih]

theorem exists_formal_iteration_uniform_budget (C n : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧ ∀ p : ℝ, 0 ≤ p →
      (n + 1 : ℝ) * formalIterationBudget C p n ≤ (p + D) ^ D := by
  obtain ⟨D, hD, hbound⟩ := exists_natPolynomial_eval_budget
    (Polynomial.C (n + 1) * formalIterationPolynomial C n)
  refine ⟨D, hD, fun p hp => ?_⟩
  have h := hbound p hp
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, formalIterationPolynomial_eval] at h
  change ((n + 1 : ℕ) : ℝ) * formalIterationBudget C p n ≤ (p + D) ^ D at h
  simpa only [Nat.cast_add, Nat.cast_one] using h

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_formal_induction_iteration (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
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
    (T : σ → ℝ) (_hT : ∀ i, Real.exp (formalIterationBudget C p (s - 1)) ≤ T i)
    (X : F.FormalInductionState b w U V K eK T 2 p),
    Nonempty (F.FormalInductionRun b w U V K eK T X.P (s - 1)
      (formalIterationBudget C p (s - 1))) := by
  classical
  obtain ⟨C, hC, hstage⟩ := exists_formal_induction_stage s
  refine ⟨C, hC, ?_⟩
  intro L μ ι κ σ _ _ _ _ _ _ F b w hF hgraded hs U V K hUV hU hV eK f hK H hH G
    hKernelBasis hQuotient hStructure p hp hμ hι hκ hσ hRanks hsp hHp T hT X
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hrun : ∀ r, r ≤ s - 1 →
      Nonempty (F.FormalInductionRun b w U V K eK T X.P r (formalIterationBudget C p r)) := by
    intro r
    induction r with
    | zero =>
      intro _
      exact ⟨FormalInductionRun.start X⟩
    | succ r ih =>
      intro hr
      obtain ⟨W⟩ := ih (by omega)
      have hj : 2 ≤ 2 + r := by omega
      have hjs : 2 + r ≤ s := by omega
      let g := G (2 + r) hj hjs
      have hpq : p ≤ formalIterationBudget C p r := formalIterationBudget_ge hC hp r
      have hq : 0 ≤ formalIterationBudget C p r := formalIterationBudget_nonneg C hp r
      have hnext : formalIterationBudget C p r ≤ formalIterationBudget C p (r + 1) :=
        formalIterationBudget_monotone hC hp (Nat.le_succ r)
      have hcutoff : ∀ i, Real.exp ((formalIterationBudget C p r + C) ^ C) ≤ T i := by
        intro i
        exact (Real.exp_le_exp.mpr (formalIterationBudget_monotone hC hp hr)).trans (hT i)
      have hν : (Fintype.card (Fin g.bracketRank) : ℝ) ≤ formalIterationBudget C p r := by
        simpa only [Fintype.card_fin] using (hRanks (2 + r) hj hjs).1.trans hpq
      have hτ : (Fintype.card (Fin g.currentRank) : ℝ) ≤ formalIterationBudget C p r := by
        simpa only [Fintype.card_fin] using (hRanks (2 + r) hj hjs).2.trans hpq
      have hjp : ((2 + r : ℕ) : ℝ) ≤ formalIterationBudget C p r :=
        (Nat.cast_le.mpr hjs).trans (hsp.trans hpq)
      obtain ⟨Y, A₁, A₂, B₁, B₂, hfactor, hmem, hdeg, hzero,
        hA₁bound, hA₂bound, hB₁grid, hB₂grid⟩ :=
        hstage F b w hF hgraded hs U V K g.bracketSpace g.currentSpace hUV hV
          eK g.bracketBasis g.currentBasis f hK hj hH
          g.bracket_grade g.bracket_U g.bracket_K g.bracket_V
          g.current_grade g.current_U g.current_projection
          g.bracket_matrix_height g.current_matrix_height hKernelBasis
          g.bracket_basis_height g.current_basis_height hQuotient hStructure hq
          (hμ.trans hpq) (hι.trans hpq) (hκ.trans hpq) hν hτ (hσ.trans hpq) hjp
          (hHp.trans (Real.exp_le_exp.mpr hpq)) T hcutoff W.state
          (W.state.bracket_source g hU hj)
      exact ⟨W.extend hnext hTpos Y A₁ A₂ B₁ B₂ hfactor
        ⟨fun α => (hmem α).1, hdeg.1, hzero.1⟩
        ⟨fun α => (hmem α).2.1, hdeg.2.1, hzero.2.1⟩
        ⟨fun α => (hmem α).2.2.1, hdeg.2.2.1, hzero.2.2.1⟩
        ⟨fun α => (hmem α).2.2.2, hdeg.2.2.2, hzero.2.2.2⟩
        hA₁bound hA₂bound hB₁grid hB₂grid⟩
  exact hrun (s - 1) le_rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_uniform_formal_induction_iteration (s : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧
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
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + D) ^ D) ≤ T i)
    (X : F.FormalInductionState b w U V K eK T 2 p),
    ∃ q : ℝ, p ≤ q ∧ 0 ≤ q ∧ q ≤ (p + D) ^ D ∧
      ∃ W : F.FormalInductionRun b w U V K eK T X.P (s - 1) q,
        (W.denominator : ℝ) ≤ Real.exp ((p + D) ^ D) := by
  obtain ⟨C, hC, hiteration⟩ := exists_formal_induction_iteration s
  obtain ⟨D, hD, hbudget⟩ := exists_formal_iteration_uniform_budget C (s - 1)
  refine ⟨D, hD, ?_⟩
  intro L μ ι κ σ _ _ _ _ _ _ F b w hF hgraded hs U V K hUV hU hV eK f hK H hH G
    hKernelBasis hQuotient hStructure p hp hμ hι hκ hσ hRanks hsp hHp T hT X
  let q := formalIterationBudget C p (s - 1)
  have hpq : p ≤ q := formalIterationBudget_ge hC hp (s - 1)
  have hq : 0 ≤ q := formalIterationBudget_nonneg C hp (s - 1)
  have htotal : ((s - 1 : ℕ) + 1 : ℝ) * q ≤ (p + D) ^ D := hbudget p hp
  have hqcap : q ≤ (p + D) ^ D := by
    have hmul := mul_nonneg (Nat.cast_nonneg (s - 1) : (0 : ℝ) ≤ (s - 1 : ℕ)) hq
    nlinarith
  have hT' : ∀ i, Real.exp (formalIterationBudget C p (s - 1)) ≤ T i :=
    fun i => (Real.exp_le_exp.mpr hqcap).trans (hT i)
  obtain ⟨W⟩ := hiteration F b w hF hgraded hs U V K hUV hU hV eK f hK hH G
    hKernelBasis hQuotient hStructure hp hμ hι hκ hσ hRanks hsp hHp T hT' X
  exact ⟨q, hpq, hq, hqcap, W, W.denominator_bound.trans (Real.exp_le_exp.mpr htotal)⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
