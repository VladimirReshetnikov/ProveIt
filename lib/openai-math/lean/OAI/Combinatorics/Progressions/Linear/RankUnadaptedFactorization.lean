import OAI.Combinatorics.Progressions.Estimates.UnconditionalStepDrop
import OAI.Combinatorics.Progressions.Nilpotent.RankBracketFactorizationMonotone

namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

def rankVerticalSelectionBudget (p : ℝ) : ℝ := p + verticalDecompositionBudget (p + 1) + 1

theorem rankVerticalSelectionBudget_bounds {p : ℝ} (hp : 0 ≤ p) :
    p + 1 ≤ rankVerticalSelectionBudget p ∧
      verticalDecompositionBudget (p + 1) ≤ rankVerticalSelectionBudget p := by
  have h := verticalDecompositionBudget_nonneg (show 0 ≤ p + 1 by linarith)
  unfold rankVerticalSelectionBudget
  constructor <;> linarith

namespace RationalFilteredNilmanifold.Niltest

open CircleFourier

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  {D : RationalFilteredNilmanifold L s d}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem exists_biased_mode_restricting_frequency (T : D.Niltest (fun _ : σ => 1))
    {p : ℝ} (hp : 0 ≤ p) (hT : T.ComplexityLE p)
    (S : Submodule ℚ L) (hS : S ≤ D.filtration.layer s) (η : L →ₗ[ℚ] ℚ)
    (hchar : ∀ y ∈ S, ∀ t : ℝ, ∀ x,
      T.observable ((⟨t ⊗ₜ[ℚ] y⟩ : D.RealGroup) • x) =
        character ((t * (η y : ℝ) : ℝ) : CircleFourier.Circle) * T.observable x)
    (Q : Finset (σ → ℤ)) (hQ : Q.Nonempty)
    (hbias : Real.exp (-p) ≤ ‖𝔼 x ∈ Q, T.eval x‖) :
    ∃ (ξ : L →ₗ[ℚ] ℚ) (U : D.Niltest (fun _ : σ => 1)),
      U.ComplexityLE (rankVerticalSelectionBudget p) ∧ U.orbit = T.orbit ∧
      (∀ i, rationalLogHeight (ξ (D.basis i)) ≤ rankVerticalSelectionBudget p) ∧
      (∀ z ∈ D.filtration.realification.subgroup s, ∀ x,
        U.observable (z • x) = character ((realifyFunctional ξ z.coord : ℝ) : CircleFourier.Circle) *
          U.observable x) ∧
      (∀ y ∈ S, ξ y = η y) ∧
      Real.exp (-rankVerticalSelectionBudget p) ≤ ‖𝔼 x ∈ Q, U.eval x‖ := by
  have hp1 : 0 ≤ p + 1 := by linarith
  have hρp : (Real.exp (-p) / 2)⁻¹ ≤ Real.exp (p + 1) := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ = 2 * Real.exp p := by rw [inv_div, Real.exp_neg]; field_simp
      _ ≤ Real.exp 1 * Real.exp p := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, add_comm]
  obtain ⟨ξ, U, hU, hOrbit, hheight, hvert, _, hpres, hc⟩ :=
    T.exists_correlating_vertical_mode_preserving_characters hp1
      (hT.mono (by linarith)) (Real.exp_pos (-p)) hρp hQ (fun _ => 1)
      (fun _ _ => by simp) (by rwa [norm_finiteCorrelation_one])
  rw [norm_finiteCorrelation_one] at hc
  have hthreshold : Real.exp (-rankVerticalSelectionBudget p) ≤
      Real.exp (-p) / (2 * Real.exp (verticalDecompositionBudget (p + 1))) := by
    calc
      _ = Real.exp (-p - 1) / Real.exp (verticalDecompositionBudget (p + 1)) := by
        rw [← Real.exp_sub]
        congr 1
        unfold rankVerticalSelectionBudget
        ring
      _ ≤ (Real.exp (-p) / 2) / Real.exp (verticalDecompositionBudget (p + 1)) :=
        div_le_div_of_nonneg_right (exp_sub_one_le_half_exp (-p)) (Real.exp_nonneg _)
      _ = _ := by ring
  have hfinal := hthreshold.trans hc
  have hne : ∃ x, U.observable x ≠ 0 := by
    by_contra! hzero
    have heval : ∀ x, U.eval x = 0 := fun x => hzero _
    simp only [heval, Finset.expect_const_zero, norm_zero] at hfinal
    exact (not_le_of_gt (Real.exp_pos _)) hfinal
  refine ⟨ξ, U, hU.mono (rankVerticalSelectionBudget_bounds hp).1, hOrbit,
    fun i => (hheight i).trans (rankVerticalSelectionBudget_bounds hp).2, hvert, ?_, hfinal⟩
  intro y hy
  have heq := vertical_frequency_on_real_direction D.filtration D.realLattice ξ U.observable
    hvert hne y (hS hy) (η y : ℝ) (fun t x => hpres _ _ (hchar y hy t) x)
  exact_mod_cast heq

end RationalFilteredNilmanifold.Niltest

end Erdos3

end

section

namespace Erdos3

theorem exists_rank_biased_factorization_budget (c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      rankVerticalSelectionBudget p ≤ (p + C) ^ C ∧
      (rankVerticalSelectionBudget p + c) ^ c ≤ (p + C) ^ C := by
  obtain ⟨a, _, hvertical⟩ := exists_verticalDecompositionBudget_bound
  let X : Polynomial ℕ := Polynomial.X
  let Y := X + (X + 1 + Polynomial.C a) ^ a + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Y + (Y + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro p hp
  have hq : rankVerticalSelectionBudget p ≤ p + (p + 1 + a) ^ a + 1 := by
    have h := hvertical (p + 1) (by linarith)
    unfold rankVerticalSelectionBudget
    linarith only [h]
  have hq0 : 0 ≤ rankVerticalSelectionBudget p :=
    (show 0 ≤ p + 1 by linarith).trans (rankVerticalSelectionBudget_bounds hp).1
  have hY : 0 ≤ p + (p + 1 + a) ^ a + 1 := by positivity
  have hZ : 0 ≤ (p + (p + 1 + a) ^ a + 1 + c) ^ c := by positivity
  have hpow : (rankVerticalSelectionBudget p + c) ^ c ≤
      (p + (p + 1 + a) ^ a + 1 + c) ^ c := by gcongr
  have hbound : p + (p + 1 + a) ^ a + 1 +
      (p + (p + 1 + a) ^ a + 1 + c) ^ c ≤ (p + C) ^ C := by
    simpa [X, Y, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨by linarith only [hq, hZ, hbound], by linarith only [hpow, hY, hbound]⟩

end Erdos3

end

section

namespace Erdos3

theorem exists_rank_adapted_factorization_budget (c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      rankAdaptedNiltestBudget p ≤ (p + C) ^ C ∧
      (rankAdaptedNiltestBudget p + c) ^ c ≤ (p + C) ^ C ∧
      p + 1 ≤ (p + C) ^ C ∧ (p + 3) ^ 5 ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let A := (X + 3) ^ 11 + X + 2
  let B := A + (A + 2) ^ 2
  let P := B + (B + Polynomial.C c) ^ c + (X + 3) ^ 5 + X + 1
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro p hp
  have hB : 0 ≤ rankAdaptedNiltestBudget p := hp.trans (le_rankAdaptedNiltestBudget hp)
  have hpow : 0 ≤ (rankAdaptedNiltestBudget p + c) ^ c := by positivity
  have hinv : 0 ≤ (p + 3) ^ 5 := by positivity
  have htotal : rankAdaptedNiltestBudget p + (rankAdaptedNiltestBudget p + c) ^ c +
      (p + 3) ^ 5 + p + 1 ≤ (p + C) ^ C := by
    simpa [P, B, A, X, Polynomial.eval₂_pow, rankAdaptedNiltestBudget,
      rankAdaptedNiltestBase] using hbound p hp
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end Erdos3

end

section

namespace Erdos3

open Module CircleFourier
open scoped TensorProduct BigOperators

theorem exists_rank_biased_symbol_factorization (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] {d r : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (R : D.DegreeRankStructure r)
      (ω : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (p : ℝ), 0 ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (T : D.Niltest (fun _ : σ => 1)) → T.ComplexityLE p →
      (η : L →ₗ[ℚ] ℚ) →
      (∀ z ∈ R.realSubgroup s r, ∀ x, T.observable (z • x) =
        character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * T.observable x) →
      ∀ (origin : σ → ℤ) (lengths : σ → ℕ), (∀ i, 0 < lengths i) →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths, T.eval x‖ →
      ∃ ξ : L →ₗ[ℚ] ℚ,
        (∀ x ∈ R.filtration.layer s r, ξ x = η x) ∧
        D.filtration.ControlledSymbolFactorization D.basis ω hF ξ (fun i => (lengths i : ℝ))
          (T.symbol D.basis ω hF) ((p + C) ^ C) := by
  obtain ⟨c, _, hstep⟩ := exists_translated_step_drop s hs
  obtain ⟨C, hC, hbudget⟩ := exists_rank_biased_factorization_budget c
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ d r _ _ _ _ D R ω hF p hp hσ T hT η hvert origin lengths hlengths hlarge hbias
  have hS : R.filtration.layer s r ≤ D.filtration.layer s := by
    intro y hy
    have h := R.filtration.layer_le_associatedDegree s r hy
    rwa [R.associated] at h
  have hchar : ∀ y ∈ R.filtration.layer s r, ∀ t : ℝ, ∀ x,
      T.observable ((⟨t ⊗ₜ[ℚ] y⟩ : D.RealGroup) • x) =
        character ((t * (η y : ℝ) : ℝ) : CircleFourier.Circle) * T.observable x := by
    intro y hy t x
    have hz : (⟨t ⊗ₜ[ℚ] y⟩ : D.RealGroup) ∈ R.realSubgroup s r :=
      Submodule.tmul_mem_baseChange_of_mem t hy
    simpa only [realifyFunctional_tmul] using hvert _ hz x
  have hQ : (translatedIntegerBox origin lengths).Nonempty := by
    refine ⟨origin, (mem_translatedIntegerBox origin lengths origin).mpr ?_⟩
    intro i
    have hi := hlengths i
    exact ⟨le_rfl, by omega⟩
  obtain ⟨ξ, U, hU, hOrbit, hheight, hUvert, hrestrict, hUbias⟩ :=
    T.exists_biased_mode_restricting_frequency hp hT _ hS η hchar _ hQ hbias
  let q := rankVerticalSelectionBudget p
  have hpq : p ≤ q := by
    have h := (rankVerticalSelectionBudget_bounds hp).1
    dsimp only [q]
    linarith
  have hq : 0 ≤ q := hp.trans hpq
  have hfact := hstep D ω hF q hq (hσ.trans hpq) U hU ξ hheight hUvert origin lengths hlengths
    (fun i => (Real.exp_le_exp.mpr (hbudget p hp).2).trans (hlarge i)) hUbias
  have hsymbol : U.symbol D.basis ω hF = T.symbol D.basis ω hF := by
    unfold RationalFilteredNilmanifold.Niltest.symbol
    apply congrArg (D.filtration.realPolynomialSymbolHom D.basis ω hF (fun _ => 1))
    apply NilpotentLieBCHGroup.ext
    apply Subtype.ext
    exact congrArg (fun o : D.filtration.realification.PolynomialOrbit (fun _ : σ => 1) => o.log) hOrbit
  rw [hsymbol] at hfact
  exact ⟨ξ, hrestrict, NilpotentLieFiltration.ControlledSymbolFactorization.mono
    D.filtration D.basis ω hF hfact (hbudget p hp).2 (fun i => by exact_mod_cast hlengths i)⟩

end Erdos3

end

section

namespace Erdos3

open Module CircleFourier
open scoped TensorProduct BigOperators

theorem exists_rank_biased_refiltration (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] {d r : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (R : D.DegreeRankStructure r)
      (ω : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (p : ℝ), 0 ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (T : D.Niltest (fun _ : σ => 1)) → T.ComplexityLE p →
      (η : L →ₗ[ℚ] ℚ) →
      (∀ z ∈ R.realSubgroup s r, ∀ x, T.observable (z • x) =
        character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * T.observable x) →
      ∀ (origin : σ → ℤ) (lengths : σ → ℕ), (∀ i, 0 < lengths i) →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths, T.eval x‖ →
      R.ControlledRankBracketFactorization ω hF η (fun i => (lengths i : ℝ))
        (T.symbol D.basis ω hF) ((p + C) ^ C) := by
  obtain ⟨C, hC, hfactor⟩ := exists_rank_biased_symbol_factorization s hs
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ d r _ _ _ _ D R ω hF p hp hσ T hT η hvert origin lengths hlengths hlarge hbias
  obtain ⟨ξ, hrestrict, h⟩ := hfactor D R ω hF p hp hσ T hT η hvert origin lengths hlengths hlarge hbias
  exact R.controlledRankBracketFactorization_of_frequency_restriction ω hF ξ η _ _ _ h hrestrict

end Erdos3

end

section

namespace Erdos3

open Module CircleFourier
open scoped TensorProduct BigOperators

theorem exists_rank_unadapted_factorization (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] {d r : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (R : D.DegreeRankStructure r)
      (p : ℝ), 0 ≤ p → (Fintype.card σ : ℝ) ≤ p → R.ComplexityLE p →
      (T : D.Niltest (fun _ : σ => 1)) → T.ComplexityLE p →
      (η : L →ₗ[ℚ] ℚ) →
      (∀ z ∈ R.realSubgroup s r, ∀ x, T.observable (z • x) =
        character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * T.observable x) →
      ∀ (origin : σ → ℤ) (lengths : σ → ℕ), (∀ i, 0 < lengths i) →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
      Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths, T.eval x‖ →
      ∃ F : R.AdaptedData,
        F.rank.ComplexityLE ((p + C) ^ C) ∧
        (∀ i j, rationalLogHeight (D.basis.repr (F.basis i) j) ≤ (p + C) ^ C) ∧
        (∀ j i, rationalLogHeight (F.basis.repr (D.basis j) i) ≤ (p + C) ^ C) ∧
        F.rank.ControlledRankBracketFactorization F.weight F.layers η (fun i => (lengths i : ℝ))
          (T.symbol F.basis F.weight F.layers) ((p + C) ^ C) := by
  obtain ⟨c, _, hfactor⟩ := exists_rank_biased_refiltration s hs
  obtain ⟨C, hC, hbudget⟩ := exists_rank_adapted_factorization_budget c
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ d r _ _ _ _ D R p hp hσ hR T hT η hvert origin lengths hlengths hlarge hbias
  obtain ⟨F, hFR, hforward, hback, S, horbit, hobs, hS⟩ := R.exists_adapted_niltest T hp hR hT
  let q := rankAdaptedNiltestBudget p
  have hpq : p ≤ q := le_rankAdaptedNiltestBudget hp
  have hq : 0 ≤ q := hp.trans hpq
  obtain ⟨hqC, hfactorC, hforwardC, hbackC⟩ := hbudget p hp
  have hvertS : ∀ z ∈ F.rank.realSubgroup s r, ∀ x, S.observable (z • x) =
      character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * S.observable x := by
    intro z hz x
    rw [hobs]
    exact hvert z hz x
  have heval (x : σ → ℤ) : S.eval x = T.eval x := by
    unfold RationalFilteredNilmanifold.Niltest.eval
    rw [hobs, horbit]
    rfl
  have hbiasS : Real.exp (-q) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths, S.eval x‖ := by
    simp only [heval]
    exact (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans hbias
  have hfact := hfactor F.model F.rank F.weight F.layers q hq (hσ.trans hpq)
    S hS η hvertS origin lengths hlengths
    (fun i => (Real.exp_le_exp.mpr hfactorC).trans (hlarge i)) hbiasS
  have hsymbol : S.symbol F.basis F.weight F.layers = T.symbol F.basis F.weight F.layers := by
    unfold RationalFilteredNilmanifold.Niltest.symbol
    apply congrArg (D.filtration.realPolynomialSymbolHom F.basis F.weight F.layers (fun _ => 1))
    apply NilpotentLieBCHGroup.ext
    apply Subtype.ext
    exact congrArg (fun o : D.filtration.realification.PolynomialOrbit (fun _ : σ => 1) => o.log) horbit
  change F.rank.ControlledRankBracketFactorization F.weight F.layers η (fun i => (lengths i : ℝ))
    (S.symbol F.basis F.weight F.layers) ((q + c) ^ c) at hfact
  rw [hsymbol] at hfact
  refine ⟨F, hFR.mono F.rank hqC,
    (fun i j => (hforward i j).trans hforwardC),
    (fun j i => (hback j i).trans hbackC), ?_⟩
  exact RationalFilteredNilmanifold.DegreeRankStructure.ControlledRankBracketFactorization.mono
    F.rank F.weight F.layers hfact hfactorC (fun i => by exact_mod_cast hlengths i)

end Erdos3

end

end OAI
