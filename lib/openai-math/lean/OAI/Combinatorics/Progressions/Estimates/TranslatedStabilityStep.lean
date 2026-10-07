import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import OAI.Combinatorics.Progressions.Estimates.UnconditionalStepDrop

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem gradedFast_finrank_inf_lt (V U : LieSubalgebra ℚ F.AssociatedGraded)
    (eta : L →ₗ[ℚ] ℚ)
    (hU : ∀ x ∈ U, basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x →
      F.gradedFrequency b ω hF eta x = 0)
    (hV : ∃ x ∈ V, basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x ∧
      F.gradedFrequency b ω hF eta x ≠ 0) :
    finrank ℚ ↥(V ⊓ U) < finrank ℚ V := by
  let : FiniteDimensional ℚ F.AssociatedGraded :=
    (F.associatedGradedBasis b ω hF).finiteDimensional_of_finite
  change finrank ℚ ↥(V.toSubmodule ⊓ U.toSubmodule) < finrank ℚ V.toSubmodule
  apply Submodule.finrank_lt_finrank_of_lt
  refine lt_of_le_of_ne inf_le_left ?_
  intro heq
  obtain ⟨x, hx, hgrade, hnonzero⟩ := hV
  have hxinf : x ∈ V.toSubmodule ⊓ U.toSubmodule := heq.symm ▸ hx
  exact hnonzero (hU x hxinf.2 hgrade)

omit [Fintype ι] in
theorem exists_graded_top_frequency_ne_zero (V : LieSubalgebra ℚ F.AssociatedGraded)
    (eta : L →ₗ[ℚ] ℚ) (hV : ∃ x ∈ F.gradedRefiltrationLayer V s, eta x ≠ 0) :
    ∃ x ∈ V, basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x ∧
      F.gradedFrequency b ω hF eta x ≠ 0 := by
  obtain ⟨v, hv, hne⟩ := hV
  obtain ⟨hvs, hvV⟩ := (F.mem_gradedRefiltrationLayer V s v).mp hv
  refine ⟨F.associatedGradedPieceMap s ⟨v, hvs⟩, hvV,
    F.associatedGradedPieceMap_grade_fixed b ω hF s ⟨v, hvs⟩, ?_⟩
  simpa only [F.gradedFrequency_top_piece b ω hF eta] using hne

theorem ControlledSymbolFactorization.exists_dimension_drop
    {eta : L →ₗ[ℚ] ℚ} {T : σ → ℝ}
    {X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)} {p : ℝ}
    (h : F.ControlledSymbolFactorization b ω hF eta T X p)
    (V : LieSubalgebra ℚ F.AssociatedGraded)
    (hV : ∃ x ∈ F.gradedRefiltrationLayer V s, eta x ≠ 0) :
    ∃ (l : ℕ) (U : LieSubalgebra ℚ F.AssociatedGraded) (u : ι → F.AssociatedGraded),
      0 < l ∧ (l : ℝ) ≤ Real.exp p ∧ Submodule.span ℚ (Set.range u) = U.toSubmodule ∧
      BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω U.toSubmodule ∧
      (∀ i j, rationalLogHeight ((F.associatedGradedBasis b ω hF).repr (u i) j) ≤ p) ∧
      (∀ x ∈ U, basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x →
        F.gradedFrequency b ω hF eta x = 0) ∧
      finrank ℚ ↥(V ⊓ U) < finrank ℚ V ∧ F.SymbolFactorizationIn b ω hF T X p l U := by
  obtain ⟨l, U, u, hl, hlp, hspan, hgraded, hheight, hkill, hfactor⟩ :=
    ControlledSymbolFactorization.exists_in F b ω hF h
  exact ⟨l, U, u, hl, hlp, hspan, hgraded, hheight, hkill,
    F.gradedFast_finrank_inf_lt b ω hF V U eta hkill
      (F.exists_graded_top_frequency_ne_zero b ω hF V eta hV), hfactor⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module CircleFourier NilpotentLieFiltration
open scoped TensorProduct BigOperators

theorem exists_translated_stability_step (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (ω : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (p q rho : ℝ), 0 ≤ p → p ≤ q → (Fintype.card σ : ℝ) ≤ q →
      verticalDecompositionBudget p ≤ q → 0 < rho → rho⁻¹ ≤ Real.exp p →
      ∀ (T : D.Niltest (fun _ : σ => 1)), T.UnitIntervalValued → T.ComplexityLE p →
      ∀ (V : LieSubalgebra ℚ D.filtration.AssociatedGraded)
        {β : Type*} (origin : β → σ → ℤ) (lengths : β → σ → ℕ),
      (∀ a i, 0 < lengths a i) →
      (∀ a i, Real.exp ((q + C) ^ C) ≤ (lengths a i : ℝ)) →
      (∃ (a : β) (l : ℕ) (U : LieSubalgebra ℚ D.filtration.AssociatedGraded)
          (u : Fin d → D.filtration.AssociatedGraded),
        0 < l ∧ (l : ℝ) ≤ Real.exp ((q + C) ^ C) ∧
        Submodule.span ℚ (Set.range u) = U.toSubmodule ∧
        BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis ω hF) ω U.toSubmodule ∧
        (∀ i j, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis ω hF).repr (u i) j) ≤
          (q + C) ^ C) ∧
        finrank ℚ ↥(V ⊓ U) < finrank ℚ V ∧
        D.filtration.SymbolFactorizationIn D.basis ω hF (fun i => (lengths a i : ℝ))
          (T.symbol D.basis ω hF) ((q + C) ^ C) l U) ∨
      (∃ S : D.Niltest (fun _ : σ => 1),
        S.UnitIntervalValued ∧ S.ComplexityLE p ∧ S.orbit = T.orbit ∧
        (∀ z : D.RealGroup, z.coord ∈ (D.filtration.gradedRefiltrationLayer V s).baseChange ℝ →
          ∀ x, S.observable (z • x) = S.observable x) ∧
        ∀ a, ‖(𝔼 x ∈ translatedIntegerBox (origin a) (lengths a), T.eval x) -
          (𝔼 x ∈ translatedIntegerBox (origin a) (lengths a), S.eval x)‖ ≤
            2 * rho + Real.exp (verticalDecompositionBudget p - q)) := by
  classical
  obtain ⟨C, hC, hstep⟩ := exists_translated_step_drop s hs
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ d _ _ _ _ D ω hF p q rho hp hpq hσ hfreq hrho hrhop
    T hunit hTc V β origin lengths hlength hlarge
  obtain ⟨J, inst, eta, U, hcard, hheight, hU, hvertical, _, _, happrox, _⟩ :=
    T.exists_controlled_vertical_decomposition hp hTc rho hrho hrhop
  let := inst
  let K := D.filtration.gradedRefiltrationLayer V s
  by_cases hevent : ∃ (j : J) (a : β),
      Real.exp (-q) < ‖𝔼 x ∈ translatedIntegerBox (origin a) (lengths a), (U j).eval x‖ ∧
      ∃ v ∈ K, eta j v ≠ 0
  · left
    obtain ⟨j, a, hbias, hnonzero⟩ := hevent
    have hfactor := hstep D ω hF q (hp.trans hpq) hσ (U j) ((hU j).1.mono hpq)
      (eta j) (fun i => (hheight j i).trans hfreq) (hvertical j)
      (origin a) (lengths a) (hlength a) (hlarge a) hbias.le
    have hsymbol : (U j).symbol D.basis ω hF = T.symbol D.basis ω hF := by
      unfold RationalFilteredNilmanifold.Niltest.symbol
      apply congrArg (D.filtration.realPolynomialSymbolHom D.basis ω hF (fun _ => 1))
      apply NilpotentLieBCHGroup.ext
      apply Subtype.ext
      exact congrArg (fun o : D.filtration.realification.PolynomialOrbit (fun _ : σ => 1) => o.log)
        (hU j).2
    rw [hsymbol] at hfactor
    obtain ⟨l, W, u, hl, hlp, hspan, hgraded, hheightW, _hkill, hdim, hfixed⟩ :=
      ControlledSymbolFactorization.exists_dimension_drop D.filtration D.basis ω hF hfactor V hnonzero
    exact ⟨a, l, W, u, hl, hlp, hspan, hgraded, hheightW, hdim, hfixed⟩
  · right
    have hkill : ∀ j, (∃ a, Real.exp (-q) <
        ‖𝔼 x ∈ translatedIntegerBox (origin a) (lengths a), (U j).eval x‖) →
        ∀ v ∈ K, eta j v = 0 := by
      intro j ⟨a, ha⟩ v hv
      by_contra hne
      exact hevent ⟨j, a, ha, v, hv, hne⟩
    have hboxes (a : β) : (translatedIntegerBox (origin a) (lengths a)).Nonempty := by
      refine ⟨origin a, (mem_translatedIntegerBox (origin a) (lengths a) (origin a)).mpr ?_⟩
      intro i
      have hi := hlength a i
      exact ⟨le_rfl, by omega⟩
    obtain ⟨S, hS, hSc, hSo, hinv, herr⟩ := T.exists_finset_kernel_projection_family
      hunit hTc K (D.filtration.gradedRefiltrationLayer_le V s) eta U (fun j => (hU j).2)
      hvertical (fun a => translatedIntegerBox (origin a) (lengths a)) hboxes
      (fun _ => Real.exp (-q)) hrho.le (fun _ => (Real.exp_pos _).le)
      (fun x => by simpa only [norm_sub_rev] using happrox x) hkill
    refine ⟨S, hS, hSc, hSo, hinv, ?_⟩
    intro a
    apply (herr a).trans
    apply add_le_add le_rfl
    calc
      (Fintype.card J : ℝ) * Real.exp (-q) ≤
          Real.exp (verticalDecompositionBudget p) * Real.exp (-q) :=
        mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
      _ = Real.exp (verticalDecompositionBudget p - q) := by rw [← Real.exp_add, sub_eq_add_neg]

end Erdos3

end

end OAI
