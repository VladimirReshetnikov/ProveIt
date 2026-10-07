import OAI.Combinatorics.Progressions.Dynamics.ComparisonEquivalenceBudget
import OAI.Combinatorics.Progressions.Estimates.VerticalTranslations

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct NNReal

theorem exists_native_vertical_translate_frame (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) {w : σ → ℕ} (T : D.Niltest w)
      {p : ℝ}, 0 ≤ p → T.ComplexityLE p → T.normBound ≤ 1 →
      ∀ eta : L →ₗ[ℚ] ℚ,
      (∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
        T.observable (z • x) =
          character ((realifyFunctional eta z.coord : ℝ) : CircleFourier.Circle) * T.observable x) →
      ∀ y : D.Space, Real.exp (-p) ≤ ‖T.observable y‖ →
      ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      ∃ u : Fin n → D.Space → ℂ,
        (∀ i x, ‖u i x‖ ≤ 1) ∧
        (letI := D.metricSpace; ∀ i, LipschitzWith K (u i)) ∧
        (∀ x, ∃ i, Real.exp (-(p + 1)) ≤ ‖u i x‖) ∧
        ∀ i z, z ∈ D.filtration.realification.subgroup s → ∀ x,
          u i (z • x) =
            character ((realifyFunctional eta z.coord : ℝ) : CircleFourier.Circle) * u i x := by
  obtain ⟨a, _, hrep⟩ := exists_realification_representatives_exp_bound s
  obtain ⟨b, _, hleft⟩ := exists_bounded_normalization_left_lipschitz s a
  obtain ⟨c, _, hcover⟩ := exists_native_quotient_parameter_cover s
  let X : Polynomial ℕ := Polynomial.X
  let Q := 2 * X + 2 * (X + Polynomial.C a + 2 + Polynomial.C b) ^ b + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + Q + (Q + Polynomial.C c) ^ c + 1)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ d D w T p hp hT hnorm eta hvertical y hy
  let := D.metricSpace
  let l := normalizedSquareLeftBudget a b p
  let q := 2 * p + 2 * l + 2
  have hl : 0 ≤ l := normalizedSquareLeftBudget_nonneg a b hp
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have htotal : p + q + (q + c) ^ c + 1 ≤ (p + C) ^ C := by
    simpa [X, Q, q, l, normalizedSquareLeftBudget, Polynomial.eval₂_pow] using hbudget p hp
  have hcp : 0 ≤ (q + c) ^ c := by positivity
  have hqp : q ≤ (p + C) ^ C := by linarith
  have hcount : (q + c) ^ c ≤ (p + C) ^ C := by linarith
  obtain ⟨A, _, hA, hLip⟩ := hleft D p hp hT.1
  have hrepresentatives : ∀ x : D.Space, ∃ r : D.RealGroup,
      (∀ i, |(D.basis.baseChange ℝ).repr r.coord i| ≤ Real.exp ((p + 1 + a) ^ a)) ∧
      QuotientGroup.mk r = x := by
    intro x
    induction x using Quotient.inductionOn with
    | h g =>
      obtain ⟨r, hr, γ, hγ, hg⟩ :=
        hrep D.basis D.filtration.lowerCentralSeries_eq_bot D.lattice D.grid
          ⌈Real.exp p⌉₊ (p + 1) D.grid_pos D.inner_grid
          (fun i j k => rationalHeightLE_ceil_exp (hT.1.2.2.1 i j k))
          (by linarith)
          (by simpa only [Fintype.card_fin] using hT.1.1.trans (show p ≤ p + 1 by linarith))
          (ceil_exp_le_exp_add_one hp) (hT.1.2.1.trans (Real.exp_le_exp.mpr (by linarith))) g
      refine ⟨r, hr, ?_⟩
      change (QuotientGroup.mk r : D.Space) = QuotientGroup.mk g
      rw [hg]
      exact (QuotientGroup.mk_mul_of_mem r (show γ ∈ D.realLattice from hγ)).symm
  choose r hr hrc using hrepresentatives
  have hInv (x : D.Space) : ∀ i,
      |(D.basis.baseChange ℝ).repr (r x)⁻¹.coord i| ≤ Real.exp ((p + 1 + a) ^ a) := by
    intro i
    simpa only [coord_inv, map_neg, Finsupp.neg_apply, abs_neg] using hr x i
  let ε := Real.exp (-q)
  have hε : 0 < ε := Real.exp_pos _
  have hεinv : 1 / ε ≤ Real.exp q := by
    simp only [ε, Real.exp_neg, one_div, inv_inv, le_refl]
  obtain ⟨n, hn, hnc, centers, hcenters⟩ :=
    hcover D hq (hT.1.mono D hpq) hε hεinv
  let K := T.lipBound * (A * A)
  let u (i : Fin n) (x : D.Space) := T.observable (r y • ((r (centers i))⁻¹ • x))
  have hK : (K : ℝ) ≤ Real.exp (p + 2 * l) := by
    have hTlip : (T.lipBound : ℝ) ≤ Real.exp p := by
      linarith [Niltest.observable_budget hT, T.normBound.coe_nonneg]
    calc
      _ ≤ Real.exp p * (Real.exp l * Real.exp l) := by
        dsimp [K]
        exact mul_le_mul hTlip (mul_le_mul hA hA A.coe_nonneg (Real.exp_nonneg _))
          (mul_nonneg A.coe_nonneg A.coe_nonneg) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have huLip (i : Fin n) : LipschitzWith K (u i) :=
    T.lipschitz.comp ((hLip (r y) (hr y)).comp (hLip ((r (centers i))⁻¹) (hInv _)))
  have hcenter (i : Fin n) : u i (centers i) = T.observable y := by
    change T.observable (r y • ((r (centers i))⁻¹ • centers i)) = T.observable y
    have heq : (r (centers i))⁻¹ • centers i = (QuotientGroup.mk (1 : D.RealGroup) : D.Space) := by
      calc
        _ = (r (centers i))⁻¹ • QuotientGroup.mk (r (centers i)) :=
          congrArg (fun x : D.Space => (r (centers i))⁻¹ • x) (hrc _).symm
        _ = _ := by simp only [MulAction.Quotient.smul_mk, smul_eq_mul, inv_mul_cancel]
    rw [heq]
    simp only [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, hrc]
  have herror : (K : ℝ) * ε ≤ Real.exp (-p) / 2 := by
    calc
      _ ≤ Real.exp (p + 2 * l) * Real.exp (-q) := mul_le_mul_of_nonneg_right hK hε.le
      _ = Real.exp (-p - 2) := by rw [← Real.exp_add]; congr 1; dsimp [q]; ring
      _ ≤ Real.exp (-p - 1) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ _ := exp_sub_one_le_half_exp (-p)
  refine ⟨n, hn, hnc.trans (Real.exp_le_exp.mpr hcount), K,
    hK.trans (Real.exp_le_exp.mpr (by dsimp [q] at hqp; linarith)), u, ?_, huLip, ?_, ?_⟩
  · intro i x
    have hnorm' : (T.normBound : ℝ) ≤ (1 : ℝ) := by exact_mod_cast hnorm
    exact (T.norm_le _).trans hnorm'
  · intro x
    obtain ⟨i, hi⟩ := hcenters x
    have hdist := (huLip i).dist_le_mul x (centers i)
    have herr : ‖u i (centers i) - u i x‖ ≤ Real.exp (-p) / 2 := by
      have h := hdist.trans ((mul_le_mul_of_nonneg_left hi K.coe_nonneg).trans herror)
      simpa only [dist_eq_norm, norm_sub_rev] using h
    have ht := norm_sub_norm_le (u i (centers i)) (u i x)
    rw [hcenter] at ht herr
    refine ⟨i, ?_⟩
    have hh : Real.exp (-(p + 1)) ≤ Real.exp (-p) / 2 := by
      simpa only [neg_add, sub_eq_add_neg] using exp_sub_one_le_half_exp (-p)
    linarith
  · intro i z hz x
    exact D.vertical_left_translate (fun x => T.observable (r y • x)) eta
      (fun z hz x => D.vertical_left_translate T.observable eta hvertical (r y) z hz x)
      ((r (centers i))⁻¹) z hz x

end Erdos3.RationalFilteredNilmanifold

end

end OAI
