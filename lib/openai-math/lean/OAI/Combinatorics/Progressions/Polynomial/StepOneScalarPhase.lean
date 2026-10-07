import OAI.Combinatorics.Progressions.Fourier.QuadraticFrequencyCoordinates

namespace OAI

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct BigOperators

theorem exists_stepOne_row_phase_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d N : ℕ} [NeZero N]
      (D : RationalFilteredNilmanifold L 1 d) {p : ℝ}, 0 ≤ p →
      ∀ T : D.Niltest (fun _ : Fin 2 => 1), T.ComplexityLE p →
      ∀ F : ZMod N → ZMod N → ℂ, (∀ h n, ‖F h n‖ ≤ 1) →
      Real.exp (-p) ≤ (𝔼 h : ZMod N, ‖𝔼 n : ZMod N, F h n * star (T.eval ![(h.val : ℤ), (n.val : ℤ)])‖) →
      ∃ α β : ℝ, Real.exp (-((p + C) ^ C)) ≤
        (𝔼 h : ZMod N, ‖𝔼 n : ZMod N, F h n *
          star (character ((((h.val : ℝ) * α + (n.val : ℝ) * β) : ℝ) : CircleFourier.Circle))‖) := by
  obtain ⟨A, _, hvertical⟩ := exists_verticalDecompositionBudget_bound
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + (2 * X + 2 + Polynomial.C A) ^ A + (2 * X + 2) + 2)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d N _ D p hp T hT F hF hmass
  let r := 2 * p + 2
  let δ := Real.exp (-(p + 2))
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hpr : p ≤ r := by dsimp [r]; linarith
  have hδ : 0 < δ := Real.exp_pos _
  have hδr : δ⁻¹ ≤ Real.exp r := by
    dsimp [δ]
    rw [← Real.exp_neg, neg_neg]
    exact Real.exp_le_exp.mpr (by dsimp [r]; linarith)
  obtain ⟨J, inst, η, U, hcard, _, hU, hchar, _, _, _, herr⟩ :=
    T.exists_controlled_vertical_decomposition hr (hT.mono hpr) δ hδ hδr
  let := inst
  have hrow (h : ZMod N) :
      ‖𝔼 n : ZMod N, F h n * star (T.eval ![(h.val : ℤ), (n.val : ℤ)])‖ ≤
        (∑ j : J, ‖𝔼 n : ZMod N, F h n * star ((U j).eval ![(h.val : ℤ), (n.val : ℤ)])‖) + δ := by
    apply (norm_correlation_partition_bound (F h)
      (fun n => T.eval ![(h.val : ℤ), (n.val : ℤ)])
      (fun j n => (U j).eval ![(h.val : ℤ), (n.val : ℤ)]) (hF h)).trans
    apply add_le_add le_rfl
    apply Finset.expect_le Finset.univ_nonempty
    intro n _
    simpa only [norm_sub_rev] using herr ![(h.val : ℤ), (n.val : ℤ)]
  have hm := Finset.expect_le_expect (s := Finset.univ) (fun h _ => hrow h)
  simp only [Finset.expect_add_distrib, Finset.expect_sum_comm, Fintype.expect_const] at hm
  have htwo : 2 * δ ≤ Real.exp (-p) := by
    calc
      _ ≤ Real.exp 2 * δ := mul_le_mul_of_nonneg_right
        (by linarith [Real.add_one_le_exp (2 : ℝ)]) hδ.le
      _ = _ := by dsimp [δ]; rw [← Real.exp_add]; congr 1; ring
  have hs : δ ≤ ∑ j : J, (𝔼 h : ZMod N, ‖𝔼 n : ZMod N, F h n * star ((U j).eval ![(h.val : ℤ), (n.val : ℤ)])‖) := by
    linarith
  obtain ⟨j, hj⟩ := exists_large_nonnegative_weighted_term (fun _ : J => (1 : ℝ))
    (fun j => 𝔼 h : ZMod N, ‖𝔼 n : ZMod N, F h n * star ((U j).eval ![(h.val : ℤ), (n.val : ℤ)])‖)
    (fun _ => by norm_num) (fun _ => Finset.expect_nonneg (fun _ _ => norm_nonneg _))
    hδ (Real.exp_pos _) (by simpa using hcard) (by simpa only [one_mul] using hs)
  let θ (k : Fin 2) := realifyFunctional (η j) (VectorPolynomial.coefficients (U j).orbit.log (Finsupp.single k 1))
  let γ := realifyFunctional (η j) (VectorPolynomial.coefficients (U j).orbit.log 0)
  let a := (U j).observable (QuotientGroup.mk (1 : D.RealGroup)) * character (γ : CircleFourier.Circle)
  let P (h n : ZMod N) := character ((((h.val : ℝ) * θ 0 + (n.val : ℝ) * θ 1) : ℝ) : CircleFourier.Circle)
  have heval (h n : ZMod N) : (U j).eval ![(h.val : ℤ), (n.val : ℤ)] = a * P h n := by
    rw [D.stepOne_niltest_eval_affine (U j) (η j) (hchar j)]
    simp only [a, P, γ, θ, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Int.cast_natCast, AddCircle.coe_add, character_add]
    ring
  have ha : ‖a‖ ≤ Real.exp r := by
    dsimp [a]
    rw [norm_mul, norm_character, mul_one]
    apply ((U j).norm_le _).trans
    have h := (U j).observable_budget (hU j).1
    have hl := (U j).lipBound.coe_nonneg
    linarith
  have hmean (h : ZMod N) :
      (𝔼 n : ZMod N, F h n * star ((U j).eval ![(h.val : ℤ), (n.val : ℤ)])) =
        star a * (𝔼 n : ZMod N, F h n * star (P h n)) := by
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro n _
    rw [heval, star_mul]
    ring
  have hupper : (𝔼 h : ZMod N, ‖𝔼 n : ZMod N, F h n * star ((U j).eval ![(h.val : ℤ), (n.val : ℤ)])‖) ≤
      Real.exp r * (𝔼 h : ZMod N, ‖𝔼 n : ZMod N, F h n * star (P h n)‖) := by
    simp only [hmean, norm_mul, norm_star, ← Finset.mul_expect]
    exact mul_le_mul_of_nonneg_right ha (Finset.expect_nonneg (fun _ _ => norm_nonneg _))
  have hchosen : Real.exp (-(p + 2 + verticalDecompositionBudget r)) ≤
      Real.exp r * (𝔼 h : ZMod N, ‖𝔼 n : ZMod N, F h n * star (P h n)‖) := by
    have hexp : δ / Real.exp (verticalDecompositionBudget r) = Real.exp (-(p + 2 + verticalDecompositionBudget r)) := by
      dsimp [δ]
      rw [← Real.exp_sub]
      congr 1
      ring
    rw [hexp] at hj
    exact hj.trans hupper
  have hlower : Real.exp (-(p + verticalDecompositionBudget r + r + 2)) ≤
      (𝔼 h : ZMod N, ‖𝔼 n : ZMod N, F h n * star (P h n)‖) := by
    apply (mul_le_mul_iff_right₀ (Real.exp_pos r)).mp
    calc
      Real.exp r * Real.exp (-(p + verticalDecompositionBudget r + r + 2)) =
          Real.exp (-(p + 2 + verticalDecompositionBudget r)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp r * (𝔼 h : ZMod N, ‖𝔼 n : ZMod N, F h n * star (P h n)‖) := hchosen
  have hcost : p + verticalDecompositionBudget r + r + 2 ≤ (p + C) ^ C := by
    have hh : p + (r + A) ^ A + r + 2 ≤ (p + C) ^ C := by
      simpa [X, r, Polynomial.eval₂_pow] using hbudget p hp
    linarith [hvertical r hr]
  exact ⟨θ 0, θ 1, (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans hlower⟩

theorem exists_fourier_of_stepOne_cross_correlation :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d N : ℕ} [NeZero N]
      (D : RationalFilteredNilmanifold L 1 d) {p : ℝ}, 0 ≤ p →
      ∀ T : D.Niltest (fun _ : Fin 2 => 1), T.ComplexityLE p →
      ∀ f g : ZMod N → ℂ, (∀ x, ‖f x‖ ≤ 1) → (∀ x, ‖g x‖ ≤ 1) →
      Real.exp (-p) ≤ (𝔼 h : ZMod N, ‖𝔼 n : ZMod N, (f n * star (g (n + h))) *
        star (T.eval ![(h.val : ℤ), (n.val : ℤ)])‖) →
      ∃ χ : AddChar (ZMod N) ℂ, Real.exp (-((p + C) ^ C)) ≤ ‖finiteFourierCoeff g χ‖ := by
  obtain ⟨C, hC, hphase⟩ := exists_stepOne_row_phase_budget
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d N _ D p hp T hT f g hf hg hmass
  obtain ⟨α, β, hcorr⟩ := hphase D hp T hT (fun h n => f n * star (g (n + h)))
    (fun shift point => by
      rw [norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hf point)).trans (hg _)) hmass
  let u (n : ZMod N) := f n * star (character (((n.val : ℝ) * β : ℝ) : CircleFourier.Circle))
  have hu (n : ZMod N) : ‖u n‖ ≤ 1 := by
    simpa only [u, norm_mul, norm_star, norm_character, mul_one] using hf n
  have hrow (h : ZMod N) :
      ‖𝔼 n : ZMod N, (f n * star (g (n + h))) *
        star (character ((((h.val : ℝ) * α + (n.val : ℝ) * β) : ℝ) : CircleFourier.Circle))‖ =
      ‖𝔼 n : ZMod N, u n * star (g (n + h))‖ := by
    have heq : (𝔼 n : ZMod N, (f n * star (g (n + h))) *
        star (character ((((h.val : ℝ) * α + (n.val : ℝ) * β) : ℝ) : CircleFourier.Circle))) =
        star (character (((h.val : ℝ) * α : ℝ) : CircleFourier.Circle)) *
          (𝔼 n : ZMod N, u n * star (g (n + h))) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro n _
      simp only [u, AddCircle.coe_add, character_add, star_mul]
      ring
    rw [heq, norm_mul, norm_star, norm_character, one_mul]
  simp only [hrow] at hcorr
  obtain ⟨χ, hχ⟩ := exists_large_fourier_of_mean_cross_correlation u g hu
  exact ⟨χ, hcorr.trans hχ⟩

end Erdos3

end

section

namespace Erdos3

open CircleFourier
open scoped TensorProduct BigOperators

theorem exists_stepOne_scalar_phase_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d N : ℕ} [NeZero N]
      (D : RationalFilteredNilmanifold L 1 d) {p : ℝ}, 0 ≤ p →
      ∀ T : D.Niltest (fun _ : Unit => 1), T.ComplexityLE p →
      ∀ f : ZMod N → ℂ, (∀ n, ‖f n‖ ≤ 1) →
      Real.exp (-p) ≤ ‖𝔼 n, f n * star (T.evalCyclic N (fun _ => n))‖ →
      ∃ β : ℝ, Real.exp (-((p + C) ^ C)) ≤
        ‖𝔼 n : ZMod N, f n * star (character (((n.val : ℝ) * β : ℝ) : CircleFourier.Circle))‖ := by
  obtain ⟨C, hC, hphase⟩ := exists_stepOne_row_phase_budget
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d N _ D p hp T hT f hf hcorr
  let projection : Unit → ((Fin 2 → ℤ) →+ ℤ) := fun _ =>
    { toFun := fun x => x 1, map_zero' := rfl, map_add' := fun _ _ => rfl }
  let U := T.linearPullbackHom projection
  have hU (h n : ZMod N) : U.eval ![(h.val : ℤ), (n.val : ℤ)] =
      T.evalCyclic N (fun _ => n) := by
    rw [RationalFilteredNilmanifold.Niltest.eval_linearPullbackHom]
    rfl
  have hmass : Real.exp (-p) ≤ 𝔼 h : ZMod N,
      ‖𝔼 n : ZMod N, f n * star (U.eval ![(h.val : ℤ), (n.val : ℤ)])‖ := by
    simpa only [hU, Fintype.expect_const] using hcorr
  obtain ⟨α, β, hresult⟩ := hphase D hp U hT (fun _ n => f n) (fun _ => hf) hmass
  have hrow (h : ZMod N) :
      ‖𝔼 n : ZMod N, f n * star (character
        ((((h.val : ℝ) * α + (n.val : ℝ) * β) : ℝ) : CircleFourier.Circle))‖ =
      ‖𝔼 n : ZMod N, f n * star (character (((n.val : ℝ) * β : ℝ) : CircleFourier.Circle))‖ := by
    have heq : (𝔼 n : ZMod N, f n * star (character
        ((((h.val : ℝ) * α + (n.val : ℝ) * β) : ℝ) : CircleFourier.Circle))) =
        star (character (((h.val : ℝ) * α : ℝ) : CircleFourier.Circle)) *
          (𝔼 n : ZMod N, f n * star (character (((n.val : ℝ) * β : ℝ) : CircleFourier.Circle))) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro n _
      simp only [AddCircle.coe_add, character_add, star_mul]
      ring
    rw [heq, norm_mul, norm_star, norm_character, one_mul]
  exact ⟨β, by simpa only [hrow, Fintype.expect_const] using hresult⟩

end Erdos3

end

end OAI
