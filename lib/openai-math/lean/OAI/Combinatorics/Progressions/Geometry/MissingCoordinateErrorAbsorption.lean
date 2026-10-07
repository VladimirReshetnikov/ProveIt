import OAI.Combinatorics.Progressions.Nilpotent.MissingCoordinateNiltestApproximation

namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem exists_absorb_missing_coordinate_error (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} {D : RationalFilteredNilmanifold L s d} {p : ℝ}
      (T : D.Niltest (fun _ : Fin (s + 1) => 1)), T.ComplexityLE p →
      ∀ {G X : Type*} (H : Finset G), H.Nonempty →
      ∀ (S : G → Finset X), (∀ h ∈ H, (S h).Nonempty) →
      ∀ (sample : G → X → Fin (s + 1) → ℤ) (f : G → X → ℂ),
      (∀ h ∈ H, ∀ x ∈ S h, ‖f h x‖ ≤ 1) →
      (∀ h ∈ H, Real.exp (-p) ≤ ‖𝔼 x ∈ S h, f h x * star (T.eval (sample h x))‖) →
      ∃ A : Fin (s + 1) → (Fin (s + 1) → ℤ) → ℂ,
        (∀ i x, ‖A i x‖ ≤ 1) ∧
        (∀ i x y, (∀ k, k ≠ i → x k = y k) → A i x = A i y) ∧
        ∃ H' : Finset G, H' ⊆ H ∧ H'.Nonempty ∧
          Real.exp (-((p + C) ^ C)) * (H.card : ℝ) ≤ (H'.card : ℝ) ∧
          ∀ h ∈ H', Real.exp (-((p + C) ^ C)) ≤
            ‖𝔼 x ∈ S h, f h x * ∏ i, A i (sample h x)‖ := by
  obtain ⟨a, _, hsplit⟩ := exists_missing_coordinate_niltest_approximation s 2
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (2 * X + (X + Polynomial.C a) ^ a + 2)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D p T hT G Ω H hH S hS sample f hf hcorr
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hT.1.1
  let U := T.expNormalize p
  let epsilon := Real.exp (-(2 * p + 1))
  let q := (p + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hcost : 2 * p + q + 2 ≤ (p + C) ^ C := by
    simpa [X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith only [hp, hcost]
  have hscale : 1 / epsilon ≤ Real.exp ((p + 2) ^ 2) := by
    dsimp [epsilon]
    rw [one_div, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    nlinarith only [sq_nonneg p, hp]
  obtain ⟨m, _, hm, c, V, hc, hV, hindependent, happ⟩ :=
    hsplit U (T.expNormalize_complexity hT) (T.expNormalize_norm hT)
      epsilon (Real.exp_pos _) hscale
  have hepsilon : epsilon ≤ Real.exp (-(2 * p)) / 2 := by
    simpa only [epsilon, show -(2 * p + 1) = -(2 * p) - 1 by ring] using
      exp_sub_one_le_half_exp (-(2 * p))
  have hsmall : Real.exp (-(2 * p + q + 2)) ≤ Real.exp (-(2 * p)) / (2 * Real.exp q * 2) := by
    calc
      _ = Real.exp (-(2 * p + q) - 1 - 1) := by congr 1; ring
      _ ≤ Real.exp (-(2 * p + q) - 1) / 2 := exp_sub_one_le_half_exp _
      _ ≤ (Real.exp (-(2 * p + q)) / 2) / 2 :=
        div_le_div_of_nonneg_right (exp_sub_one_le_half_exp _) (by norm_num)
      _ = _ := by rw [show -(2 * p + q) = -(2 * p) - q by ring, Real.exp_sub]; ring
  let R (h : G) (_ : Unit) (j : Fin m) : Prop :=
    Real.exp (-(2 * p + q + 2)) ≤
      ‖𝔼 x ∈ S h, f h x * star (∏ i, V i j (sample h x))‖
  have hchoice : ∀ h ∈ H, ∀ u, ∃ j, R h u j := by
    intro h hh _
    have hmean : (𝔼 x ∈ S h, f h x * star (U.eval (sample h x))) =
        (Real.exp (-p) : ℂ) * (𝔼 x ∈ S h, f h x * star (T.eval (sample h x))) := by
      rw [Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro x _
      simp only [U, RationalFilteredNilmanifold.Niltest.expNormalize_eval,
        star_mul, Complex.star_def, Complex.conj_ofReal]
      ring
    have hnorm : Real.exp (-(2 * p)) ≤ ‖finiteCorrelation (S h) (f h)
        (fun x => U.eval (sample h x))‖ := by
      unfold finiteCorrelation
      rw [hmean, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
      calc
        _ = Real.exp (-p) * Real.exp (-p) := by rw [← Real.exp_add]; congr 1; ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hcorr h hh) (Real.exp_nonneg _)
    obtain ⟨j, hj⟩ := exists_correlating_weighted_summand (hS h hh) (f h)
      (fun x => U.eval (sample h x)) (fun j x => ∏ i, V i j (sample h x)) c
      (Real.exp_pos (-(2 * p))) (Real.exp_pos q) (by norm_num : (0 : ℝ) < 2)
      (by simpa only [Fintype.card_fin] using hm) hc (hf h hh)
      (fun x _ => by rw [norm_sub_rev]; exact (happ (sample h x)).trans hepsilon) hnorm
    exact ⟨j, hsmall.trans hj⟩
  obtain ⟨j, H', hsub, hH', hdense, hfixed⟩ := exists_large_fixed_choices H hH R hchoice
    (by simpa only [Fintype.card_fin] using hm)
  refine ⟨(fun i x => star (V i (j ()) x)), ?_, ?_, H', hsub, hH', ?_, ?_⟩
  · intro i x
    simpa only [norm_star] using hV i (j ()) x
  · intro i x y hxy
    exact congrArg star (hindependent i (j ()) x y hxy)
  · have hdense' : Real.exp (-q) * (H.card : ℝ) ≤ (H'.card : ℝ) := by
      simpa only [Fintype.card_unit, Nat.cast_one, mul_one] using hdense
    exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hdense'
  · intro h hh
    simpa only [star_prod] using
      (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans (hfixed h hh ())

end Erdos3

end

end OAI
