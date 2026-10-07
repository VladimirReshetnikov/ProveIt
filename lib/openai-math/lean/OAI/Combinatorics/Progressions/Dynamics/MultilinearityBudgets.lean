import OAI.Combinatorics.Progressions.Estimates.CommonRefilteredFactorization

namespace OAI

section

namespace Erdos3.MultilinearityBudget

open RationalFilteredNilmanifold.MultidegreeStructure
open scoped NNReal

noncomputable def coordinates (p : ℝ) : ℝ := ((p + 4) ^ 2 + 2) ^ 63 + 3

noncomputable def ambient (p : ℝ) : ℝ := p + additiveTripleGeometryBudget p + coordinates p

noncomputable def quotient (p : ℝ) : ℝ := (ambient p + 3) ^ 11

noncomputable def observable (C : ℕ) (p : ℝ) : ℝ := p + (p + C) ^ C + (ambient p + 3) ^ 2 + 2

noncomputable def reconstruction (C : ℕ) (p : ℝ) : ℝ := ambient p + quotient p + observable C p + 1

noncomputable def total (C N : ℕ) (p : ℝ) : ℝ := quotient p + (reconstruction C p + N) ^ N + 4

theorem ambient_bounds {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ ambient p ∧ p ≤ ambient p ∧ additiveTripleGeometryBudget p ≤ ambient p ∧
      coordinates p ≤ ambient p := by
  have hG : 0 ≤ additiveTripleGeometryBudget p := by unfold additiveTripleGeometryBudget; positivity
  have hC : 0 ≤ coordinates p := by unfold coordinates; positivity
  refine ⟨add_nonneg (add_nonneg hp hG) hC, ?_, ?_, ?_⟩
  · exact (le_add_of_nonneg_right hG).trans (le_add_of_nonneg_right hC)
  · exact (le_add_of_nonneg_left hp).trans (le_add_of_nonneg_right hC)
  · exact le_add_of_nonneg_left (add_nonneg hp hG)

theorem quotient_bounds {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ quotient p ∧ ambient p ≤ quotient p ∧ (ambient p + 3) ^ 5 ≤ quotient p := by
  have hR := (ambient_bounds hp).1
  have hbase : 1 ≤ ambient p + 3 :=
    (by norm_num : (1 : ℝ) ≤ 3).trans (le_add_of_nonneg_left hR)
  have hpow : ambient p + 3 ≤ (ambient p + 3) ^ 11 := by
    simpa only [pow_one] using pow_le_pow_right₀ hbase (by decide : 1 ≤ 11)
  exact ⟨pow_nonneg (add_nonneg hR (by norm_num)) _,
    (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 3)).trans hpow,
    pow_le_pow_right₀ hbase (by decide : 5 ≤ 11)⟩

theorem observable_nonneg (C : ℕ) {p : ℝ} (hp : 0 ≤ p) : 0 ≤ observable C p := by
  unfold observable
  positivity

theorem reconstruction_bounds (C : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ reconstruction C p ∧ ambient p ≤ reconstruction C p ∧
      quotient p + 1 ≤ reconstruction C p ∧ observable C p ≤ reconstruction C p := by
  have hR := (ambient_bounds hp).1
  have hQ := (quotient_bounds hp).1
  have hO := observable_nonneg C hp
  refine ⟨add_nonneg (add_nonneg (add_nonneg hR hQ) hO) zero_le_one, ?_, ?_, ?_⟩
  · exact ((le_add_of_nonneg_right hQ).trans (le_add_of_nonneg_right hO)).trans
      (le_add_of_nonneg_right zero_le_one)
  · have h : quotient p ≤ ambient p + quotient p + observable C p :=
      (le_add_of_nonneg_left hR).trans (le_add_of_nonneg_right hO)
    exact add_le_add h (le_refl 1)
  · exact (le_add_of_nonneg_left (add_nonneg hR hQ)).trans (le_add_of_nonneg_right zero_le_one)

theorem total_bounds (C N : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    quotient p ≤ total C N p ∧ (reconstruction C p + N) ^ N + 4 ≤ total C N p := by
  have hQ := (quotient_bounds hp).1
  have hB := (reconstruction_bounds C hp).1
  have hN : 0 ≤ (reconstruction C p + N) ^ N := pow_nonneg (add_nonneg hB (Nat.cast_nonneg N)) _
  refine ⟨(le_add_of_nonneg_right hN).trans (le_add_of_nonneg_right (by norm_num)), ?_⟩
  exact add_le_add (show (reconstruction C p + N) ^ N ≤ quotient p + (reconstruction C p + N) ^ N
    from le_add_of_nonneg_left hQ) (le_refl 4)

theorem observable_bound (C : ℕ) (p : ℝ) (K A : ℝ≥0)
    (hK : (K : ℝ) ≤ Real.exp p) (hA : (A : ℝ) ≤ Real.exp ((p + C) ^ C)) :
    (3 : ℝ) * (K * (A * Real.exp ((ambient p + 3) ^ 2))) ≤ Real.exp (observable C p) := by
  have h3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hP : 0 ≤ Real.exp ((ambient p + 3) ^ 2) := (Real.exp_pos _).le
  have h := mul_le_mul h3
    (mul_le_mul hK (mul_le_mul_of_nonneg_right hA hP)
      (mul_nonneg A.coe_nonneg hP) (Real.exp_pos p).le)
    (mul_nonneg K.coe_nonneg (mul_nonneg A.coe_nonneg hP)) (Real.exp_pos 2).le
  simpa only [observable, Real.exp_add, mul_assoc, mul_comm, mul_left_comm] using h

theorem exists_total_bound (C N : ℕ) :
    ∃ Z : ℕ, 2 ≤ Z ∧ ∀ p : ℝ, 0 ≤ p → total C N p ≤ (p + Z) ^ Z := by
  let X : Polynomial ℕ := Polynomial.X
  let co : Polynomial ℕ := ((X + 4) ^ 2 + 2) ^ 63 + 3
  let geom : Polynomial ℕ := ((X + 6) ^ 2 + ((X + 4) ^ 2 + 2) ^ 63 + 6) ^ 11
  let R := X + geom + co
  let Q := (R + 3) ^ 11
  let O := X + (X + Polynomial.C C) ^ C + (R + 3) ^ 2 + 2
  let B := R + Q + O + 1
  obtain ⟨Z, hZ, hbudget⟩ := exists_natPolynomial_eval_budget (Q + (B + Polynomial.C N) ^ N + 4)
  refine ⟨Z, hZ, fun p hp => ?_⟩
  simpa [total, reconstruction, observable, quotient, ambient, coordinates,
    additiveTripleGeometryBudget, X, co, geom, R, Q, O, B, Polynomial.eval₂_pow] using hbudget p hp

end Erdos3.MultilinearityBudget

end

end OAI
