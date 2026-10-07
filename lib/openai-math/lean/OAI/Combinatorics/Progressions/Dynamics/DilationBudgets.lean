import OAI.Combinatorics.Progressions.Estimates.ControlledComparisonModel

namespace OAI

section

namespace Erdos3.DilationBudget

open RationalFilteredNilmanifold
open scoped NNReal

noncomputable def height (q : ℤ) : ℕ := ⌈rationalLogHeight (q : ℚ)⌉₊

noncomputable def shift (q : ℤ) (p : ℝ) : ℝ := p + height q

noncomputable def ambient (t : ℕ) (q : ℤ) (p : ℝ) : ℝ :=
  shift q p + dilationPairGeometryBudget t (shift q p) + 2 * (shift q p + 1)

noncomputable def quotient (t : ℕ) (q : ℤ) (p : ℝ) : ℝ := (ambient t q p + 3) ^ 11

noncomputable def common (t : ℕ) (q : ℤ) (C : ℕ) (p : ℝ) : ℝ :=
  ambient t q p + quotient t q p + (p + C) ^ C + 4

noncomputable def reconstruction (t : ℕ) (q : ℤ) (p : ℝ) : ℝ :=
  3 * p + (p + 3) ^ 2 + (q ^ t).natAbs + 6

noncomputable def total (t : ℕ) (q : ℤ) (N : ℕ) (p : ℝ) : ℝ :=
  p + (reconstruction t q p + N) ^ N + 4

theorem shift_bounds (q : ℤ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ shift q p ∧ p ≤ shift q p ∧ rationalLogHeight (q : ℚ) ≤ shift q p := by
  have hh : rationalLogHeight (q : ℚ) ≤ (height q : ℝ) := Nat.le_ceil _
  exact ⟨add_nonneg hp (Nat.cast_nonneg _), le_add_of_nonneg_right (Nat.cast_nonneg _),
    hh.trans (le_add_of_nonneg_left hp)⟩

theorem ambient_bounds (t : ℕ) (q : ℤ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ ambient t q p ∧ shift q p ≤ ambient t q p ∧
      dilationPairGeometryBudget t (shift q p) ≤ ambient t q p ∧
      2 * (shift q p + 1) ≤ ambient t q p := by
  have hr := (shift_bounds q hp).1
  have hG : 0 ≤ dilationPairGeometryBudget t (shift q p) := by
    unfold dilationPairGeometryBudget
    positivity
  have hc : 0 ≤ 2 * (shift q p + 1) := by positivity
  unfold ambient
  exact ⟨by positivity, by linarith, by linarith, by linarith⟩

theorem quotient_bounds (t : ℕ) (q : ℤ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ quotient t q p ∧ ambient t q p ≤ quotient t q p ∧
      (ambient t q p + 3) ^ 5 ≤ quotient t q p := by
  have hA := (ambient_bounds t q hp).1
  have hb : 1 ≤ ambient t q p + 3 := by linarith
  have hpow : ambient t q p + 3 ≤ (ambient t q p + 3) ^ 11 := by
    simpa only [pow_one] using pow_le_pow_right₀ hb (by decide : 1 ≤ 11)
  exact ⟨by unfold quotient; positivity, (by linarith : ambient t q p ≤ ambient t q p + 3).trans hpow,
    pow_le_pow_right₀ hb (by decide : 5 ≤ 11)⟩

theorem common_bounds (t : ℕ) (q : ℤ) (C : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ common t q C p ∧ p ≤ common t q C p ∧
      ambient t q p ≤ common t q C p ∧ quotient t q p ≤ common t q C p ∧
      (p + C) ^ C ≤ common t q C p := by
  have hA := (ambient_bounds t q hp).1
  have hQ := (quotient_bounds t q hp).1
  have hN : 0 ≤ (p + C) ^ C := by positivity
  have hpA := (shift_bounds q hp).2.1.trans (ambient_bounds t q hp).2.1
  unfold common
  exact ⟨by positivity, by linarith, by linarith, by linarith, by linarith⟩

theorem reconstruction_bounds (t : ℕ) (q : ℤ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ reconstruction t q p ∧ p + 1 ≤ reconstruction t q p := by
  have hn : 0 ≤ ((q ^ t).natAbs : ℝ) := Nat.cast_nonneg _
  unfold reconstruction
  constructor <;> nlinarith only [hp, hn, sq_nonneg (p + 3)]

theorem observable_bound (t : ℕ) (q : ℤ) {p : ℝ} (hp : 0 ≤ p) (K A : ℝ≥0)
    (hK : (K : ℝ) ≤ Real.exp p) (hA : (A : ℝ) ≤ Real.exp p) :
    (((q ^ t).natAbs : ℝ) + 1) * (K * (A * Real.exp ((p + 3) ^ 2))) ≤
      Real.exp (reconstruction t q p) := by
  have hn : ((q ^ t).natAbs : ℝ) + 1 ≤ Real.exp ((q ^ t).natAbs : ℝ) := Real.add_one_le_exp _
  have hP : 0 ≤ Real.exp ((p + 3) ^ 2) := (Real.exp_pos _).le
  have h := mul_le_mul hn
    (mul_le_mul hK (mul_le_mul_of_nonneg_right hA hP)
      (mul_nonneg A.coe_nonneg hP) (Real.exp_pos p).le)
    (mul_nonneg K.coe_nonneg (mul_nonneg A.coe_nonneg hP)) (Real.exp_pos _).le
  have he : Real.exp ((q ^ t).natAbs : ℝ) *
      (Real.exp p * (Real.exp p * Real.exp ((p + 3) ^ 2))) =
      Real.exp (2 * p + (p + 3) ^ 2 + (q ^ t).natAbs) := by
    rw [show 2 * p = p + p by ring]
    simp only [Real.exp_add]
    ring
  rw [he] at h
  exact h.trans (Real.exp_le_exp.mpr (by unfold reconstruction; linarith))

theorem total_bounds (t : ℕ) (q : ℤ) (N : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    p ≤ total t q N p ∧ (reconstruction t q p + N) ^ N + 4 ≤ total t q N p := by
  have hr := (reconstruction_bounds t q hp).1
  have hpow : 0 ≤ (reconstruction t q p + N) ^ N := by positivity
  unfold total
  exact ⟨by linarith, by linarith⟩

theorem exists_full_bound (t : ℕ) (q : ℤ) (C N : ℕ) :
    ∃ Z : ℕ, 2 ≤ Z ∧ ∀ p : ℝ, 0 ≤ p →
      total t q N (common t q C p) ≤ (p + Z) ^ Z ∧
        ((q ^ t).natAbs + 1 : ℝ) * p ≤ (p + Z) ^ Z := by
  let X : Polynomial ℕ := Polynomial.X
  let r := X + Polynomial.C (height q)
  let G := ((r + 4) ^ 2 + Polynomial.C (t + 2) * (r + 1) + 6) ^ 11
  let A := r + G + 2 * (r + 1)
  let B := A + (A + 3) ^ 11 + (X + Polynomial.C C) ^ C + 4
  let R := 3 * B + (B + 3) ^ 2 + Polynomial.C (q ^ t).natAbs + 6
  let P := B + (R + Polynomial.C N) ^ N + 4
  obtain ⟨Z, hZ, hz⟩ := exists_natPolynomial_eval_budget
    (P + Polynomial.C ((q ^ t).natAbs + 1) * X)
  refine ⟨Z, hZ, fun p hp => ?_⟩
  have h : total t q N (common t q C p) + ((q ^ t).natAbs + 1 : ℝ) * p ≤ (p + Z) ^ Z := by
    simpa [total, reconstruction, common, quotient, ambient, shift, dilationPairGeometryBudget,
      X, r, G, A, B, R, P, Polynomial.eval₂_pow, Nat.cast_add] using hz p hp
  have ht : 0 ≤ total t q N (common t q C p) :=
    (common_bounds t q C hp).1.trans (total_bounds t q N (common_bounds t q C hp).1).1
  have hn : 0 ≤ ((q ^ t).natAbs + 1 : ℝ) * p := by positivity
  exact ⟨by linarith, by linarith⟩

end Erdos3.DilationBudget

end

end OAI
