import OAI.Combinatorics.Progressions.Estimates.SharedFreeFrozenComparison
import OAI.Combinatorics.Progressions.Estimates.SharedFreeLowerFactorization

namespace OAI

section

namespace Erdos3

noncomputable def sharedFreeCorrelationInput (s : ℕ) (p : ℝ) : ℝ :=
  p + (p + (exists_sharedFreeFullOrbitBudget_bound s).choose) ^
      (exists_sharedFreeFullOrbitBudget_bound s).choose +
    (p + sharedFreeFactorFreezingConstant s) ^ sharedFreeFactorFreezingConstant s + 2

noncomputable def sharedFreeCorrelationBudget (s : ℕ) (hs : 2 ≤ s) (p : ℝ) : ℝ :=
  (sharedFreeCorrelationInput s p + sharedFactorCorrelationConstant s hs) ^
    sharedFactorCorrelationConstant s hs

theorem sharedFreeCorrelationInput_bounds (s : ℕ) {q p : ℝ}
    (hq : 0 ≤ q) (hqp : q ≤ p) (hp : 0 ≤ p) :
    2 ≤ sharedFreeCorrelationInput s p ∧ q ≤ sharedFreeCorrelationInput s p ∧
    (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s ≤ sharedFreeCorrelationInput s p ∧
    (s : ℝ) * (sharedFreeCommonCorrectionBudget s q p + sharedFreePetalLiftBudget s q p) ≤
      sharedFreeCorrelationInput s p ∧
    Real.exp (sharedFreeCommonCorrectionBudget s q p) + Real.exp (sharedFreePetalLiftBudget s q p) ≤
      Real.exp ((sharedFreeCorrelationInput s p + 2) ^ 1) ∧
    (p + sharedFreeFactorFreezingConstant s) ^ sharedFreeFactorFreezingConstant s ≤
      sharedFreeCorrelationInput s p := by
  let a := (exists_sharedFreeFullOrbitBudget_bound s).choose
  let b := sharedFreeFactorFreezingConstant s
  have ha : 0 ≤ (p + a) ^ a := by positivity
  have hb : 0 ≤ (p + b) ^ b := by positivity
  have h2 : 2 ≤ sharedFreeCorrelationInput s p := by
    change 2 ≤ p + (p + a) ^ a + (p + b) ^ b + 2
    linarith
  have hpa : (p + a) ^ a ≤ sharedFreeCorrelationInput s p := by
    change (p + a) ^ a ≤ p + (p + a) ^ a + (p + b) ^ b + 2
    linarith
  have hpb : (p + b) ^ b ≤ sharedFreeCorrelationInput s p := by
    change (p + b) ^ b ≤ p + (p + a) ^ a + (p + b) ^ b + 2
    linarith
  have hqT : q ≤ sharedFreeCorrelationInput s p := by
    change q ≤ p + (p + a) ^ a + (p + b) ^ b + 2
    linarith
  obtain ⟨hΛ, _, _, hden, hslow⟩ := (exists_sharedFreeFullOrbitBudget_bound s).choose_spec.2 q p hq hqp hp
  refine ⟨h2, hqT, hΛ.trans hpa, hden.trans hpa, ?_, hpb⟩
  exact hslow.trans (Real.exp_le_exp.mpr (by simpa only [pow_one] using
    (hpa.trans (show sharedFreeCorrelationInput s p ≤ sharedFreeCorrelationInput s p + 2 by linarith))))

theorem sharedFreeCorrelationInput_le_budget (s : ℕ) (hs : 2 ≤ s) {p : ℝ} (hp : 0 ≤ p) :
    sharedFreeCorrelationInput s p ≤ sharedFreeCorrelationBudget s hs p := by
  let T := sharedFreeCorrelationInput s p
  let C := sharedFactorCorrelationConstant s hs
  have hT : 2 ≤ T := (sharedFreeCorrelationInput_bounds s hp le_rfl hp).1
  have hC : 2 ≤ C := (exists_shared_factor_correlations s hs).choose_spec.1
  have hbase : 1 ≤ T + C := by linarith [Nat.cast_nonneg (α := ℝ) C]
  change T ≤ (T + C) ^ C
  exact (le_add_of_nonneg_right (Nat.cast_nonneg (α := ℝ) C)).trans
    ((pow_one (T + C)).symm.le.trans (pow_le_pow_right₀ hbase (by omega : 1 ≤ C)))

theorem exists_sharedFreeCorrelationBudget_bound (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ q p : ℝ, 0 ≤ q → q ≤ p → 0 ≤ p →
      let B := sharedFreeCorrelationBudget s hs p
      let Q := B + sharedFreeComparisonBasisBudget q p + 2
      (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s + B ≤ (p + C) ^ C ∧
      (Q + nativePairModelConstant s) ^ nativePairModelConstant s ≤ (p + C) ^ C ∧
      nativeLowerPairModelBudget s Q ≤ (p + C) ^ C := by
  obtain ⟨b, _, hb⟩ := exists_sharedFreeComparisonBasisBudget_bound
  obtain ⟨c, _, hc⟩ := exists_nativeLowerPairModelBudget_bound s
  let a := (exists_sharedFreeFullOrbitBudget_bound s).choose
  let d := sharedFreeFactorFreezingConstant s
  let e := sharedFactorCorrelationConstant s hs
  let f := sharedFreeAffineConstant s
  let T : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C a) ^ a +
    (Polynomial.X + Polynomial.C d) ^ d + 2
  let B : Polynomial ℕ := (T + Polynomial.C e) ^ e
  let Q : Polynomial ℕ := B + (Polynomial.X + Polynomial.C b) ^ b + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Polynomial.X + Polynomial.C f) ^ f + B + (Q + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro q p hq hqp hp B₀ Q₀
  have hB₀ : 0 ≤ B₀ := by
    apply le_trans (show 0 ≤ sharedFreeCorrelationInput s p from
      (by linarith [(sharedFreeCorrelationInput_bounds s hq hqp hp).1]))
    exact sharedFreeCorrelationInput_le_budget s hs hp
  have hQ₀ : 0 ≤ Q₀ := by
    have := sharedFreeComparisonBasisBudget_nonneg hq hp
    dsimp only [Q₀]
    positivity
  let v := B₀ + (p + b) ^ b + 2
  have hQv : Q₀ ≤ v := by
    dsimp only [Q₀, v]
    linarith [hb q p hq hqp hp]
  have hv : 0 ≤ v := hQ₀.trans hQv
  have hΛ : 0 ≤ (p + f) ^ f := by positivity
  have hsum : (p + f) ^ f + B₀ + (v + c) ^ c ≤ (p + C) ^ C := by
    change (p + f) ^ f + (p + (p + a) ^ a + (p + d) ^ d + 2 + e) ^ e +
      ((p + (p + a) ^ a + (p + d) ^ d + 2 + e) ^ e + (p + b) ^ b + 2 + c) ^ c ≤ _
    simpa [T, B, Q, Polynomial.eval₂_pow] using hbudget p hp
  have htail : (v + c) ^ c ≤ (p + C) ^ C := by linarith
  have hfirst : (p + f) ^ f + B₀ ≤ (p + C) ^ C := by
    linarith [show 0 ≤ (v + c) ^ c by positivity]
  have hpow : (Q₀ + c) ^ c ≤ (v + c) ^ c :=
    pow_le_pow_left₀ (by positivity) (by linarith) c
  exact ⟨hfirst, (hc Q₀ hQ₀).1.trans (hpow.trans htail),
    (hc Q₀ hQ₀).2.trans (hpow.trans htail)⟩

end Erdos3

end

end OAI
