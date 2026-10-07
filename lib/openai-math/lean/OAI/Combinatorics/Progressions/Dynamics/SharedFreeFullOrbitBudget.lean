import OAI.Combinatorics.Progressions.Lattices.SharedFreeAffineOrbitFamily

namespace OAI

section

namespace Erdos3

theorem exists_sharedFreePetalLiftBudget_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ q p : ℝ, 0 ≤ q → q ≤ p → 0 ≤ p →
      sharedFreePetalLiftBudget s q p ≤ (p + C) ^ C := by
  let R (X : Polynomial ℕ) := ((X + 1 + (X + 3) ^ 7 + 2) ^ 9 + X + 4) ^ 4
  let H (X : Polynomial ℕ) := X + R X + 2
  let G (X : Polynomial ℕ) := X + X * ((X + 2) ^ 7 + X)
  let V (X : Polynomial ℕ) := G (X + (X + (X + 3) ^ 7 + 2) ^ 4 + 1)
  let F (X : Polynomial ℕ) := (4 * X + (X + V (4 * X)) + 3) ^ 7
  let Λ : Polynomial ℕ :=
    (Polynomial.X + Polynomial.C (sharedFreeAffineConstant s)) ^ sharedFreeAffineConstant s
  let A : Polynomial ℕ := 4 * Polynomial.X + F (Polynomial.X + H Polynomial.X) + Λ
  let T₀ : Polynomial ℕ := (A + 2) ^ 4 + 1
  let T : Polynomial ℕ := (T₀ + 2) ^ 3 + (T₀ + 2) ^ 36 + Λ
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget T
  refine ⟨C, hC, ?_⟩
  intro q p hq hqp hp
  have hheight : 0 ≤ coefficientFourHeightBudget p := coefficientFourHeightBudget_nonneg hp
  have hF : fourRefinementAnnihilatorBudget (q + coefficientFourHeightBudget p) ≤
      fourRefinementAnnihilatorBudget (p + coefficientFourHeightBudget p) := by
    unfold fourRefinementAnnihilatorBudget fourRefinementBasisBudget preimageBasisBudget
      sparseGeneratorBudget
    gcongr
  have hA : sharedFreePetalLiftInput s q p ≤ sharedFreePetalLiftInput s p p := by
    unfold sharedFreePetalLiftInput
    linarith
  have hA0 : 0 ≤ sharedFreePetalLiftInput s q p := by
    have h := fourRefinementAnnihilatorBudget_nonneg (add_nonneg hq hheight)
    unfold sharedFreePetalLiftInput
    positivity
  have hupper : sharedFreePetalLiftBudget s q p ≤ sharedFreePetalLiftBudget s p p := by
    dsimp only [sharedFreePetalLiftBudget]
    gcongr
  apply hupper.trans
  simpa [T, T₀, A, Λ, F, V, G, H, R, sharedFreePetalLiftBudget, sharedFreePetalLiftInput,
    coefficientFourHeightBudget, refiltrationCoordinateBudget, fourRefinementAnnihilatorBudget,
    fourRefinementBasisBudget, preimageBasisBudget, sparseGeneratorBudget, Polynomial.eval₂_pow]
      using hbound p hp

end Erdos3

end

section

namespace Erdos3

theorem exists_sharedFreeCommonCorrectionBudget_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ q p : ℝ, 0 ≤ q → q ≤ p → 0 ≤ p →
      sharedFreeCommonCorrectionBudget s q p ≤ (p + C) ^ C := by
  let Λ : Polynomial ℕ :=
    (Polynomial.X + Polynomial.C (sharedFreeAffineConstant s)) ^ sharedFreeAffineConstant s
  let T₀ : Polynomial ℕ := 2 * Polynomial.X + Λ + 1
  let T : Polynomial ℕ := (T₀ + 2) ^ 3 + (T₀ + 2) ^ 36 + Λ
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget T
  refine ⟨C, hC, ?_⟩
  intro q p hq hqp hp
  have hupper : sharedFreeCommonCorrectionBudget s q p ≤
      sharedFreeCommonCorrectionBudget s p p := by
    dsimp only [sharedFreeCommonCorrectionBudget]
    gcongr
  apply hupper.trans
  simpa [T, T₀, Λ, sharedFreeCommonCorrectionBudget, two_mul, Polynomial.eval₂_pow]
    using hbound p hp

theorem exists_sharedFreeCommonPolynomialCorrectionBudget_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ q p : ℝ, 0 ≤ q → q ≤ p → 0 ≤ p →
      sharedFreeCommonCorrectionBudget s q p ≤ (p + C) ^ C ∧
      (s : ℝ) * sharedFreeCommonCorrectionBudget s q p ≤ (p + C) ^ C := by
  obtain ⟨c, _hc, hbase⟩ := exists_sharedFreeCommonCorrectionBudget_bound s
  let T : Polynomial ℕ := Polynomial.C (s + 1) * (Polynomial.X + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget T
  refine ⟨C, hC, ?_⟩
  intro q p hq hqp hp
  have heval : ((s : ℝ) + 1) * (p + c) ^ c ≤ (p + C) ^ C := by
    simpa [T, Polynomial.eval₂_pow] using hbound p hp
  have hsmall := hbase q p hq hqp hp
  have hnonneg : 0 ≤ (p + c) ^ c := by positivity
  have hmul := mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg s : (0 : ℝ) ≤ s)
  have hprod : 0 ≤ (s : ℝ) * (p + c) ^ c := mul_nonneg (Nat.cast_nonneg s) hnonneg
  constructor <;> nlinarith

end Erdos3

end

section

namespace Erdos3

theorem exists_sharedFreeFullOrbitBudget_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ q p : ℝ, 0 ≤ q → q ≤ p → 0 ≤ p →
      (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s ≤ (p + C) ^ C ∧
      sharedFreeCommonCorrectionBudget s q p ≤ (p + C) ^ C ∧
      sharedFreePetalLiftBudget s q p ≤ (p + C) ^ C ∧
      (s : ℝ) * (sharedFreeCommonCorrectionBudget s q p + sharedFreePetalLiftBudget s q p) ≤
        (p + C) ^ C ∧
      Real.exp (sharedFreeCommonCorrectionBudget s q p) + Real.exp (sharedFreePetalLiftBudget s q p) ≤
        Real.exp ((p + C) ^ C) := by
  obtain ⟨c, _hc, hcommon⟩ := exists_sharedFreeCommonCorrectionBudget_bound s
  obtain ⟨v, _hv, hpetal⟩ := exists_sharedFreePetalLiftBudget_bound s
  let Pc : Polynomial ℕ := (Polynomial.X + Polynomial.C c) ^ c
  let Pv : Polynomial ℕ := (Polynomial.X + Polynomial.C v) ^ v
  let Pa : Polynomial ℕ :=
    (Polynomial.X + Polynomial.C (sharedFreeAffineConstant s)) ^ sharedFreeAffineConstant s
  let T : Polynomial ℕ := Polynomial.C s * (Pc + Pv) + (Pc + Pv + 2) + Pa
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget T
  refine ⟨C, hC, ?_⟩
  intro q p hq hqp hp
  let Bc := (p + c) ^ c
  let Bv := (p + v) ^ v
  let Λ := (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
  have hBc : 0 ≤ Bc := pow_nonneg (add_nonneg hp (Nat.cast_nonneg c)) _
  have hBv : 0 ≤ Bv := pow_nonneg (add_nonneg hp (Nat.cast_nonneg v)) _
  have hΛ : 0 ≤ Λ := pow_nonneg (add_nonneg hp (Nat.cast_nonneg _)) _
  have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  have htotal : (s : ℝ) * (Bc + Bv) + (Bc + Bv + 2) + Λ ≤ (p + C) ^ C := by
    simpa [T, Pc, Pv, Pa, Bc, Bv, Λ, Polynomial.eval₂_pow] using hbound p hp
  have hprod : 0 ≤ (s : ℝ) * (Bc + Bv) := mul_nonneg hs0 (add_nonneg hBc hBv)
  have hplain : Bc + Bv + 2 ≤ (p + C) ^ C := by linarith only [htotal, hprod, hΛ]
  have hc := hcommon q p hq hqp hp
  have hv := hpetal q p hq hqp hp
  change sharedFreeCommonCorrectionBudget s q p ≤ Bc at hc
  change sharedFreePetalLiftBudget s q p ≤ Bv at hv
  have hscaled := mul_le_mul_of_nonneg_left (add_le_add hc hv) hs0
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change Λ ≤ _
    linarith only [htotal, hprod, hBc, hBv]
  · linarith only [hc, hplain, hBv]
  · linarith only [hv, hplain, hBc]
  · linarith only [hscaled, htotal, hBc, hBv, hΛ]
  · calc
      _ ≤ Real.exp Bc + Real.exp Bv :=
        add_le_add (Real.exp_le_exp.mpr hc) (Real.exp_le_exp.mpr hv)
      _ ≤ Real.exp Bc + Real.exp Bc + Real.exp Bv := by linarith only [Real.exp_pos Bc]
      _ ≤ Real.exp (Bc + Bv + 2) := exp_repeated_add_le hBc hBv
      _ ≤ _ := Real.exp_le_exp.mpr hplain

end Erdos3

end

end OAI
