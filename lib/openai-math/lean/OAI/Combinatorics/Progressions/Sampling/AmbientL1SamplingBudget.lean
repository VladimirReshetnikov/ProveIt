import OAI.Combinatorics.Progressions.Polynomial.PolynomialDensityBudget

namespace OAI

section

namespace Erdos3
open scoped NNReal

noncomputable def ambientL1FourierInput {A : Type*} [Semiring A] (T : A) : A := 2 * T + 1
noncomputable def ambientL1SamplingBudget {A : Type*} [Semiring A] (T : A) : A :=
  let Q := ambientL1FourierInput T
  T + (2 * Q + 1) * (2 * Q + 2) ^ 4 + Q

theorem ambientL1SamplingBudget_bounds {T : ℝ} (hT : 0 ≤ T)
    {Lf Lg Cf Cg Ljet : ℝ≥0} {η : ℝ}
    (hf : (Lf : ℝ) ≤ Real.exp T) (hg : (Lg : ℝ) ≤ Real.exp T)
    (hcf : (Cf : ℝ) ≤ Real.exp T) (hcg : (Cg : ℝ) ≤ Real.exp T)
    (hjet : (Ljet : ℝ) ≤ Real.exp T) (hη : η⁻¹ ≤ Real.exp T) :
    let Q := ambientL1FourierInput T
    let P := ambientL1SamplingBudget T
    0 ≤ Q ∧ T ≤ Q ∧ T ≤ P ∧
      (((Lf + Lg) * Ljet : ℝ≥0) : ℝ) ≤ Real.exp Q ∧ η⁻¹ ≤ Real.exp Q ∧
      Real.exp ((2 * Q + 2) ^ 4) ≤ Real.exp P ∧
      Real.exp (2 * Q * (2 * Q + 2) ^ 4) * (Cf + Cg : ℝ≥0) ≤ Real.exp P := by
  intro Q P
  have hTQ : T ≤ Q := by dsimp [Q, ambientL1FourierInput]; linarith
  have hQ : 0 ≤ Q := hT.trans hTQ
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hsum {a b : ℝ≥0} (ha : (a : ℝ) ≤ Real.exp T) (hb : (b : ℝ) ≤ Real.exp T) :
      ((a + b : ℝ≥0) : ℝ) ≤ Real.exp (T + 1) := by
    rw [NNReal.coe_add, Real.exp_add]
    calc
      _ ≤ 2 * Real.exp T := by linarith
      _ ≤ _ := by nlinarith [Real.exp_pos T]
  have hl : (((Lf + Lg) * Ljet : ℝ≥0) : ℝ) ≤ Real.exp Q := by
    rw [NNReal.coe_mul]
    apply (mul_le_mul (hsum hf hg) hjet (NNReal.coe_nonneg _) (Real.exp_nonneg _)).trans_eq
    rw [← Real.exp_add]
    congr 1
    dsimp [Q, ambientL1FourierInput]
    ring
  have hc : ((Cf + Cg : ℝ≥0) : ℝ) ≤ Real.exp Q :=
    (hsum hcf hcg).trans (Real.exp_le_exp.mpr (by dsimp [Q, ambientL1FourierInput]; linarith))
  have hpow : 0 ≤ (2 * Q + 2) ^ 4 := by positivity
  have hprod : 0 ≤ 2 * Q * (2 * Q + 2) ^ 4 := by positivity
  have hTP : T ≤ P := by
    change T ≤ T + (2 * Q + 1) * (2 * Q + 2) ^ 4 + Q
    nlinarith
  have hfreq : (2 * Q + 2) ^ 4 ≤ P := by
    change (2 * Q + 2) ^ 4 ≤ T + (2 * Q + 1) * (2 * Q + 2) ^ 4 + Q
    nlinarith
  have hcoeff : 2 * Q * (2 * Q + 2) ^ 4 + Q ≤ P := by
    change _ ≤ T + (2 * Q + 1) * (2 * Q + 2) ^ 4 + Q
    nlinarith
  refine ⟨hQ, hTQ, hTP, hl, hη.trans (Real.exp_le_exp.mpr hTQ), Real.exp_le_exp.mpr hfreq, ?_⟩
  calc
    _ ≤ Real.exp (2 * Q * (2 * Q + 2) ^ 4) * Real.exp Q :=
      mul_le_mul_of_nonneg_left hc (Real.exp_nonneg _)
    _ = _ := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr hcoeff

theorem exists_ambientL1SamplingThreshold_bound (K : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ T : ℝ, 0 ≤ T →
      (ambientL1SamplingBudget T + K) ^ K ≤ (T + A) ^ A := by
  obtain ⟨A, hA, hb⟩ := exists_natPolynomial_eval_budget
    ((ambientL1SamplingBudget Polynomial.X + Polynomial.C K) ^ K)
  refine ⟨A, hA, ?_⟩
  intro T hT
  simpa [ambientL1SamplingBudget, ambientL1FourierInput, Polynomial.eval₂_pow] using hb T hT

end Erdos3

end

end OAI
