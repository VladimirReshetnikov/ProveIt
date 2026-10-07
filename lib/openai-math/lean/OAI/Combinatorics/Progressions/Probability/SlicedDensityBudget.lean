/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Dynamics.SlicedProductBudget
import OAI.Combinatorics.Progressions.Polynomial.PolynomialPerturbationScaleLowerBound

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

theorem slicedUniformCap_le_exp {ι : Type*} [Fintype ι] {a δ P : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hP : 0 ≤ P)
    (haP : a⁻¹ ≤ Real.exp P) (hδP : δ⁻¹ ≤ Real.exp P)
    (m : ℕ) (hm : Fintype.card ι ≤ m) :
    (SlicedProductBlock.uniformCap ι (a * δ ^ (Fintype.card ι + 1))
      (mul_pos ha (pow_pos hδ _)) : ℝ) ≤ Real.exp (P + (P + 2) * (m + 1)) := by
  have h4 : (4 : ℝ) ≤ Real.exp 2 := by
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ = (2 : ℝ)^2 := by norm_num
      _ ≤ (Real.exp 1)^2 := pow_le_pow_left₀ (by norm_num) h2 _
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  change (a * δ ^ (Fintype.card ι + 1))⁻¹ * 4 ^ Fintype.card ι ≤ _
  rw [mul_inv_rev, ← inv_pow]
  calc
    _ ≤ ((Real.exp P) ^ (Fintype.card ι + 1) * Real.exp P) *
        (Real.exp 2) ^ Fintype.card ι := by gcongr
    _ = Real.exp ((Fintype.card ι + 1) * P + P + Fintype.card ι * 2) := by
      simp only [← Real.exp_nat_mul, ← Real.exp_add, Nat.cast_add, Nat.cast_one]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have hm' : (Fintype.card ι : ℝ) ≤ m := by exact_mod_cast hm
      nlinarith

theorem densityProductConstants_le_exp {D : Type*} [Fintype D]
    (K : D → ℝ≥0) {Q : ℝ} (hQ : 0 ≤ Q) (hK : ∀ d, (K d : ℝ) ≤ Real.exp Q)
    (O : ℕ) (hO : Fintype.card D ≤ O) :
    ((∏ d, K d : ℝ≥0) : ℝ) ≤ Real.exp ((O + 2) * (Q + 1) + O + 1) ∧
    (((∏ d, (K d + 1)) * ∑ d, K d * (2 * K d) : ℝ≥0) : ℝ) ≤
      Real.exp ((O + 2) * (Q + 1) + O + 1) := by
  have hO' : (Fintype.card D : ℝ) ≤ O := by exact_mod_cast hO
  have hp : (∏ d, (K d : ℝ)) ≤ Real.exp ((O : ℝ) * Q) := by
    calc
      _ ≤ ∏ _d : D, Real.exp Q := Finset.prod_le_prod₀ (fun _ _ => NNReal.coe_nonneg _) (fun d _ => hK d)
      _ = Real.exp ((Fintype.card D : ℝ) * Q) := by simp [← Real.exp_nat_mul]
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hO' hQ)
  have hp1 : (∏ d, ((K d : ℝ) + 1)) ≤ Real.exp ((O : ℝ) * (Q + 1)) := by
    calc
      _ ≤ ∏ _d : D, Real.exp (Q + 1) := Finset.prod_le_prod₀ (fun _ _ => by positivity)
        (fun d _ => by simpa only [add_comm] using one_add_le_exp_succ hQ (hK d))
      _ = Real.exp ((Fintype.card D : ℝ) * (Q + 1)) := by simp [← Real.exp_nat_mul]
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hO' (by positivity))
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hs : (∑ d, (K d : ℝ) * (2 * K d)) ≤ Real.exp ((O : ℝ) + 2 * Q + 1) := by
    calc
      _ ≤ ∑ _d : D, Real.exp Q * (Real.exp 1 * Real.exp Q) :=
        Finset.sum_le_sum (fun d _ => by gcongr; exact hK d; exact hK d)
      _ = (Fintype.card D : ℝ) * Real.exp (2 * Q + 1) := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (O : ℝ) * Real.exp (2 * Q + 1) := by
        gcongr
        linarith [Real.add_one_le_exp (O : ℝ)]
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  constructor
  · simp only [NNReal.coe_prod]
    exact hp.trans (Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) O]))
  · simp only [NNReal.coe_mul, NNReal.coe_prod, NNReal.coe_sum, NNReal.coe_add,
      NNReal.coe_one, NNReal.coe_ofNat]
    calc
      _ ≤ Real.exp ((O : ℝ) * (Q + 1)) * Real.exp ((O : ℝ) + 2 * Q + 1) := by gcongr
      _ ≤ _ := by rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith

end Erdos3

end

end OAI
