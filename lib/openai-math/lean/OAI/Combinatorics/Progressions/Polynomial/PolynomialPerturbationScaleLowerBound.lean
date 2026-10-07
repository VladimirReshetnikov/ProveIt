import OAI.Combinatorics.Progressions.Estimates.ResidualErrorAllocation
import OAI.Combinatorics.Progressions.Polynomial.PolynomialPerturbationScaleBudget

namespace OAI

section

namespace Erdos3

theorem polynomialPerturbationScale_inverse_le_exp {K M Q τ P : ℝ}
    (hK : 0 ≤ K) (hM : 0 ≤ M) (hQ : 0 ≤ Q) (hτ : 0 < τ) (hP : 0 ≤ P)
    (m : ℕ) (hm : (m : ℝ) ≤ Real.exp P)
    (hKP : K ≤ Real.exp P) (hMP : M ≤ Real.exp P) (hQP : Q ≤ Real.exp P)
    (hτP : τ⁻¹ ≤ Real.exp P) :
    (polynomialPerturbationScale K M Q τ m)⁻¹ ≤ Real.exp (6*P+8) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h16 : (16 : ℝ) ≤ Real.exp 4 := by
    calc
      _ = (2 : ℝ)^4 := by norm_num
      _ ≤ (Real.exp 1)^4 := pow_le_pow_left₀ (by norm_num) h2 _
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hm1 : (m : ℝ)+1 ≤ Real.exp (P+1) := by
    simpa only [add_comm] using one_add_le_exp_succ hP hm
  have hK1 := one_add_le_exp_succ hP hKP
  have hM1 := one_add_le_exp_succ hP hMP
  have hQ1 := one_add_le_exp_succ hP hQP
  apply inv_min_le_of_inv_le
  · simpa only [inv_one] using Real.one_le_exp_iff.mpr (by positivity : 0 ≤ 6*P+8)
  · apply inv_min_le_of_inv_le
    · calc
        (1/(2*(1+K)*(1+M)))⁻¹ = 2*(1+K)*(1+M) := by simp
        _ ≤ Real.exp 1*Real.exp (P+1)*Real.exp (P+1) := by gcongr
        _ = Real.exp (2*P+3) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
        _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
    · calc
        (τ^2/(16*((m : ℝ)+1)^2*(1+Q)*(1+M)))⁻¹ =
            16*((m : ℝ)+1)^2*(1+Q)*(1+M)*(τ⁻¹)^2 := by
              rw [inv_div, div_eq_mul_inv, inv_pow]
        _ ≤ Real.exp 4*(Real.exp (P+1))^2*Real.exp (P+1)*Real.exp (P+1)*(Real.exp P)^2 := by
          gcongr
        _ = _ := by
          rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add,
            ← Real.exp_add, ← Real.exp_add]
          congr 1
          ring

theorem polynomialPerturbationScale_log_inverse_le {K M Q τ P : ℝ}
    (hK : 0 ≤ K) (hM : 0 ≤ M) (hQ : 0 ≤ Q) (hτ : 0 < τ) (hP : 0 ≤ P)
    (m : ℕ) (hm : (m : ℝ) ≤ Real.exp P)
    (hKP : K ≤ Real.exp P) (hMP : M ≤ Real.exp P) (hQP : Q ≤ Real.exp P)
    (hτP : τ⁻¹ ≤ Real.exp P) :
    Real.log (polynomialPerturbationScale K M Q τ m)⁻¹ ≤ 6*P+8 :=
  (Real.log_le_log (inv_pos.mpr (polynomialPerturbationScale_spec hK hM hQ hτ m).1)
    (polynomialPerturbationScale_inverse_le_exp hK hM hQ hτ hP m hm hKP hMP hQP hτP)).trans_eq
    (Real.log_exp _)

end Erdos3

end

section

namespace Erdos3

theorem polynomialPerturbationScale_unit_inverse_le_exp
    {K Q τ Klog Qlog Tlog D : ℝ}
    (hKlog : 0 ≤ Klog) (hQlog : 0 ≤ Qlog) (hTlog : 0 ≤ Tlog) (hD : 0 ≤ D)
    (O : ℕ) (hO : (O : ℝ) ≤ D)
    (hK : K ≤ Real.exp Klog) (hQ : Q ≤ Real.exp Qlog)
    (hτ : τ⁻¹ ≤ Real.exp Tlog) (hτ0 : 0 < τ) (hQ0 : 0 ≤ Q) (hK0 : 0 ≤ K) :
    (polynomialPerturbationScale K 1 Q τ O)⁻¹ ≤
      Real.exp (2 * Klog + 2 * Qlog + 2 * Tlog + 2 * D + 20) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have h4 : (4 : ℝ) ≤ Real.exp 2 := by
    calc
      _ = (2 : ℝ) ^ 2 := by norm_num
      _ ≤ (Real.exp 1) ^ 2 := pow_le_pow_left₀ (by norm_num) h2 _
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have h32 : (32 : ℝ) ≤ Real.exp 5 := by
    calc
      _ = (2 : ℝ) ^ 5 := by norm_num
      _ ≤ (Real.exp 1) ^ 5 := pow_le_pow_left₀ (by norm_num) h2 _
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hO1 : (O : ℝ) + 1 ≤ Real.exp D := by
    linarith [Real.add_one_le_exp D]
  have hK1 := one_add_le_exp_succ hKlog hK
  have hQ1 := one_add_le_exp_succ hQlog hQ
  unfold polynomialPerturbationScale
  apply inv_min_le_of_inv_le
  · simpa only [inv_one] using
      Real.one_le_exp_iff.mpr (by positivity :
        0 ≤ 2 * Klog + 2 * Qlog + 2 * Tlog + 2 * D + 20)
  · apply inv_min_le_of_inv_le
    · calc
        (1 / (2 * (1 + K) * (1 + 1 : ℝ)))⁻¹ = 4 * (1 + K) := by simp; ring
        _ ≤ Real.exp 2 * Real.exp (Klog + 1) := by gcongr
        _ = Real.exp (Klog + 3) := by rw [← Real.exp_add]; congr 1; ring
        _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
    · calc
        (τ ^ 2 / (16 * ((O : ℝ) + 1) ^ 2 * (1 + Q) * (1 + 1)))⁻¹ =
            32 * ((O : ℝ) + 1) ^ 2 * (1 + Q) * (τ⁻¹) ^ 2 := by
          rw [inv_div, div_eq_mul_inv, inv_pow]
          ring
        _ ≤ Real.exp 5 * (Real.exp D) ^ 2 * Real.exp (Qlog + 1) *
            (Real.exp Tlog) ^ 2 := by gcongr
        _ = Real.exp (2 * D + Qlog + 2 * Tlog + 6) := by
          rw [← Real.exp_nat_mul, ← Real.exp_nat_mul,
            ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          congr 1
          ring
        _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem polynomialPerturbationScale_unit_exp_lower
    {K Q τ Klog Qlog Tlog D : ℝ}
    (hK0 : 0 ≤ K) (hQ0 : 0 ≤ Q) (hτ0 : 0 < τ)
    (hKlog : 0 ≤ Klog) (hQlog : 0 ≤ Qlog) (hTlog : 0 ≤ Tlog) (hD : 0 ≤ D)
    (O : ℕ) (hO : (O : ℝ) ≤ D)
    (hK : K ≤ Real.exp Klog) (hQ : Q ≤ Real.exp Qlog)
    (hτ : τ⁻¹ ≤ Real.exp Tlog) :
    Real.exp (-(2 * Klog + 2 * Qlog + 2 * Tlog + 2 * D + 20)) ≤
      polynomialPerturbationScale K 1 Q τ O := by
  have hpos := (polynomialPerturbationScale_spec hK0 zero_le_one hQ0 hτ0 O).1
  have hinv := polynomialPerturbationScale_unit_inverse_le_exp
    hKlog hQlog hTlog hD O hO hK hQ hτ hτ0 hQ0 hK0
  have h := one_div_le_one_div_of_le (inv_pos.mpr hpos) hinv
  simpa only [one_div, inv_inv, ← Real.exp_neg] using h

end Erdos3

end

end OAI
