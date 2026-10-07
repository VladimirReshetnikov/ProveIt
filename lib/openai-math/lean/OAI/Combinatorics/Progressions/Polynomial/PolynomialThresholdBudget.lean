import OAI.Combinatorics.Progressions.Estimates.ResidualErrorAllocation
import OAI.Combinatorics.Progressions.Polynomial.PolynomialSublevelThresholdBudget

namespace OAI

section

namespace Erdos3

theorem polynomialSublevelThreshold_inverse_le_exp (n m : ℕ) {C scale η Pc Ps Pe : ℝ}
    (hC : 0 ≤ C) (hs : 0 ≤ scale) (hη : 0 < η)
    (hPc : 0 ≤ Pc) (hPs : 0 ≤ Ps) (hPe : 0 ≤ Pe)
    (hCb : C ≤ Real.exp Pc) (hsb : scale ≤ Real.exp Ps) (hηb : η⁻¹ ≤ Real.exp Pe) :
    (polynomialSublevelThreshold n m C scale η)⁻¹ ≤
      Real.exp (Ps+2+(n : ℝ)*(Pc+m+Pe+2)) := by
  have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hm : (m : ℝ)+1 ≤ Real.exp m := Real.add_one_le_exp _
  have hb : 2*C*((m : ℝ)+1)/η ≤ Real.exp (Pc+m+Pe+1) := by
    rw [div_eq_mul_inv]
    calc
      _ ≤ Real.exp 1*Real.exp Pc*Real.exp m*Real.exp Pe := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hbase : 1+2*C*((m : ℝ)+1)/η ≤ Real.exp (Pc+m+Pe+2) := by
    have he : Pc+m+Pe+1+1 = Pc+m+Pe+2 := by ring
    simpa only [he] using one_add_le_exp_succ (by positivity : 0 ≤ Pc+m+Pe+1) hb
  rw [polynomialSublevelThreshold, inv_inv]
  calc
    _ ≤ Real.exp 1*Real.exp (Ps+1)*(Real.exp (Pc+m+Pe+2))^n := by
      gcongr
      exact one_add_le_exp_succ hPs hsb
    _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; congr 1; ring

end Erdos3

end

end OAI
