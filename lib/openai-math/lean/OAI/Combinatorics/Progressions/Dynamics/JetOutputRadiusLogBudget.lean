import OAI.Combinatorics.Progressions.Polynomial.BooleanPolynomialLogBudget

namespace OAI

section

namespace Erdos3

open scoped NNReal

theorem polynomialBoxLip_le_exp (n d : ℕ) (C : ℝ≥0) {p : ℝ} (hC : (C : ℝ) ≤ Real.exp p) :
    (polynomialBoxLip n d C : ℝ) ≤ Real.exp (3*(n : ℝ)*d+p) := by
  have h := (polynomialC2BoxBudget_dominates n d C.coe_nonneg).2.1
  have h' : (polynomialBoxLip n d C : ℝ) ≤ polynomialC2BoxBudget n d C := h
  exact h'.trans (polynomialC2BoxBudget_le_exp n d C.coe_nonneg hC)

theorem normalizedJetMass_le_exp (α : Type*) [Fintype α] (d : ℕ) :
    (normalizedJetMass α d : ℝ) ≤ Real.exp ((Fintype.card α : ℝ)*(d+1)) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    convert Real.add_one_le_exp (1 : ℝ) using 1
    norm_num
  have hbase := Real.add_one_le_exp (Fintype.card α : ℝ)
  change (2 : ℝ)^Fintype.card α * ((Fintype.card α : ℝ)+1)^d ≤ _
  calc
    _ ≤ (Real.exp 1)^Fintype.card α * (Real.exp (Fintype.card α : ℝ))^d :=
      mul_le_mul (pow_le_pow_left₀ (by norm_num) htwo _) (pow_le_pow_left₀ (by positivity) hbase _)
        (by positivity) (by positivity)
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring

theorem normalizedJetColumnLip_le_exp (α : Type*) [Fintype α] (n p d : ℕ) :
    (n : ℝ) * polynomialBoxLip p d (normalizedJetMass α d) ≤
      Real.exp (n + 3*(p : ℝ)*d + (Fintype.card α : ℝ)*(d+1)) := by
  have hn : (n : ℝ) ≤ Real.exp (n : ℝ) := (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _)
  calc
    _ ≤ Real.exp (n : ℝ) * Real.exp (3*(p : ℝ)*d + (Fintype.card α : ℝ)*(d+1)) :=
      mul_le_mul hn (polynomialBoxLip_le_exp p d _ (normalizedJetMass_le_exp α d))
        (NNReal.coe_nonneg _) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add, add_assoc]

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

def jetOutputRadiusLog (q n d : ℕ) (P : ℝ) : ℝ := 4*P+n+q+(d : ℝ)*q+2

theorem jetOutputRadiusLog_nonneg (q n d : ℕ) {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ jetOutputRadiusLog q n d P := by unfold jetOutputRadiusLog; positivity

theorem normalizedJetOutputRadius_le_exp {I J : Type*} [Fintype I] [Fintype J]
    (α N : Type*) [Fintype α] [Fintype N]
    (A : (I → ℝ) ≃L[ℝ] (I → ℝ)) (F : (J → ℝ) →L[ℝ] (I → ℝ))
    (degree : ℕ) (R S : ℝ≥0) {P : ℝ} (hP : 0 ≤ P)
    (hA : ‖A.toContinuousLinearMap‖ ≤ Real.exp P) (hF : ‖F‖ ≤ Real.exp P)
    (hR : (R : ℝ) ≤ Real.exp P) (hS : (S : ℝ) ≤ Real.exp P) :
    (normalizedJetOutputRadius α N A F degree R S : ℝ) ≤
      Real.exp (jetOutputRadiusLog (Fintype.card α) (Fintype.card N) degree P) := by
  have hAF := add_le_exp_add_one hP hP hA hF
  have hlinear : (‖A.toContinuousLinearMap‖+‖F‖)*(R : ℝ) ≤ Real.exp (3*P+1) := by
    calc
      _ ≤ Real.exp (P+P+1)*Real.exp P := by gcongr
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hmass : (normalizedJetMass α degree : ℝ) ≤
      Real.exp (Fintype.card α+(degree : ℝ)*Fintype.card α) := by
    have he : (Fintype.card α : ℝ)*(degree+1) = Fintype.card α+(degree : ℝ)*Fintype.card α := by ring
    simpa only [he] using normalizedJetMass_le_exp α degree
  have hn : (Fintype.card N : ℝ) ≤ Real.exp (Fintype.card N : ℝ) := by
    linarith [Real.add_one_le_exp (Fintype.card N : ℝ)]
  have htail : (Fintype.card N : ℝ)*(normalizedJetMass α degree : ℝ)*(S : ℝ) ≤
      Real.exp (Fintype.card N+Fintype.card α+(degree : ℝ)*Fintype.card α+P) := by
    calc
      _ ≤ Real.exp (Fintype.card N : ℝ)*Real.exp (Fintype.card α+(degree : ℝ)*Fintype.card α)*Real.exp P := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hs := add_le_exp_add_one (show 0 ≤ 3*P+1 by positivity)
    (show 0 ≤ (Fintype.card N : ℝ)+Fintype.card α+(degree : ℝ)*Fintype.card α+P by positivity) hlinear htail
  change (‖A.toContinuousLinearMap‖+‖F‖)*(R : ℝ)+
    (Fintype.card N : ℝ)*(normalizedJetMass α degree : ℝ)*(S : ℝ) ≤ _
  apply hs.trans_eq
  congr 1
  unfold jetOutputRadiusLog
  ring

end Erdos3

end

end OAI
