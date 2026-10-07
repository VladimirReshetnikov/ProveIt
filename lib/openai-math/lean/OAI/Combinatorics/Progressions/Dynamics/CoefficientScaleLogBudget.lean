import OAI.Combinatorics.Progressions.Estimates.JointTupleTolerance

namespace OAI

section

namespace Erdos3

theorem coefficientRowAccuracy_inverse_le_exp (n : ℕ) {η e : ℝ}
    (hη : 0 < η) (hi : η⁻¹ ≤ Real.exp e) :
    (coefficientRowAccuracy n η)⁻¹ ≤ Real.exp (n+e+4) := by
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hn := Real.add_one_le_exp (n : ℝ)
  calc
    _ = 4*((n : ℝ)+1)*η⁻¹ := by simp only [coefficientRowAccuracy, inv_div]; ring
    _ ≤ Real.exp 4*Real.exp n*Real.exp e := by gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

noncomputable def coefficientToleranceLog (i j d : ℕ) (b t e l z : ℝ) : ℝ :=
  z+coefficientLogAllowance i j (affineCoefficientCommonBudget j j b t)+
    (i : ℝ)*(j+2*b+3)+e+1+(d*(i+1) : ℕ)*l

theorem coefficientToleranceLog_nonneg (i j d : ℕ) {b t e l z : ℝ}
    (hb : 0 ≤ b) (ht : 0 ≤ t) (he : 0 ≤ e) (hl : 0 ≤ l) (hz : 0 ≤ z) :
    0 ≤ coefficientToleranceLog i j d b t e l z := by
  have hc := affineCoefficientCommonBudget_nonneg j j hb ht
  unfold coefficientToleranceLog coefficientLogAllowance
  positivity

theorem coefficientToleranceScale_le_exp {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (d : ℕ) {b t e l z ε L mesh : ℝ}
    (hb : 0 ≤ b) (ht : 0 ≤ t) (he : 0 ≤ e) (hl : 0 ≤ l) (hz : 0 ≤ z)
    (hε : 0 < ε) (hL0 : 0 ≤ L)
    (hεe : ε⁻¹ ≤ Real.exp e) (hLl : L ≤ Real.exp l) (hmz : mesh⁻¹ ≤ Real.exp z) :
    coefficientToleranceScale s b t ε L mesh d ≤
      Real.exp (coefficientToleranceLog (Fintype.card I) (Fintype.card J) d b t e l z) := by
  have hcard : (Fintype.card (UnselectedColumn s) : ℝ) ≤ Fintype.card J := by
    exact_mod_cast Fintype.card_subtype_le (fun j : J => j ∉ Set.range s)
  have hB0 := affineCoefficientCommonBudget_nonneg (Fintype.card J) (Fintype.card (UnselectedColumn s)) hb ht
  have hB : affineCoefficientCommonBudget (Fintype.card J) (Fintype.card (UnselectedColumn s)) b t ≤
      affineCoefficientCommonBudget (Fintype.card J) (Fintype.card J) b t := by
    unfold affineCoefficientCommonBudget
    gcongr
  have hE : coefficientLogAllowance (Fintype.card I) (Fintype.card (UnselectedColumn s))
      (affineCoefficientCommonBudget (Fintype.card J) (Fintype.card (UnselectedColumn s)) b t) ≤
      coefficientLogAllowance (Fintype.card I) (Fintype.card J)
        (affineCoefficientCommonBudget (Fintype.card J) (Fintype.card J) b t) := by
    unfold coefficientLogAllowance
    gcongr
  let E := coefficientLogAllowance (Fintype.card I) (Fintype.card J)
    (affineCoefficientCommonBudget (Fintype.card J) (Fintype.card J) b t) +
    (Fintype.card I : ℝ)*(Fintype.card J+2*b+3)
  have hE0 : 0 ≤ E := by
    have hC := affineCoefficientCommonBudget_nonneg (Fintype.card J) (Fintype.card J) hb ht
    unfold E coefficientLogAllowance
    positivity
  have hbound : Real.exp
      (coefficientLogAllowance (Fintype.card I) (Fintype.card (UnselectedColumn s))
        (affineCoefficientCommonBudget (Fintype.card J) (Fintype.card (UnselectedColumn s)) b t) +
        (Fintype.card I : ℝ)*(Fintype.card J+2*b+3)) * (1+ε⁻¹) * L^(d*(Fintype.card I+1)) ≤
      Real.exp (E+e+1+(d*(Fintype.card I+1) : ℕ)*l) := by
    calc
      _ ≤ Real.exp E*Real.exp (e+1)*(Real.exp l)^(d*(Fintype.card I+1)) := by
        gcongr
        · exact add_le_add hE le_rfl
        · exact one_add_le_exp_succ he hεe
      _ = _ := by rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have heq : coefficientToleranceLog (Fintype.card I) (Fintype.card J) d b t e l z =
      z+E+e+1+(d*(Fintype.card I+1) : ℕ)*l := by
    unfold coefficientToleranceLog
    dsimp only [E]
    ring
  unfold coefficientToleranceScale
  refine max_le (Real.one_le_exp_iff.mpr (coefficientToleranceLog_nonneg _ _ _ hb ht he hl hz)) (max_le ?_ ?_)
  · apply hmz.trans
    apply Real.exp_le_exp.mpr
    rw [heq]
    have hd : 0 ≤ (d*(Fintype.card I+1) : ℕ)*l := by positivity
    linarith
  · apply hbound.trans
    apply Real.exp_le_exp.mpr
    rw [heq]
    linarith

end Erdos3

end

end OAI
