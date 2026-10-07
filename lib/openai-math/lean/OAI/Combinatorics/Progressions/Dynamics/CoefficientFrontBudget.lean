import OAI.Combinatorics.Progressions.Lattices.ResidueCoefficientFamily

namespace OAI

section

namespace Erdos3

noncomputable def coefficientFrontLog (i j : ℕ) (b t e : ℝ) : ℝ :=
  coefficientLogAllowance i j (affineCoefficientCommonBudget j j b t) + e + 1

theorem coefficientFrontLog_nonneg (i j : ℕ) {b t e : ℝ}
    (hb : 0 ≤ b) (ht : 0 ≤ t) (he : 0 ≤ e) : 0 ≤ coefficientFrontLog i j b t e := by
  have hB := affineCoefficientCommonBudget_nonneg j j hb ht
  unfold coefficientFrontLog coefficientLogAllowance
  positivity

theorem coefficientReplacementScale_front_bound {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (h : ℕ) {b t e ε L : ℝ}
    (hb : 0 ≤ b) (ht : 0 ≤ t) (he : 0 ≤ e) (hε : 0 < ε) (hL : 0 ≤ L)
    (hεe : ε⁻¹ ≤ Real.exp e) :
    coefficientReplacementScale s b t ε L h ≤
      Real.exp (coefficientFrontLog (Fintype.card I) (Fintype.card J) b t e) *
        L^(h*(Fintype.card I+1)) := by
  have hcard : (Fintype.card (UnselectedColumn s) : ℝ) ≤ Fintype.card J := by
    exact_mod_cast Fintype.card_subtype_le (fun j : J => j ∉ Set.range s)
  have hB0 := affineCoefficientCommonBudget_nonneg
    (Fintype.card J) (Fintype.card (UnselectedColumn s)) hb ht
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
  unfold coefficientReplacementScale coefficientFrontLog
  rw [Real.exp_add, Real.exp_add]
  calc
    _ ≤ Real.exp (coefficientLogAllowance (Fintype.card I) (Fintype.card J)
        (affineCoefficientCommonBudget (Fintype.card J) (Fintype.card J) b t)) *
          Real.exp (e+1) * L^(h*(Fintype.card I+1)) := by
      gcongr
      exact one_add_le_exp_succ he hεe
    _ = _ := by rw [Real.exp_add]; ring

theorem coefficientReplacementScale_le_power {I J : Type*} [Fintype I] [Fintype J]
    (s : I ↪ J) (h : ℕ) {b t e ε L : ℝ}
    (hb : 0 ≤ b) (ht : 0 ≤ t) (he : 0 ≤ e) (hε : 0 < ε) (hL : 0 ≤ L)
    (hεe : ε⁻¹ ≤ Real.exp e)
    (hfront : Real.exp (coefficientFrontLog (Fintype.card I) (Fintype.card J) b t e) ≤ L) :
    coefficientReplacementScale s b t ε L h ≤ L^(h*(Fintype.card I+1)+1) := by
  apply (coefficientReplacementScale_front_bound s h hb ht he hε hL hεe).trans
  calc
    _ ≤ L * L^(h*(Fintype.card I+1)) := mul_le_mul_of_nonneg_right hfront (pow_nonneg hL _)
    _ = _ := by rw [pow_succ]; ring

end Erdos3

end

end OAI
