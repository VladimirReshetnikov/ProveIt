import GowersSzemeredi.Proofs13RecurrenceParameterBudgets

/-! Double-exponential envelopes for the actual uniform integer budgets. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open scoped BigOperators

theorem section13IntegerBudgetThreshold_le_double_exp {delta : Real}
    (hδ : 0 < delta) (hδone : delta ≤ 1) {q : Nat} (hq : (q : Real) ≤ section13Q delta) :
    section13IntegerBudgetThreshold delta q ≤ Real.exp (Real.exp (18 * section13Q delta)) := by
  let Q := section13Q delta
  let d0 := section13ThetaOne (section10Lambda (delta ^ 32 / 16)) / (64 * Real.pi)
  let d := min 1 (d0 / 2)
  let c := section13Zeta delta / 2
  let z := section10Zeta (delta ^ 32 / 16)
  let e := (1 : Real) / (2 : Real) ^ (13 * Q)
  have hQ : 512 ≤ Q := section13Q_ge_512 hδ hδone
  have hQ0 : 0 ≤ Q := le_trans (by norm_num) hQ
  have hQe := Real.add_one_le_exp Q
  have key {C D e' b r : Real} (hD : 0 < D) (he' : 0 ≤ e') (hb : 0 ≤ b) (hs : 1 + b + r ≤ 18)
      (hC : C ≤ Real.exp Q) (hDi : D⁻¹ ≤ Real.exp (b * Q)) (hEi : e'⁻¹ ≤ Real.exp (r * Q)) :
      positivePowerThreshold C D e' ≤ Real.exp (Real.exp (18 * Q)) :=
    (positivePowerThreshold_le_double_exp hD he' hQ0 zero_le_one hb (by rwa [one_mul]) hDi
      hEi).trans (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hs hQ0)))
  have hζ : 0 < section13Zeta delta := by unfold section13Zeta; positivity
  have hd0 : 0 < d0 := by dsimp only [d0, section13ThetaOne, section10Lambda]; positivity
  have hd : 0 < d := lt_min zero_lt_one (half_pos hd0)
  have hz : 0 < z := section10Zeta_pos (by positivity)
  have he : 0 < e := by positivity
  have hcI : c⁻¹ ≤ Real.exp (2 * Q) := by
    have hc : c⁻¹ = 2 * (section13Zeta delta)⁻¹ := by simp only [c]; rw [inv_div, div_eq_mul_inv]
    rw [two_mul, Real.exp_add, hc]
    exact mul_le_mul (by linarith) ((section13Zeta_inv_le_spectral_exp hδ hδone).trans
      (two_rpow_le_exp hQ0)) (inv_nonneg.mpr hζ.le) (Real.exp_pos _).le
  have hdI : d⁻¹ ≤ Real.exp (3 * Q) :=
    (section13_initial_min_coefficient_inv_le_Q_cube hδ hδone).trans (real_pow_le_exp_nat_mul hQ0 3)
  have hzdI : (z * d)⁻¹ ≤ Real.exp (4 * Q) := by
    rw [mul_inv_rev, show 4 * Q = 3 * Q + Q by ring, Real.exp_add]
    exact mul_le_mul hdI ((section10Zeta_inv_le_spectral_exp hδ hδone).trans
      (two_rpow_le_exp hQ0)) (inv_nonneg.mpr hz.le) (Real.exp_pos _).le
  have heI : e⁻¹ ≤ Real.exp (13 * Q) := by
    simp only [e, one_div, inv_inv]
    exact two_rpow_le_exp (by positivity)
  exact max_le (max_le (key (half_pos hζ) he.le zero_le_two (by norm_num) (by linarith) hcI heI)
    (max_le (key hd he.le (by norm_num) (by norm_num) (by linarith) hdI heI)
      (key (mul_pos hz hd) he.le (by norm_num) (by norm_num) (by linarith) hzdI heI)))
    (key hd0 (by positivity) zero_le_two (by norm_num) (by linarith)
      ((section13_initial_coefficient_inv_le_Q_sq hδ hδone).trans (real_pow_le_exp_nat_mul hQ0 2))
      ((section13_initial_exponent_inv_le_Q_four hδ hδone hq).trans
        (real_pow_le_exp_nat_mul hQ0 4)))

/-- Real upper bounds pass through a finite supremum of natural counts. -/
theorem nat_cast_finset_sup_le {ι : Type*} (s : Finset ι) (f : ι → Nat) {W : Real}
    (hW : 0 ≤ W) (hf : ∀ i ∈ s, (f i : Real) ≤ W) : ((s.sup f : Nat) : Real) ≤ W := by
  have h : s.sup f ≤ Nat.floor W := Finset.sup_le (fun i hi => Nat.le_floor (hf i hi))
  exact (Nat.cast_le.mpr h).trans (Nat.floor_le hW)

/-- The maximum over all permitted frequencies preserves the numerical
bound, including q=0 and the natural ceiling at each term. -/
theorem section13DensityIntegerThreshold_le_double_exp {delta : Real}
    (hδ : 0 < delta) (hδone : delta ≤ 1) :
    (section13DensityIntegerThreshold delta : Real) ≤ Real.exp (Real.exp (19 * section13Q delta)) := by
  have hQ := section13Q_ge_512 hδ hδone
  have hb : 0 ≤ section13QBound (section10Lambda (delta ^ 32 / 16)) := by
    unfold section13QBound section10Lambda
    positivity
  unfold section13DensityIntegerThreshold
  refine nat_cast_finset_sup_le _ _ (Real.exp_pos _).le fun q hq ↦ ?_
  have hqQ : (q : Real) ≤ section13Q delta :=
    ((Nat.cast_le.mpr (Nat.lt_succ_iff.mp (Finset.mem_range.mp hq))).trans (Nat.floor_le hb)).trans
      ((section13_qBound_le_half_Q hδ hδone).trans (by linarith only [hQ]))
  have ht0 : 0 ≤ section13IntegerBudgetThreshold delta q :=
    zero_le_one.trans ((positivePowerThreshold_one_le _ _ _).trans
      ((le_max_left _ _).trans (le_max_left _ _)))
  exact (nat_ceil_le_double_exp_add_one (by linarith only [hQ]) ht0
    (section13IntegerBudgetThreshold_le_double_exp hδ hδone hqQ)).trans
    (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by linarith only [hQ])))

end LeanProofs.GowersSzemeredi
