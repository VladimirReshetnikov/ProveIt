import GowersSzemeredi.Proofs13RecurrenceParameterBudgets
import GowersSzemeredi.Proofs13ExplicitDensityBudgets

/-! Double-exponential envelopes for the actual uniform integer budgets. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open scoped BigOperators

theorem section13IntegerBudgetThreshold_le_double_exp {delta : Real}
    (hδ : 0 < delta) (hδone : delta ≤ 1) {q : Nat} (hq : (q : Real) ≤ section13Q delta) :
    section13IntegerBudgetThreshold delta q ≤ Real.exp (Real.exp (18 * section13Q delta)) := by
  let Q := section13Q delta
  let theta := section10Lambda (delta ^ 32 / 16)
  let d0 := section13ThetaOne theta / (64 * Real.pi)
  let d := min 1 (d0 / 2)
  let c := section13Zeta delta / 2
  let z := section10Zeta (delta ^ 32 / 16)
  let e := (1 : Real) / (2 : Real) ^ (13 * Q)
  let u := section13ThetaOne theta ^ 2 / (16 * (q : Real))
  have hQ := section13Q_ge_512 hδ hδone
  have hQ0 : 0 ≤ Q := by dsimp [Q]; linarith only [hQ]
  have hQ4 : 4 ≤ Q := by dsimp [Q]; linarith only [hQ]
  have hθ : 0 < theta := by dsimp [theta, section10Lambda]; positivity
  have hd0 : 0 < d0 := by dsimp [d0, section13ThetaOne]; positivity
  have hd : 0 < d := lt_min zero_lt_one (div_pos hd0 (by norm_num))
  have hc : 0 < c := by dsimp [c, section13Zeta]; positivity
  have hz : 0 < z := section10Zeta_pos (by positivity)
  have he : 0 < e := by dsimp [e]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have h4 : (4 : Real) ≤ Real.exp Q := (by norm_num : (4 : Real) ≤ 8).trans (eight_le_exp_of_four_le hQ4)
  have h1 : (1 : Real) ≤ Real.exp (1 * Q) := by rw [one_mul]; exact Real.one_le_exp_iff.mpr hQ0
  have hcI : c⁻¹ ≤ Real.exp (2 * Q) := by
    have hh := (section13Zeta_inv_le_spectral_exp hδ hδone).trans (two_rpow_le_exp hQ0)
    rw [show c⁻¹ = 2 * (section13Zeta delta)⁻¹ by dsimp [c]; rw [inv_div, div_eq_mul_inv]]
    have hm := mul_le_mul (show (2 : Real) ≤ Real.exp Q by linarith only [h4]) hh
      (by unfold section13Zeta; positivity) (Real.exp_pos _).le
    change 2 * (section13Zeta delta)⁻¹ ≤ Real.exp Q * Real.exp Q at hm
    simpa only [← Real.exp_add, show Q + Q = 2 * Q by ring] using hm
  have hdI : d⁻¹ ≤ Real.exp (3 * Q) :=
    (section13_initial_min_coefficient_inv_le_Q_cube hδ hδone).trans (real_pow_le_exp_nat_mul hQ0 3)
  have hzI : z⁻¹ ≤ Real.exp Q :=
    (section10Zeta_inv_le_spectral_exp hδ hδone).trans (two_rpow_le_exp hQ0)
  have hzdI : (z * d)⁻¹ ≤ Real.exp (4 * Q) := by
    rw [mul_inv_rev]
    have hm := mul_le_mul hdI hzI (inv_nonneg.mpr hz.le) (Real.exp_pos _).le
    simpa only [← Real.exp_add, show 3 * Q + Q = 4 * Q by ring] using hm
  have hd0I : d0⁻¹ ≤ Real.exp (2 * Q) :=
    (section13_initial_coefficient_inv_le_Q_sq hδ hδone).trans (real_pow_le_exp_nat_mul hQ0 2)
  have heI : e⁻¹ ≤ Real.exp (13 * Q) := by
    simp only [e, one_div, inv_inv]
    exact two_rpow_le_exp (by positivity)
  have huI : u⁻¹ ≤ Real.exp (4 * Q) :=
    (section13_initial_exponent_inv_le_Q_four hδ hδone hq).trans (real_pow_le_exp_nat_mul hQ0 4)
  have hleft := positivePowerThreshold_le_double_exp (C := 1) hc he.le hQ0
    (by norm_num : (0 : Real) ≤ 1) (by norm_num : (0 : Real) ≤ 2) h1 hcI heI
  have hmid := positivePowerThreshold_le_double_exp (C := 4) hd he.le hQ0
    (by norm_num : (0 : Real) ≤ 1) (by norm_num : (0 : Real) ≤ 3)
    (by simpa only [one_mul] using h4) hdI heI
  have hright := positivePowerThreshold_le_double_exp (C := 1) (mul_pos hz hd) he.le hQ0
    (by norm_num : (0 : Real) ≤ 1) (by norm_num : (0 : Real) ≤ 4) h1 hzdI heI
  have houter := positivePowerThreshold_le_double_exp (C := 4) hd0 hu hQ0
    (by norm_num : (0 : Real) ≤ 1) (by norm_num : (0 : Real) ≤ 2)
    (by simpa only [one_mul] using h4) hd0I huI
  norm_num only [show (1 + 2 + 13 : Real) = 16 by norm_num] at hleft
  norm_num only [show (1 + 3 + 13 : Real) = 17 by norm_num] at hmid
  norm_num only [show (1 + 4 + 13 : Real) = 18 by norm_num] at hright
  norm_num only [show (1 + 2 + 4 : Real) = 7 by norm_num] at houter
  change max (max (positivePowerThreshold 1 c e)
    (max (positivePowerThreshold 4 d e) (positivePowerThreshold 1 (z * d) e)))
    (positivePowerThreshold 4 d0 u) ≤ _
  refine max_le (max_le (hleft.trans ?_) (max_le (hmid.trans ?_) hright)) (houter.trans ?_)
  all_goals exact Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by nlinarith only [hQ0]))

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
  let Q := section13Q delta
  have hQ := section13Q_ge_512 hδ hδone
  have hQ0 : 0 ≤ Q := by dsimp [Q]; linarith only [hQ]
  have hb : 0 ≤ section13QBound (section10Lambda (delta ^ 32 / 16)) := by
    unfold section13QBound section10Lambda
    positivity
  unfold section13DensityIntegerThreshold
  apply nat_cast_finset_sup_le _ _ (Real.exp_pos _).le
  intro q hq
  have hqN : q ≤ Nat.floor (section13QBound (section10Lambda (delta ^ 32 / 16))) := by
    simp only [Finset.mem_range] at hq
    omega
  have hqQ : (q : Real) ≤ Q := by
    have h := (Nat.cast_le.mpr hqN).trans (Nat.floor_le hb)
    have h' := h.trans (section13_qBound_le_half_Q hδ hδone)
    dsimp [Q]
    linarith only [h', hQ]
  have ht := section13IntegerBudgetThreshold_le_double_exp hδ hδone hqQ
  have ht0 : 0 ≤ section13IntegerBudgetThreshold delta q :=
    zero_le_one.trans ((positivePowerThreshold_one_le _ _ _).trans
      ((le_max_left _ _).trans (le_max_left _ _)))
  have hc := nat_ceil_le_double_exp_add_one (by positivity : 0 ≤ 18 * Q) ht0 ht
  apply hc.trans
  exact Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by dsimp [Q]; linarith only [hQ]))

end LeanProofs.GowersSzemeredi
