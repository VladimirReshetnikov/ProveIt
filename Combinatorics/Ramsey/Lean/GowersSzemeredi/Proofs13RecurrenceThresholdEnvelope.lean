import GowersSzemeredi.Proofs13IntegerThresholdEnvelope
import GowersSzemeredi.Proofs13RecurrenceRange

/-! Numerical envelopes for the actual finite recurrence threshold. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem nat_two_tower_cast (n : Nat) :
    (((2 : Nat) ^ ((2 : Nat) ^ n) : Nat) : Real) =
      (2 : Real) ^ ((2 : Real) ^ (n : Real)) := by
  rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast]
  rw [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_natCast]

/-- The simultaneous quadratic recurrence threshold is double exponential
in any spectral upper bound Q at least 512, uniformly including q=0. -/
theorem simultaneous_quadratic_threshold_le_double_exp {Q : Real} {q : Nat}
    (hQ : 512 ≤ Q) (hq : (q : Real) ≤ Q) :
    (simultaneousPolynomialThreshold 2 q : Real) ≤ Real.exp (Real.exp (12 * Q)) := by
  let n := 40 * (2 : Nat) ^ 3 + 2 + 11 * (q - 1)
  have hn : n ≤ 322 + 11 * q := by dsimp [n]; omega
  have hnr : (n : Real) ≤ 322 + 11 * (q : Real) := by exact_mod_cast hn
  have hnQ : (n : Real) ≤ 12 * Q := by linarith only [hnr, hq, hQ]
  have hK : polynomialPartitionConstant 2 ≤ (2 : Nat) ^ 11 := by norm_num [polynomialPartitionConstant]
  have hb := simultaneous_partition_threshold_le_tower 2 q 11 hK
  have hbr : (simultaneousPolynomialThreshold 2 q : Real) ≤ (((2 : Nat) ^ ((2 : Nat) ^ n) : Nat) : Real) :=
    Nat.cast_le.mpr hb
  rw [nat_two_tower_cast] at hbr
  calc
    _ ≤ (2 : Real) ^ ((2 : Real) ^ (n : Real)) := hbr
    _ ≤ Real.exp ((2 : Real) ^ (n : Real)) := two_rpow_le_exp (Real.rpow_nonneg (by norm_num) _)
    _ ≤ Real.exp (Real.exp (n : Real)) := Real.exp_le_exp.mpr (two_rpow_le_exp (Nat.cast_nonneg n))
    _ ≤ _ := Real.exp_le_exp.mpr (Real.exp_le_exp.mpr hnQ)

theorem section13RecurrenceLengthThreshold_le_double_exp {delta : Real}
    (hδ : 0 < delta) (hδone : delta ≤ 1) {q : Nat} (hq : (q : Real) ≤ section13Q delta) :
    section13RecurrenceLengthThreshold delta q ≤ Real.exp (Real.exp (14 * section13Q delta)) := by
  let Q := section13Q delta
  have hQ : 512 ≤ Q := section13Q_ge_512 hδ hδone
  have hQexp : Q ≤ Real.exp Q := by linarith only [Real.add_one_le_exp Q]
  have heI : ((1 : Real) / (2 : Real) ^ (12 * q))⁻¹ ≤ Real.exp (12 * Q) := by
    rw [one_div, inv_inv, ← Real.rpow_natCast]
    exact (two_rpow_le_exp (Nat.cast_nonneg _)).trans
      (Real.exp_le_exp.mpr (by push_cast; linarith only [hq]))
  have hD : (delta ^ (32 : Nat))⁻¹ ≤ Real.exp (1 * Q) := by
    have hm := section13_monomial_le_Q hδ hδone (a := 0) (b := 32) (by norm_num) (by norm_num)
    simp only [pow_zero, one_mul, inv_pow] at hm
    simpa only [one_mul] using hm.trans hQexp
  -- both power thresholds have `C, D⁻¹ ≤ e ^ Q` and `e⁻¹ ≤ e ^ (12 Q)`
  have hleft := positivePowerThreshold_le_double_exp (C := 8) zero_lt_one (by positivity)
    (by linarith) zero_le_one zero_le_one (by rw [one_mul]; linarith)
    (by rw [inv_one]; linarith [Real.add_one_le_exp (1 * Q)]) heI
  have hright := positivePowerThreshold_le_double_exp (C := 160 + 2 * delta ^ 32) (pow_pos hδ 32)
    (by positivity) (by linarith) zero_le_one zero_le_one
    (by rw [one_mul]; linarith [pow_le_one₀ (n := 32) hδ.le hδone]) hD heI
  norm_num only [show (1 + 1 + 12 : Real) = 14 by norm_num] at hleft hright
  unfold section13RecurrenceLengthThreshold
  rw [Nat.cast_add, Nat.cast_one]
  refine max_le ?_ (max_le hleft hright)
  exact ((add_le_add (simultaneous_quadratic_threshold_le_double_exp hQ hq) le_rfl).trans
    (double_exp_add_one_le (by positivity))).trans
      (Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by linarith only [hQ])))

theorem section13InitialRecurrenceThreshold_le_double_exp {delta : Real}
    (hδ : 0 < delta) (hδone : delta ≤ 1) {q : Nat} (hq : (q : Real) ≤ section13Q delta) :
    section13InitialRecurrenceThreshold delta q ≤ Real.exp (Real.exp (21 * section13Q delta)) := by
  let Q := section13Q delta
  let d := section13ThetaOne (section10Lambda (delta ^ 32 / 16)) / (64 * Real.pi)
  let u := section13ThetaOne (section10Lambda (delta ^ 32 / 16)) ^ 2 / (16 * (q : Real))
  have hQ : 512 ≤ Q := section13Q_ge_512 hδ hδone
  have hQ0 : 0 ≤ Q := by linarith only [hQ]
  have hd : 0 < d := by dsimp [d, section13ThetaOne, section10Lambda]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hdI : d⁻¹ ≤ Real.exp (2 * Q) :=
    (section13_initial_coefficient_inv_le_Q_sq hδ hδone).trans (real_pow_le_exp_nat_mul hQ0 2)
  have huI : u⁻¹ ≤ Real.exp (4 * Q) :=
    (section13_initial_exponent_inv_le_Q_four hδ hδone hq).trans (real_pow_le_exp_nat_mul hQ0 4)
  -- two rounding units cost `14 Q ↦ 14 Q + 2 ≤ 16 Q` inside the double exponential
  have hC : section13RecurrenceLengthThreshold delta q + 2 ≤ Real.exp (Real.exp (16 * Q)) := by
    have h1 := (add_le_add (section13RecurrenceLengthThreshold_le_double_exp hδ hδone hq)
      le_rfl).trans (double_exp_add_one_le (by positivity : 0 ≤ 14 * Q))
    have h2 := (add_le_add h1 le_rfl).trans (double_exp_add_one_le (by positivity : 0 ≤ 14 * Q + 1))
    linarith [Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by linarith : 14 * Q + 1 + 1 ≤ 16 * Q))]
  refine (positivePowerThreshold_le_exp hd hu (by positivity) hC hdI huI).trans
    (Real.exp_le_exp.mpr ?_)
  -- `(e ^ (16 Q) + 2 Q) e ^ (4 Q) ≤ e ^ Q e ^ (16 Q) e ^ (4 Q) = e ^ (21 Q)`
  have htwo : (2 : Real) ≤ Real.exp Q := by linarith only [Real.add_one_le_exp Q, hQ]
  calc
    _ ≤ (Real.exp Q * Real.exp (16 * Q)) * Real.exp (4 * Q) := by
      gcongr
      linarith only [Real.add_one_le_exp (16 * Q), hQ,
        mul_le_mul_of_nonneg_right htwo (Real.exp_pos (16 * Q)).le]
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

theorem section13DensityRecurrenceThreshold_le_double_exp {delta : Real}
    (hδ : 0 < delta) (hδone : delta ≤ 1) :
    (section13DensityRecurrenceThreshold delta : Real) ≤ Real.exp (Real.exp (22 * section13Q delta)) := by
  let Q := section13Q delta
  have hQ : 512 ≤ Q := section13Q_ge_512 hδ hδone
  unfold section13DensityRecurrenceThreshold
  rw [Nat.cast_max]
  refine max_le ?_ (nat_cast_finset_sup_le _ _ (Real.exp_pos _).le fun q hq => ?_)
  · norm_num only [Nat.cast_ofNat]
    linarith only [Real.add_one_le_exp (22 * Q), Real.add_one_le_exp (Real.exp (22 * Q)), hQ]
  -- every admissible `q` is at most `Q`, and each ceiling costs one unit
  have hqQ : (q : Real) ≤ Q := by
    have h := ((Nat.cast_le.mpr (Nat.lt_add_one_iff.mp (Finset.mem_range.mp hq))).trans
      (Nat.floor_le (by unfold section13QBound section10Lambda; positivity))).trans
      (section13_qBound_le_half_Q hδ hδone)
    linarith only [h, hQ]
  have ht0 : 0 ≤ section13InitialRecurrenceThreshold delta q :=
    zero_le_one.trans (positivePowerThreshold_one_le _ _ _)
  refine (nat_ceil_le_double_exp_add_one (by positivity : 0 ≤ 21 * Q) ht0
    (section13InitialRecurrenceThreshold_le_double_exp hδ hδone hqQ)).trans ?_
  exact Real.exp_le_exp.mpr (Real.exp_le_exp.mpr (by linarith only [hQ]))

end LeanProofs.GowersSzemeredi
