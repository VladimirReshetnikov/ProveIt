import GowersSzemeredi.Proofs16ProductAssembly

/-! # The actual parameter range and width identity of Lemma 16.6 -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The density and spectrum cutoff lie in their required positive ranges. -/
theorem section16_theta_delta_bounds {theta gamma : Real} (k : Nat)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1) :
    0 < section16ThetaOne theta gamma k ∧ section16ThetaOne theta gamma k ≤ 1 ∧
      0 < section16Delta (section16ThetaOne theta gamma k) ∧
      section16Delta (section16ThetaOne theta gamma k) ≤ 1 := by
  obtain ⟨hpos, hbound⟩ := section16_density_parameter_bounds k ht ht1 hg hg1
  have htpos : 0 < section16ThetaOne theta gamma k := by linarith
  have htbound : section16ThetaOne theta gamma k ≤ 1 := by linarith
  have hpow : (section16ThetaOne theta gamma k / 4) ^ ((11 : Real) / 2) ≤ 1 :=
    Real.rpow_le_one hpos.le (by linarith) (by norm_num)
  have hcoef : (2 : Real) ^ (-(37 : Real)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  refine ⟨htpos, htbound, ?_, ?_⟩
  · unfold section16Delta
    positivity
  · unfold section16Delta
    exact mul_le_one₀ hcoef (by positivity) hpow

/-- The iteration count is at least one for positive density parameters. -/
theorem section16T_one_le {delta theta1 : Real} (k : Nat)
    (hd : 0 < delta) (hd1 : delta ≤ 1) (ht : 0 < theta1) (ht1 : theta1 ≤ 1) :
    1 ≤ section16T delta theta1 k := by
  have hdelta : 1 ≤ delta ^ (-(2 : Int)) := by
    rw [zpow_neg, zpow_ofNat]
    simpa using (inv_le_inv₀ (by norm_num : (0 : Real) < 1)
      (by positivity : 0 < delta ^ 2)).mpr (by nlinarith : delta ^ 2 ≤ 1)
  have hprod : 0 < theta1 / 8 * delta := by positivity
  have hprod1 : theta1 / 8 * delta ≤ 2 := by nlinarith
  have hbase : (1 : Real) ≤ 2 / (theta1 / 8 * delta) := (le_div_iff₀ hprod).mpr (by linarith)
  have hS : 1 ≤ multipleS (theta1 / 8) delta k := one_le_pow₀ hbase
  unfold section16T
  nlinarith

/-- The multiple-linearity exponent used by Lemma 16.6 lies in (0,1]. -/
theorem section16_lemma6_exponent_bounds {theta gamma sigma : Real} (k : Nat)
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hs : 0 < sigma) (hs1 : sigma ≤ 1) :
    let delta := section16Delta (section16ThetaOne theta gamma k)
    let t := section16T delta (section16ThetaOne theta gamma k) k
    0 < (multipleC (t⁻¹ * sigma) delta k) ^ t ∧
      (multipleC (t⁻¹ * sigma) delta k) ^ t ≤ 1 := by
  obtain ⟨hth, hth1, hd, hd1⟩ := section16_theta_delta_bounds k ht ht1 hg hg1
  let delta := section16Delta (section16ThetaOne theta gamma k)
  let t := section16T delta (section16ThetaOne theta gamma k) k
  have htbound : 1 ≤ t := section16T_one_le k hd hd1 hth hth1
  have htpos : 0 < t := by linarith
  have hinv : t⁻¹ ≤ 1 := inv_le_one_of_one_le₀ htbound
  have hinvpos : 0 < t⁻¹ := inv_pos.mpr htpos
  have hb : 0 < delta * (t⁻¹ * sigma) := by positivity
  have hb1 : delta * (t⁻¹ * sigma) ≤ 1 := by
    have h : t⁻¹ * sigma ≤ 1 := mul_le_one₀ hinv hs.le hs1
    exact mul_le_one₀ hd1 (by positivity) h
  have hc : 0 < multipleC (t⁻¹ * sigma) delta k := pow_pos hb _
  have hc1 : multipleC (t⁻¹ * sigma) delta k ≤ 1 := pow_le_one₀ hb.le hb1
  exact ⟨Real.rpow_pos_of_pos hc t, Real.rpow_le_one hc.le hc1 htpos.le⟩

/-- The square-root target used by the construction is exactly the corrected
catalogue width; no exponent or prefactor is lost in the conversion. -/
theorem section16Lemma6Width_eq_sqrt (m q k : Nat) (sigma delta theta1 zeta : Real) :
    section16Lemma6Width m q k sigma delta theta1 zeta =
      (zeta / 2) * Real.sqrt ((m : Real) ^
        ((multipleC ((section16T delta theta1 k)⁻¹ * sigma) delta k) ^
          section16T delta theta1 k * section16RecurrenceExponent k q)) := by
  unfold section16Lemma6Width
  dsimp only
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg m)]
  congr 2
  simp only [section16RecurrenceExponent, zpow_neg, zpow_natCast, div_eq_mul_inv, mul_inv_rev]
  rw [mul_comm sigma (section16T delta theta1 k)⁻¹]
  ring

/-- Initial widths below four have target at most one, so the singleton
construction handles them without any recurrence or properness assumptions. -/
theorem section16Lemma6Width_small {theta gamma sigma : Real} {m k q : Nat}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hs : 0 < sigma) (hs1 : sigma ≤ 1) (hm : m < 4) :
    section16Lemma6Width m q k sigma (section16Delta (section16ThetaOne theta gamma k))
      (section16ThetaOne theta gamma k) (section16Zeta theta gamma k) ≤ 1 := by
  obtain ⟨ha, ha1⟩ := section16_lemma6_exponent_bounds k ht ht1 hg hg1 hs hs1
  obtain ⟨he, he1⟩ := section16RecurrenceExponent_pos_le_one k q
  obtain ⟨hz, hz32⟩ := section16Zeta_pos_le_one_div_32 k ht ht1 hg hg1
  rw [section16Lemma6Width_eq_sqrt]
  let a := (multipleC ((section16T (section16Delta (section16ThetaOne theta gamma k))
    (section16ThetaOne theta gamma k) k)⁻¹ * sigma)
    (section16Delta (section16ThetaOne theta gamma k)) k) ^
    section16T (section16Delta (section16ThetaOne theta gamma k)) (section16ThetaOne theta gamma k) k
  change (section16Zeta theta gamma k / 2) * Real.sqrt ((m : Real) ^ (a * section16RecurrenceExponent k q)) ≤ 1
  have hae : 0 < a * section16RecurrenceExponent k q := mul_pos ha he
  have hae1 : a * section16RecurrenceExponent k q ≤ 1 := mul_le_one₀ ha1 he.le he1
  by_cases hm0 : m = 0
  · subst m
    simp [Real.zero_rpow hae.ne']
  · have hm1 : (1 : Real) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    have hpow : (m : Real) ^ (a * section16RecurrenceExponent k q) ≤ m := by
      simpa using Real.rpow_le_rpow_of_exponent_le hm1 hae1
    have hm4 : (m : Real) < 4 := by exact_mod_cast hm
    have hr := Real.sqrt_nonneg ((m : Real) ^ (a * section16RecurrenceExponent k q))
    have hrsq := Real.sq_sqrt (Real.rpow_nonneg (Nat.cast_nonneg m) (a * section16RecurrenceExponent k q))
    have hr2 : Real.sqrt ((m : Real) ^ (a * section16RecurrenceExponent k q)) ≤ 2 := by nlinarith
    nlinarith

end LeanProofs.GowersSzemeredi
