import GowersSzemeredi.Proofs16ProductAssembly
import GowersSzemeredi.Proofs16RadiusComparison

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

/-- The Lemma 16.6 width for a spectrum cover with graph count `q` and width
exponent `a`, in the square-root form of `section16Lemma6Width_eq_sqrt`. -/
def lemma6WidthWith (m q k : Nat) (a zeta : Real) : Real :=
  (zeta / 2) * Real.sqrt ((m : Real) ^ (a * section16RecurrenceExponent k q))

theorem lemma6WidthWith_small {m q k : Nat} {a theta gamma : Real}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (ha : 0 ≤ a) (ha1 : a ≤ 1) (hm : m < 4) :
    lemma6WidthWith m q k a (section16Zeta theta gamma k) ≤ 1 := by
  obtain ⟨hz, hzh⟩ := section16Zeta_pos_le_half k ht ht1 hg hg1
  have he := (section16RecurrenceExponent_pos_le_one k q).1
  have he1 := (section16RecurrenceExponent_pos_le_one k q).2
  have hx0 : 0 ≤ a * section16RecurrenceExponent k q := mul_nonneg ha he.le
  have hx1 : a * section16RecurrenceExponent k q ≤ 1 := by nlinarith
  have hm3 : (m : Real) ≤ 3 := by exact_mod_cast (by omega : m ≤ 3)
  have hpow : (m : Real) ^ (a * section16RecurrenceExponent k q) ≤ 3 := by
    rcases Nat.eq_zero_or_pos m with hm0 | hm0
    · subst hm0
      rcases eq_or_lt_of_le hx0 with h | h
      · rw [← h]; norm_num
      · rw [Nat.cast_zero, Real.zero_rpow h.ne']; norm_num
    · have hm1 : (1 : Real) ≤ m := by exact_mod_cast hm0
      calc (m : Real) ^ (a * section16RecurrenceExponent k q)
          ≤ (m : Real) ^ (1 : Real) := Real.rpow_le_rpow_of_exponent_le hm1 hx1
        _ = m := Real.rpow_one _
        _ ≤ 3 := hm3
  have hsqrt : Real.sqrt ((m : Real) ^ (a * section16RecurrenceExponent k q)) ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    linarith
  unfold lemma6WidthWith
  calc section16Zeta theta gamma k / 2 *
        Real.sqrt ((m : Real) ^ (a * section16RecurrenceExponent k q))
      ≤ (1 / 2) / 2 * 2 := by
        apply mul_le_mul (by linarith) hsqrt (Real.sqrt_nonneg _) (by norm_num)
    _ ≤ 1 := by norm_num

/-- Initial widths below four have target at most one, so the singleton
construction handles them without any recurrence or properness assumptions. -/
theorem section16Lemma6Width_small {theta gamma sigma : Real} {m k q : Nat}
    (ht : 0 < theta) (ht1 : theta ≤ 1) (hg : 0 < gamma) (hg1 : gamma ≤ 1)
    (hs : 0 < sigma) (hs1 : sigma ≤ 1) (hm : m < 4) :
    section16Lemma6Width m q k sigma (section16Delta (section16ThetaOne theta gamma k))
      (section16ThetaOne theta gamma k) (section16Zeta theta gamma k) ≤ 1 := by
  obtain ⟨ha, ha1⟩ := section16_lemma6_exponent_bounds k ht ht1 hg hg1 hs hs1
  rw [section16Lemma6Width_eq_sqrt]
  exact lemma6WidthWith_small ht ht1 hg hg1 ha.le ha1 hm

end LeanProofs.GowersSzemeredi
