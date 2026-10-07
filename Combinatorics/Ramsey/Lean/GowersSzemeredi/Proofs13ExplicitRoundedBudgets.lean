import GowersSzemeredi.Proofs13UniformRoundedBudgets
import GowersSzemeredi.Proofs13ExplicitPowerThreshold

/-! A closed threshold for the simultaneous rounded recurrence and Bohr
budgets, uniform over all admissible actual coefficients and exponents. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def uniformRoundedPowerThreshold (c d z e : Real) : Real :=
  max (positivePowerThreshold 1 c e)
    (max (positivePowerThreshold 4 d e) (positivePowerThreshold 1 (z * d) e))

/-- The rounded integer is constructed above a displayed finite threshold,
not an existential large-modulus witness. -/
theorem uniform_rounded_power_budgets_explicit
    {c₀ d z₀ e₀ : Real} (hc₀ : 0 < c₀) (hd : 0 < d) (hdone : d ≤ 1)
    (hz₀ : 0 < z₀) (he₀ : 0 < e₀)
    (N : Nat) (hthreshold : uniformRoundedPowerThreshold c₀ d z₀ e₀ ≤ N)
    (c e u v w z P Q : Real)
    (hc : c₀ ≤ c) (hcmax : c ≤ 1 / 2) (he : e₀ ≤ e) (hemax : 2 * e ≤ 1)
    (hv : 0 < v) (hvone : v ≤ 1) (hw : 0 < w) (hwone : w ≤ 1) (hz : z₀ ≤ z)
    (hrec : 2 * e ≤ u * v) (hbohr : 2 * e ≤ u * w)
    (hP : d * (N : Real) ^ u ≤ P) (hQ : P ^ v / 2 ≤ Q) :
    ∃ m : Nat, 0 < m ∧ m ^ 2 ≤ N ∧ (m : Real) + 1 ≤ Q ∧
      c * (N : Real) ^ e ≤ m ∧ P ^ (-w) ≤ z / m := by
  have h₁ : positivePowerThreshold 1 c₀ e₀ ≤ (N : Real) := (le_max_left _ _).trans hthreshold
  have h₂ : positivePowerThreshold 4 d e₀ ≤ (N : Real) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hthreshold)
  have h₃ : positivePowerThreshold 1 (z₀ * d) e₀ ≤ (N : Real) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hthreshold)
  have hN : 1 ≤ N := by exact_mod_cast (positivePowerThreshold_one_le 1 c₀ e₀).trans h₁
  have ht := positivePowerThreshold_spec hc₀ he₀ h₁
  have hr := positivePowerThreshold_spec hd he₀ h₂
  have hb := positivePowerThreshold_spec (mul_pos hz₀ hd) he₀ h₃
  have hNreal : (1 : Real) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : Real) < N := zero_lt_one.trans_le hNreal
  have hcpos : 0 < c := hc₀.trans_le hc
  have hepos : 0 < e := he₀.trans_le he
  have hpower : (N : Real) ^ e₀ ≤ (N : Real) ^ e :=
    Real.rpow_le_rpow_of_exponent_le hNreal he
  have hone : 1 ≤ c * (N : Real) ^ e := by
    calc
      _ ≤ c₀ * (N : Real) ^ e₀ := by simpa only [Real.rpow_zero, mul_one] using ht
      _ ≤ _ := mul_le_mul hc hpower (Real.rpow_nonneg hNpos.le _) hcpos.le
  have hrecconst : 4 ≤ d * (N : Real) ^ e := by
    calc
      _ ≤ d * (N : Real) ^ e₀ := by simpa only [Real.rpow_zero, mul_one] using hr
      _ ≤ _ := mul_le_mul_of_nonneg_left hpower hd.le
  have hbohrconst : 1 ≤ z * d * (N : Real) ^ e := by
    calc
      _ ≤ z₀ * d * (N : Real) ^ e₀ := by simpa only [Real.rpow_zero, mul_one] using hb
      _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_right hz hd.le) hpower
        (Real.rpow_nonneg hNpos.le _) (mul_nonneg (hz₀.trans_le hz).le hd.le)
  have hPpos : 0 < P := (mul_pos hd (Real.rpow_pos_of_pos hNpos u)).trans_le hP
  have hpow (s : Real) (hs : 0 < s) (hsone : s ≤ 1) (hgap : 2 * e ≤ u * s) :
      d * ((N : Real) ^ e * (N : Real) ^ e) ≤ P ^ s := by
    calc
      _ = d * (N : Real) ^ (2 * e) := by rw [← Real.rpow_add hNpos]; congr 2; ring
      _ ≤ d ^ s * (N : Real) ^ (u * s) := by
        apply mul_le_mul _ (Real.rpow_le_rpow_of_exponent_le hNreal hgap)
          (Real.rpow_nonneg hNpos.le _) (Real.rpow_nonneg hd.le _)
        simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_ge hd hdone hsone
      _ = (d * (N : Real) ^ u) ^ s := by
        rw [Real.mul_rpow hd.le (Real.rpow_nonneg hNpos.le _), ← Real.rpow_mul hNpos.le]
      _ ≤ P ^ s := Real.rpow_le_rpow (by positivity) hP hs.le
  let m : Nat := Nat.ceil (c * (N : Real) ^ e)
  have hmpos : 0 < m := Nat.one_le_ceil_iff.mpr (zero_lt_one.trans_le hone)
  have hmlower : c * (N : Real) ^ e ≤ (m : Real) := Nat.le_ceil _
  have hmround : (m : Real) < c * (N : Real) ^ e + 1 :=
    Nat.ceil_lt_add_one (zero_le_one.trans hone)
  have hmupper : (m : Real) ≤ (N : Real) ^ e := by
    have hmul := mul_le_mul_of_nonneg_right hcmax (Real.rpow_nonneg hNpos.le e)
    linarith only [hmround, hone, hmul]
  have hnone : 1 ≤ (N : Real) ^ e := Real.one_le_rpow hNreal hepos.le
  have hmsquare : (m : Real) ^ 2 ≤ (N : Real) := by
    calc
      _ ≤ ((N : Real) ^ e) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hmupper 2
      _ = (N : Real) ^ (2 * e) := by rw [← Real.rpow_mul_natCast hNpos.le]; congr 1; ring
      _ ≤ (N : Real) ^ (1 : Real) := Real.rpow_le_rpow_of_exponent_le hNreal hemax
      _ = _ := Real.rpow_one _
  refine ⟨m, hmpos, by exact_mod_cast hmsquare, ?_, hmlower, ?_⟩
  · have hmul := mul_le_mul_of_nonneg_right hrecconst (Real.rpow_nonneg hNpos.le e)
    have hp := hpow v hv hvone hrec
    nlinarith only [hmupper, hnone, hmul, hp, hQ]
  · have hmul := mul_le_mul_of_nonneg_right hbohrconst (Real.rpow_nonneg hNpos.le e)
    have hp := mul_le_mul_of_nonneg_left (hpow w hw hwone hbohr) (hz₀.trans_le hz).le
    have hmP : (m : Real) ≤ z * P ^ w := by nlinarith only [hmupper, hmul, hp]
    rw [Real.rpow_neg hPpos.le, ← one_div]
    apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hPpos _) (by exact_mod_cast hmpos)).mpr
    simpa only [one_mul] using hmP

end LeanProofs.GowersSzemeredi
