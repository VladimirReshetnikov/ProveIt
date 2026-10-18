import GowersSzemeredi.Proofs13UniformDensityParameters
import GowersSzemeredi.Proofs13ExplicitPowerThreshold

/-! Ceiling budgets with a threshold uniform over variable exponents.

`uniform_rounded_power_budgets` is in `Proofs13UniformRoundedBudgetsSide`,
outside the final route. -/

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
  simp only [uniformRoundedPowerThreshold, max_le_iff] at hthreshold
  obtain ⟨h₁, h₂, h₃⟩ := hthreshold
  have hNreal : (1 : Real) ≤ N := (positivePowerThreshold_one_le 1 c₀ e₀).trans h₁
  have hNpos : (0 : Real) < N := zero_lt_one.trans_le hNreal
  have hX0 : 0 ≤ (N : Real) ^ e := Real.rpow_nonneg hNpos.le e
  have hpower : (N : Real) ^ e₀ ≤ (N : Real) ^ e := Real.rpow_le_rpow_of_exponent_le hNreal he
  have hz0 : 0 ≤ z := hz₀.le.trans hz
  have hone : 1 ≤ c * (N : Real) ^ e := (positivePowerThreshold_spec hc₀ he₀ h₁).trans
    (mul_le_mul hc hpower (by positivity) (hc₀.le.trans hc))
  have hrecconst : 4 ≤ d * (N : Real) ^ e :=
    (positivePowerThreshold_spec hd he₀ h₂).trans (mul_le_mul_of_nonneg_left hpower hd.le)
  have hbohrconst : 1 ≤ z * d * (N : Real) ^ e :=
    (positivePowerThreshold_spec (mul_pos hz₀ hd) he₀ h₃).trans (mul_le_mul
      (mul_le_mul_of_nonneg_right hz hd.le) hpower (by positivity) (mul_nonneg hz0 hd.le))
  have hPpos : 0 < P := (mul_pos hd (Real.rpow_pos_of_pos hNpos u)).trans_le hP
  have hXX : (N : Real) ^ e * (N : Real) ^ e = (N : Real) ^ (2 * e) := by
    rw [← Real.rpow_add hNpos, two_mul]
  have hpow (s : Real) (hs : 0 < s) (hsone : s ≤ 1) (hgap : 2 * e ≤ u * s) :
      d * ((N : Real) ^ e * (N : Real) ^ e) ≤ P ^ s := by
    rw [hXX]
    refine (mul_le_mul (Real.self_le_rpow_of_le_one hd.le hdone hsone)
      (Real.rpow_le_rpow_of_exponent_le hNreal hgap) (by positivity) (by positivity)).trans ?_
    rw [Real.rpow_mul hNpos.le, ← Real.mul_rpow hd.le (Real.rpow_nonneg hNpos.le u)]
    gcongr
  let m : Nat := Nat.ceil (c * (N : Real) ^ e)
  have hmlower : c * (N : Real) ^ e ≤ (m : Real) := Nat.le_ceil _
  have hmupper : (m : Real) ≤ (N : Real) ^ e := by
    have hm : (m : Real) < c * (N : Real) ^ e + 1 := Nat.ceil_lt_add_one (zero_le_one.trans hone)
    linarith [mul_le_mul_of_nonneg_right hcmax hX0]
  have hmpos : (0 : Real) < m := zero_lt_one.trans_le (hone.trans hmlower)
  refine ⟨m, by exact_mod_cast hmpos, ?_, ?_, hmlower, ?_⟩
  · have hm2 : (m : Real) ^ 2 ≤ N := by
      linarith [mul_self_le_mul_self hmpos.le hmupper,
        (Real.rpow_le_rpow_of_exponent_le hNreal hemax).trans_eq (Real.rpow_one _)]
    exact_mod_cast hm2
  · linarith [mul_le_mul_of_nonneg_right hrecconst hX0, hpow v hv hvone hrec,
      Real.one_le_rpow hNreal (he₀.le.trans he)]
  · rw [Real.rpow_neg hPpos.le, le_div_iff₀ hmpos, inv_mul_le_iff₀ (Real.rpow_pos_of_pos hPpos w)]
    linarith [mul_le_mul_of_nonneg_right hbohrconst hX0,
      mul_le_mul_of_nonneg_left (hpow w hw hwone hbohr) hz0]

open Filter

end LeanProofs.GowersSzemeredi
