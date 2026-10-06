import GowersSzemeredi.Proofs16DomainBounds
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Floor.Semifield

/-! # Explicit Bohr-radius budget for Lemma 16.5 -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- A convenient coarse exponential majorant, used only for radius budgets. -/
theorem real_le_two_rpow_twice {x : Real} (hx : 0 < x) : x ≤ (2 : Real) ^ (2 * x) := by
  apply Real.le_rpow_of_log_le (by norm_num)
  have hlog := Real.log_le_sub_one_of_pos hx
  have htwo : (1 : Real) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  nlinarith

/-- Uniform lower bound for the corrected, ceiling-based Section 10 radius. -/
theorem section10Zeta_lower_budget {a alpha : Real}
    (ha : 0 < a) (haAlpha : a ≤ alpha) (hAlpha : alpha ≤ 1 / 6) :
    (2 : Real) ^ (-((2 : Real) ^ (83 : Nat) / a ^ 11)) ≤ section10Zeta alpha := by
  have hAlpha0 : 0 < alpha := ha.trans_le haAlpha
  have haOne : a ≤ 1 := by linarith
  have hAlphaOne : alpha ≤ 1 := by linarith
  let K := section10SpectrumParameter alpha
  have hspec : (1 : Real) ≤ section10SpectrumBound alpha := by
    have hp : alpha ^ (10 : Nat) ≤ 1 := pow_le_one₀ hAlpha0.le hAlphaOne
    have hi : (1 : Real) ≤ (alpha ^ (10 : Nat))⁻¹ := (one_le_inv₀ (pow_pos hAlpha0 10)).mpr hp
    unfold section10SpectrumBound
    rw [Real.rpow_neg hAlpha0.le, Real.rpow_ofNat]
    exact one_le_mul_of_one_le_of_one_le (by norm_num) hi
  have hKpos : 0 < K := by
    have hceil := Nat.le_ceil (section10SpectrumBound alpha)
    have : (0 : Real) < K := by dsimp [K, section10SpectrumParameter]; linarith
    exact_mod_cast this
  have hKr : (0 : Real) < K := by exact_mod_cast hKpos
  have hK : (K : Real) ≤ (2 : Real) ^ (75 : Nat) / a ^ 10 := by
    have hc : (K : Real) ≤ 2 * section10SpectrumBound alpha := Nat.ceil_le_two_mul (by linarith)
    have hi : (alpha ^ (10 : Nat))⁻¹ ≤ (a ^ (10 : Nat))⁻¹ :=
      inv_anti₀ (pow_pos ha 10) (pow_le_pow_left₀ ha.le haAlpha 10)
    unfold section10SpectrumBound at hc
    rw [Real.rpow_neg hAlpha0.le, Real.rpow_ofNat] at hc
    calc
      (K : Real) ≤ 2 * ((2 : Real) ^ (74 : Nat) * (alpha ^ (10 : Nat))⁻¹) := hc
      _ = (2 : Real) ^ (75 : Nat) * (alpha ^ (10 : Nat))⁻¹ := by ring
      _ ≤ (2 : Real) ^ (75 : Nat) * (a ^ (10 : Nat))⁻¹ :=
        mul_le_mul_of_nonneg_left hi (by positivity)
      _ = _ := rfl
  have hbase : (2 : Real) ^ (-(2 / a)) ≤ alpha := by
    have hx := real_le_two_rpow_twice (inv_pos.mpr ha)
    have hi := inv_anti₀ (inv_pos.mpr ha) hx
    rw [inv_inv] at hi
    rw [Real.rpow_neg (by norm_num : (0 : Real) ≤ 2)]
    exact (by simpa [div_eq_mul_inv] using hi : ((2 : Real) ^ (2 / a))⁻¹ ≤ a).trans haAlpha
  have hden : (2 : Real) ^ (-(2 * (K : Real))) ≤ (K : Real)⁻¹ := by
    rw [Real.rpow_neg (by norm_num : (0 : Real) ≤ 2)]
    exact inv_anti₀ hKr (real_le_two_rpow_twice hKr)
  have hpow : ((2 : Real) ^ (-(2 / a))) ^ (18 * K) ≤ alpha ^ (18 * K) :=
    pow_le_pow_left₀ (Real.rpow_pos_of_pos (by norm_num) _).le hbase _
  have hcoarse : (2 : Real) ^ (-((157 + 36 / a) * K)) ≤ section10Zeta alpha := by
    have heq : (2 : Real) ^ (-((157 + 36 / a) * K)) =
        (2 : Real) ^ (-(155 : Real) * K) *
          ((2 : Real) ^ (-(2 / a))) ^ (18 * K) * (2 : Real) ^ (-(2 * (K : Real))) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 2),
        ← Real.rpow_add (by norm_num : (0 : Real) < 2),
        ← Real.rpow_add (by norm_num : (0 : Real) < 2)]
      congr 1
      push_cast
      ring
    rw [heq]
    unfold section10Zeta
    change _ ≤ (2 : Real) ^ (-(155 : Real) * K) * alpha ^ (18 * K) / K
    simp only [div_eq_mul_inv] at hpow ⊢
    exact mul_le_mul (mul_le_mul_of_nonneg_left hpow (by positivity)) hden
      (by positivity) (by positivity)
  have hcoeff : (157 : Real) + 36 / a ≤ 193 / a := by
    apply (le_div_iff₀ ha).mpr
    have heq : (157 + 36 / a) * a = 157 * a + 36 := by field_simp
    rw [heq]
    linarith
  have hbudget : (157 + 36 / a) * (K : Real) ≤ (2 : Real) ^ (83 : Nat) / a ^ 11 := by
    calc
      _ ≤ (193 / a) * ((2 : Real) ^ (75 : Nat) / a ^ 10) := by gcongr
      _ = (193 * (2 : Real) ^ (75 : Nat)) / a ^ 11 := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right (by norm_num) (pow_nonneg ha.le 11)
  exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) ≤ 2)
    (neg_le_neg hbudget)).trans hcoarse

end LeanProofs.GowersSzemeredi
