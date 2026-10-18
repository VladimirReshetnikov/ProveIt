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
  let K := section10SpectrumParameter alpha
  have hspec : (1 : Real) ≤ section10SpectrumBound alpha :=
    one_le_mul_of_one_le_of_one_le (by norm_num)
      (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hAlpha0 (by linarith) (by norm_num))
  have hKr : (0 : Real) < K := Nat.cast_pos.mpr (Nat.ceil_pos.mpr (by linarith))
  have hK : (K : Real) ≤ (2 : Real) ^ (75 : Nat) / a ^ 10 :=
    calc (K : Real) ≤ 2 * section10SpectrumBound alpha := Nat.ceil_le_two_mul (by linarith)
      _ = (2 : Real) ^ (75 : Nat) / alpha ^ 10 := by
          rw [section10SpectrumBound, Real.rpow_neg hAlpha0.le, Real.rpow_ofNat]; ring
      _ ≤ _ := by gcongr
  -- the three factors of `ζ`, each against a power of two
  have hbase : (2 : Real) ^ (-(2 / a)) ≤ alpha := by
    rw [Real.rpow_neg (by norm_num : (0 : Real) ≤ 2), div_eq_mul_inv]
    exact (inv_le_of_inv_le₀ ha (real_le_two_rpow_twice (inv_pos.mpr ha))).trans haAlpha
  have hden : (2 : Real) ^ (-(2 * (K : Real))) ≤ (K : Real)⁻¹ := by
    rw [Real.rpow_neg (by norm_num : (0 : Real) ≤ 2)]
    exact inv_anti₀ hKr (real_le_two_rpow_twice hKr)
  have hcoarse : (2 : Real) ^ (-((157 + 36 / a) * K)) ≤ section10Zeta alpha :=
    calc (2 : Real) ^ (-((157 + 36 / a) * K))
        = (2 : Real) ^ (-(155 : Real) * K) * ((2 : Real) ^ (-(2 / a))) ^ (18 * K) *
            (2 : Real) ^ (-(2 * (K : Real))) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : Real) ≤ 2),
            ← Real.rpow_add (by norm_num : (0 : Real) < 2),
            ← Real.rpow_add (by norm_num : (0 : Real) < 2)]
          congr 1
          push_cast
          ring
      _ ≤ (2 : Real) ^ (-(155 : Real) * K) * alpha ^ (18 * K) * (K : Real)⁻¹ := by gcongr
      _ = section10Zeta alpha := (div_eq_mul_inv _ _).symm
  have hbudget : (157 + 36 / a) * (K : Real) ≤ (2 : Real) ^ (83 : Nat) / a ^ 11 := by
    have hcoeff : (157 : Real) + 36 / a ≤ 193 / a := by
      rw [le_div_iff₀ ha, add_mul, div_mul_cancel₀ _ ha.ne']; linarith
    calc _ ≤ (193 / a) * ((2 : Real) ^ (75 : Nat) / a ^ 10) := by gcongr
      _ = (193 * (2 : Real) ^ (75 : Nat)) / a ^ 11 := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right (by norm_num) (pow_nonneg ha.le 11)
  exact (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) ≤ 2)
    (neg_le_neg hbudget)).trans hcoarse

end LeanProofs.GowersSzemeredi
