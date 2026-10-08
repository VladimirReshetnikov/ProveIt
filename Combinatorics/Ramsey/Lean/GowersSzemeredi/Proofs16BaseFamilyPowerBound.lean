import GowersSzemeredi.Proofs16BaseCaseCubicExtraction
import GowersSzemeredi.Proofs16BaseCaseAssembly

/-! Bound the fixed Freiman-family count by a single modest power of the
inverse density product. Keeping this estimate separate from the much
larger source iteration budget is important for the spectrum recurrence. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open BaseCase

theorem section16BaseFamilyBound_le_ratio {gamma theta : Real}
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) :
    (section16BaseFamilyBound gamma theta : Real) ≤
      gamma ^ (-(2 : Int)) / lemma163Alpha gamma theta := by
  have hα := lemma163Alpha_pos hg ht
  unfold section16BaseFamilyBound
  rw [Nat.cast_max, Nat.cast_one]
  apply max_le
  · exact (one_le_div (lemma163Alpha_pos hg ht)).mpr
      (lemma163Alpha_le_gammaInvSq hg hg1 ht ht1)
  · exact Nat.floor_le (by positivity)

/-- The reciprocal extraction mass has exponent 10000 in the inverse
density product; its constant is absorbed by the factor two in the base. -/
theorem lemma163Alpha_inverse_le_power {gamma theta : Real}
    (hg : 0 < gamma) (ht : 0 < theta) :
    (lemma163Alpha gamma theta)⁻¹ ≤ (2 / (gamma * theta))^(10000 : Nat) := by
  have hp : 0 < gamma * theta := mul_pos hg ht
  have hα := lemma163Alpha_pos hg ht
  have htwo : (2 : Real)^(-(10000 : Real)) ≤ (2 : Real)^(-(2000 : Real)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hlower : (gamma * theta / 2)^(10000 : Nat) ≤ lemma163Alpha gamma theta := by
    calc
      _ = (2 : Real)^(-(10000 : Real)) * (gamma * theta)^(10000 : Nat) := by
        rw [Real.rpow_neg (by norm_num : (0 : Real) ≤ 2), Real.rpow_ofNat, div_pow]
        rw [div_eq_mul_inv, mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_right htwo (by positivity)
  have hh := one_div_le_one_div_of_le (by positivity : 0 < (gamma * theta / 2)^(10000 : Nat)) hlower
  simpa only [one_div, ← inv_pow, inv_div] using hh

/-- A fixed family of at most (2/(gamma*theta))^10002 graphs suffices. -/
theorem section16BaseFamilyBound_le_power {gamma theta : Real}
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (ht : 0 < theta) (ht1 : theta ≤ 1) :
    (section16BaseFamilyBound gamma theta : Real) ≤
      (2 / (gamma * theta))^(10002 : Nat) := by
  have hp : 0 < gamma * theta := mul_pos hg ht
  have hα := lemma163Alpha_pos hg ht
  have hginv : 1 / gamma ≤ 2 / (gamma * theta) := by
    apply (div_le_div_iff₀ hg hp).mpr
    have hh := mul_le_mul_of_nonneg_left ht1 hg.le
    nlinarith
  have hgpow : gamma ^ (-(2 : Int)) ≤ (2 / (gamma * theta))^(2 : Nat) := by
    rw [zpow_neg, zpow_ofNat, ← inv_pow]
    exact pow_le_pow_left₀ (by positivity) (by simpa only [one_div] using hginv) _
  calc
    (section16BaseFamilyBound gamma theta : Real) ≤ gamma ^ (-(2 : Int)) / lemma163Alpha gamma theta :=
      section16BaseFamilyBound_le_ratio hg hg1 ht ht1
    _ = gamma ^ (-(2 : Int)) * (lemma163Alpha gamma theta)⁻¹ := div_eq_mul_inv _ _
    _ ≤ (2 / (gamma * theta))^(2 : Nat) * (2 / (gamma * theta))^(10000 : Nat) :=
      mul_le_mul hgpow (lemma163Alpha_inverse_le_power hg ht) (by positivity) (by positivity)
    _ = _ := by rw [← pow_add]

end LeanProofs.GowersSzemeredi
