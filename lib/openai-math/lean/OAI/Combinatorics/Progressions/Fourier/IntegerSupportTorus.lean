import OAI.Combinatorics.Progressions.Lattices.WeightedCubeIntegerSupport

namespace OAI

section

namespace Erdos3

noncomputable def integerSupportTorusFactor (H : ℝ) : ℕ := 2 * ⌈H⌉₊ + 1

theorem integerSupportTorusFactor_pos (H : ℝ) : 0 < integerSupportTorusFactor H := by
  unfold integerSupportTorusFactor
  omega

theorem integerSupportTorusFactor_gap (H : ℝ) :
    2 * H < (integerSupportTorusFactor H : ℝ) := by
  have h := Nat.le_ceil H
  simp only [integerSupportTorusFactor, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  linarith

theorem integerSupportTorusFactor_upper {H : ℝ} (hH : 0 ≤ H) :
    (integerSupportTorusFactor H : ℝ) ≤ 2 * H + 3 := by
  have h := Nat.ceil_lt_add_one hH
  simp only [integerSupportTorusFactor, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  linarith

theorem scaled_integer_support_close {J : Type*} (y z center : J → ℤ) {H : ℝ} {K : ℕ}
    (hK : 0 < K) (hy : ∀ j, |(y j : ℝ) - center j| ≤ H * K)
    (hz : ∀ j, |(z j : ℝ) - center j| ≤ H * K) :
    ∀ j, |y j - z j| < (integerSupportTorusFactor H * K : ℕ) := by
  intro j
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hgap := mul_lt_mul_of_pos_right (integerSupportTorusFactor_gap H) hK'
  have ht : |(y j : ℝ) - z j| ≤ 2 * H * K := by
    calc
      _ = |((y j : ℝ) - center j) + (center j - z j)| := by congr 1; ring
      _ ≤ |(y j : ℝ) - center j| + |(center j : ℝ) - z j| := abs_add_le _ _
      _ ≤ H * K + H * K := add_le_add (hy j) (by simpa only [abs_sub_comm] using hz j)
      _ = _ := by ring
  have hlt := ht.trans_lt hgap
  exact_mod_cast hlt

theorem integerGridMass_eq_imageMass_of_scaled_support {X J : Type*}
    [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (center z : J → ℤ)
    {H : ℝ} {K : ℕ} (hK : 0 < K)
    (hY : ∀ x, p.weight x ≠ 0 → ∀ j, |(Y x j : ℝ) - center j| ≤ H * K)
    (hz : ∀ j, |(z j : ℝ) - center j| ≤ H * K) :
    integerGridMass p Y (integerSupportTorusFactor H * K) z = finiteImageMass p Y z := by
  apply integerGridMass_eq_imageMass
  intro x hx
  exact scaled_integer_support_close (Y x) z center hK (hY x hx) hz

theorem grid_scale_factor_le_one (R K j : ℕ) (hR : 0 < R) (hK : 0 < K) :
    ((K : ℝ) / (R * K)) ^ j ≤ 1 := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hR' : (1 : ℝ) ≤ R := by exact_mod_cast hR
  apply pow_le_one₀ (by positivity)
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith

end Erdos3

end

end OAI
