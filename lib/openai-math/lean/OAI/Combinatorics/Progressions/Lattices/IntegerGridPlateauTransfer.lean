/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Geometry.NormalizedSupportPlateau
import OAI.Combinatorics.Progressions.Probability.WeightedModeratePointMass

namespace OAI

section

namespace Erdos3

theorem integerSupportTorusFactor_margin (H : ℝ) :
    2 * H + 1 ≤ (integerSupportTorusFactor H : ℝ) := by
  have h := Nat.le_ceil H
  simp only [integerSupportTorusFactor, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  linarith

theorem scaled_integer_support_close_buffered {J : Type*} (y z center : J → ℤ)
    {H : ℝ} {K : ℕ} (hK : 0 < K)
    (hy : ∀ j, |(y j : ℝ) - center j| ≤ H * K)
    (hz : ∀ j, |(z j : ℝ) - center j| ≤ (H + 1 / 4) * K) :
    ∀ j, |y j - z j| < (integerSupportTorusFactor H * K : ℕ) := by
  intro j
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hgap : (2 * H + 1 / 4) * K < (integerSupportTorusFactor H : ℝ) * K := by
    apply mul_lt_mul_of_pos_right _ hK'
    linarith [integerSupportTorusFactor_margin H]
  have ht : |(y j : ℝ) - z j| ≤ (2 * H + 1 / 4) * K := by
    calc
      _ = |((y j : ℝ) - center j) + (center j - z j)| := by congr 1; ring
      _ ≤ |(y j : ℝ) - center j| + |(center j : ℝ) - z j| := abs_add_le _ _
      _ ≤ H * K + (H + 1 / 4) * K :=
        add_le_add (hy j) (by simpa only [abs_sub_comm] using hz j)
      _ = _ := by ring
  have hlt := ht.trans_lt hgap
  exact_mod_cast hlt

theorem integerGridMass_eq_imageMass_on_buffered_support {X J : Type*}
    [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (center z : J → ℤ)
    {H : ℝ} {K : ℕ} (hK : 0 < K)
    (hY : ∀ x, p.weight x ≠ 0 → ∀ j, |(Y x j : ℝ) - center j| ≤ H * K)
    (hz : ∀ j, |(z j : ℝ) - center j| ≤ (H + 1 / 4) * K) :
    integerGridMass p Y (integerSupportTorusFactor H * K) z = finiteImageMass p Y z := by
  apply integerGridMass_eq_imageMass
  intro x hx
  exact scaled_integer_support_close_buffered (Y x) z center hK (hY x hx) hz

end Erdos3

end

section

namespace Erdos3

open scoped Classical

theorem integerGridDensity_plateau_transfer {X J : Type*}
    [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (center z : J → ℤ)
    {H ε : ℝ} {K M : ℕ} (hH : 0 ≤ H) (hK : 0 < K)
    (hM : M = integerSupportTorusFactor H * K)
    (hY : ∀ x, p.weight x ≠ 0 → ∀ j, |(Y x j : ℝ) - center j| ≤ H * K)
    (a : ℂ) (hε : 0 ≤ ε)
    (ha : ‖(integerGridDensity p Y K M z : ℂ) - a‖ ≤ ε) :
    ‖(((K : ℝ) ^ Fintype.card J * ((p.toPMF.map Y) z).toReal : ℝ) : ℂ) -
      (normalizedSupportPlateau H (fun j => ((z j : ℝ) - center j) / K) : ℂ) * a‖ ≤ ε := by
  let χ := normalizedSupportPlateau H (fun j => ((z j : ℝ) - center j) / K)
  let v : ℂ := ((K : ℝ) ^ Fintype.card J * ((p.toPMF.map Y) z).toReal : ℝ)
  have hχ := normalizedSupportPlateau_range H (fun j => ((z j : ℝ) - center j) / K)
  have hfix : (χ : ℂ) * v = v := by
    by_cases hz : ∀ j, |(z j : ℝ) - center j| ≤ H * K
    · have he : χ = 1 := normalizedSupportPlateau_grid_one hH hK center z hz
      simp only [he, Complex.ofReal_one, one_mul]
    · have he : finiteImageMass p Y z = 0 := by
        unfold finiteImageMass FiniteProbabilityWeights.mean
        apply Finset.sum_eq_zero
        intro x _
        by_cases hx : p.weight x = 0
        · simp only [hx, zero_mul]
        · have hn : Y x ≠ z := fun he => hz (he ▸ hY x hx)
          simp only [ite_eq_right hn, mul_zero]
      rw [finiteImageMass_eq_toPMF] at he
      simp only [v, he, mul_zero, Complex.ofReal_zero]
  change ‖v - (χ : ℂ) * a‖ ≤ ε
  by_cases hχ0 : χ = 0
  · have hv : v = 0 := by simpa only [hχ0, Complex.ofReal_zero, zero_mul] using hfix.symm
    simpa only [hv, hχ0, Complex.ofReal_zero, zero_mul, sub_self, norm_zero] using hε
  · have hz := normalizedSupportPlateau_grid_support hK center z hχ0
    have hd : integerGridDensity p Y K M z =
        (K : ℝ) ^ Fintype.card J * ((p.toPMF.map Y) z).toReal := by
      unfold integerGridDensity
      rw [hM, integerGridMass_eq_imageMass_on_buffered_support p Y center z hK hY hz,
        finiteImageMass_eq_toPMF]
    rw [hd] at ha
    calc
      _ = ‖(χ : ℂ) * (v - a)‖ := by rw [mul_sub, hfix]
      _ = χ * ‖v - a‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hχ.1]
      _ ≤ 1 * ε := mul_le_mul hχ.2 ha (norm_nonneg _) zero_le_one
      _ = ε := one_mul ε

end Erdos3

end

end OAI
