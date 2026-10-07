import GowersSzemeredi.Proofs13SquareExtraction
import GowersSzemeredi.Proofs13LargeScaleRecurrence

/-! Uniform large-scale bounds for the final Section 13 square construction. -/

set_option autoImplicit false
noncomputable section
open Filter
namespace LeanProofs.GowersSzemeredi

/-- Flooring and integer halving retain at least a quarter above scale four. -/
theorem quarter_le_floor_half {x : Real} (hx : 4 ≤ x) :
    x / 4 ≤ ((Nat.floor x / 2 : Nat) : Real) := by
  have hfloor := Nat.lt_floor_add_one x
  have hdiv : (2 : Real) * ((Nat.floor x / 2 : Nat) : Real) +
      ((Nat.floor x % 2 : Nat) : Real) = (Nat.floor x : Real) := by
    exact_mod_cast Nat.div_add_mod (Nat.floor x) 2
  have hr : ((Nat.floor x % 2 : Nat) : Real) ≤ 1 := by
    exact_mod_cast (by have := Nat.mod_lt (Nat.floor x) (by omega : 0 < 2); omega : Nat.floor x % 2 ≤ 1)
  linarith only [hx, hfloor, hdiv, hr]

/-- The three remaining row, coefficient-width, and affine scale conditions
hold uniformly as the Stage 13.6 length tends to infinity. -/
theorem eventually_square_scales {f g W : Real} (hf : 0 < f) (hg : 0 < g) :
    ∀ᶠ L : Nat in atTop, 8 ≤ (L : Real) ^ f ∧ W ≤ (L : Real) ^ f ∧
      8 ≤ ((Nat.floor ((L : Real) ^ f) / 2 : Nat) : Real) ^ g := by
  have hc : 0 < (1 / 4 : Real) ^ g := Real.rpow_pos_of_pos (by norm_num) _
  filter_upwards [eventually_nat_mul_rpow_le (C := 8) (D := 1) hf zero_lt_one,
    eventually_nat_mul_rpow_le (C := W) (D := 1) hf zero_lt_one,
    eventually_nat_mul_rpow_le (C := 8) (D := (1 / 4 : Real) ^ g) (mul_pos hf hg) hc] with
      L h8 hW hgrow
  simp only [Real.rpow_zero, mul_one, one_mul] at h8 hW hgrow
  refine ⟨h8, hW, ?_⟩
  have hquarter := quarter_le_floor_half (show 4 ≤ (L : Real) ^ f by linarith only [h8])
  calc
    8 ≤ (1 / 4 : Real) ^ g * (L : Real) ^ (f * g) := hgrow
    _ = ((L : Real) ^ f / 4) ^ g := by
      rw [show (L : Real) ^ f / 4 = (1 / 4 : Real) * (L : Real) ^ f by ring,
        Real.mul_rpow (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg _) _),
        ← Real.rpow_mul (Nat.cast_nonneg L)]
    _ ≤ _ := Real.rpow_le_rpow (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by norm_num))
      hquarter hg.le

/-- A positive power-law lower bound forces all three square scales for
large N, uniformly over every progression length above that lower bound. -/
theorem square_scales_above_power_lower_bound {c e f g W : Real}
    (hc : 0 < c) (he : 0 < e) (hf : 0 < f) (hg : 0 < g) :
    ∃ N₀ : Nat, ∀ N : Nat, N₀ ≤ N → ∀ L : Nat,
      c * (N : Real) ^ e ≤ L →
      8 ≤ (L : Real) ^ f ∧ W ≤ (L : Real) ^ f ∧
        8 ≤ ((Nat.floor ((L : Real) ^ f) / 2 : Nat) : Real) ^ g := by
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp (eventually_square_scales (W := W) hf hg)
  have hall : ∀ᶠ N : Nat in atTop, ∀ L : Nat, c * (N : Real) ^ e ≤ L →
      8 ≤ (L : Real) ^ f ∧ W ≤ (L : Real) ^ f ∧
        8 ≤ ((Nat.floor ((L : Real) ^ f) / 2 : Nat) : Real) ^ g := by
    filter_upwards [eventually_nat_mul_rpow_le (C := (L₀ : Real)) he hc] with N hN
    intro L hL
    have hbase : (L₀ : Real) ≤ c * (N : Real) ^ e := by
      simpa only [Real.rpow_zero, mul_one] using hN
    have hbound : (L₀ : Real) ≤ L := hbase.trans hL
    exact hL₀ L (by exact_mod_cast hbound)
  exact eventually_atTop.mp hall

/-- The nested floors and final subtraction preserve a concrete positive
power of N. The factor four in the exponent absorbs all fixed constants. -/
theorem eventually_square_power_lower {c e f g : Real}
    (hc : 0 < c) (he : 0 < e) (hf : 0 < f) (hg : 0 < g) :
    ∀ᶠ N : Nat in atTop, (N : Real) ^ (e * f * g / 4) ≤
      ((Nat.floor ((c * (N : Real) ^ e) ^ f) / 2 : Nat) : Real) ^ (g / 2) - 1 := by
  let C := (c ^ f / 4) ^ (g / 2)
  have hC : 0 < C := Real.rpow_pos_of_pos (div_pos (Real.rpow_pos_of_pos hc _) (by norm_num)) _
  have hef : 0 < e * f := mul_pos he hf
  have hfg : 0 < e * f * g := mul_pos hef hg
  have hgap : e * f * g / 4 < e * f * (g / 2) := by nlinarith only [hfg]
  filter_upwards [eventually_nat_mul_rpow_le (C := 4) (D := c ^ f) hef (Real.rpow_pos_of_pos hc _),
    eventually_nat_mul_rpow_le (C := 2) (D := C) hgap hC,
    eventually_ge_atTop (1 : Nat)] with N hfour hpower hN
  have hNreal : (1 : Real) ≤ N := by exact_mod_cast hN
  have hfour' : 4 ≤ (c * (N : Real) ^ e) ^ f := by
    rw [Real.mul_rpow hc.le (Real.rpow_nonneg (Nat.cast_nonneg _) _),
      ← Real.rpow_mul (Nat.cast_nonneg N)]
    simpa only [Real.rpow_zero, mul_one] using hfour
  have hquarter := quarter_le_floor_half hfour'
  have hpow : ((c * (N : Real) ^ e) ^ f / 4) ^ (g / 2) =
      C * (N : Real) ^ (e * f * (g / 2)) := by
    rw [Real.mul_rpow hc.le (Real.rpow_nonneg (Nat.cast_nonneg _) _),
      ← Real.rpow_mul (Nat.cast_nonneg N),
      show c ^ f * (N : Real) ^ (e * f) / 4 = c ^ f / 4 * (N : Real) ^ (e * f) by ring,
      Real.mul_rpow (by positivity) (Real.rpow_nonneg (Nat.cast_nonneg _) _),
      ← Real.rpow_mul (Nat.cast_nonneg N)]
  have hlarge : 2 * (N : Real) ^ (e * f * g / 4) ≤
      ((Nat.floor ((c * (N : Real) ^ e) ^ f) / 2 : Nat) : Real) ^ (g / 2) := by
    calc
      _ ≤ C * (N : Real) ^ (e * f * (g / 2)) := hpower
      _ = _ := hpow.symm
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hquarter (by positivity)
  have hone : 1 ≤ (N : Real) ^ (e * f * g / 4) := Real.one_le_rpow hNreal (by positivity)
  linarith only [hlarge, hone]

end LeanProofs.GowersSzemeredi
