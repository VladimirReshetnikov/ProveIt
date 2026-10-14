import GowersSzemeredi.Proofs13SquareExtraction
import GowersSzemeredi.Proofs13LargeScaleRecurrence
import GowersSzemeredi.Proofs13ExplicitPowerThreshold

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

def squareLengthThreshold (f g W : Real) : Real :=
  max (positivePowerThreshold 8 1 f)
    (max (positivePowerThreshold W 1 f)
      (positivePowerThreshold 8 ((1 / 4 : Real) ^ g) (f * g)))

theorem square_scales_of_explicit_length {f g W : Real} (hf : 0 < f) (hg : 0 < g)
    (L : Nat) (hL : squareLengthThreshold f g W ≤ L) :
    8 ≤ (L : Real) ^ f ∧ W ≤ (L : Real) ^ f ∧
      8 ≤ ((Nat.floor ((L : Real) ^ f) / 2 : Nat) : Real) ^ g := by
  have h8 := positivePowerThreshold_spec zero_lt_one hf ((le_max_left _ _).trans hL)
  have hW := positivePowerThreshold_spec zero_lt_one hf
    ((le_max_left _ _).trans ((le_max_right _ _).trans hL))
  have hgrow := positivePowerThreshold_spec (Real.rpow_pos_of_pos (by norm_num : (0 : Real) < 1 / 4) g)
    (mul_pos hf hg) ((le_max_right _ _).trans ((le_max_right _ _).trans hL))
  simp only [one_mul] at h8 hW
  refine ⟨h8, hW, ?_⟩
  have hquarter := quarter_le_floor_half (show 4 ≤ (L : Real) ^ f by linarith only [h8])
  calc
    8 ≤ (1 / 4 : Real) ^ g * (L : Real) ^ (f * g) := hgrow
    _ = ((L : Real) ^ f / 4) ^ g := by
      rw [show (L : Real) ^ f / 4 = (1 / 4 : Real) * (L : Real) ^ f by ring,
        Real.mul_rpow (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg _) _),
        ← Real.rpow_mul (Nat.cast_nonneg L)]
    _ ≤ _ := Real.rpow_le_rpow (by positivity) hquarter hg.le

def squareScaleThreshold (c e f g W : Real) : Real :=
  positivePowerThreshold (squareLengthThreshold f g W) c e

theorem square_scales_above_power_explicit {c e f g W : Real}
    (hc : 0 < c) (he : 0 < e) (hf : 0 < f) (hg : 0 < g)
    (N L : Nat) (hN : squareScaleThreshold c e f g W ≤ N)
    (hL : c * (N : Real) ^ e ≤ L) :
    8 ≤ (L : Real) ^ f ∧ W ≤ (L : Real) ^ f ∧
      8 ≤ ((Nat.floor ((L : Real) ^ f) / 2 : Nat) : Real) ^ g :=
  square_scales_of_explicit_length hf hg L ((positivePowerThreshold_spec hc he hN).trans hL)

def squarePowerThreshold (c e f g : Real) : Real :=
  max (positivePowerThreshold 4 (c ^ f) (e * f))
    (positivePowerThreshold 2 ((c ^ f / 4) ^ (g / 2)) (e * f * g / 4))

/-- Nested rounding and the final subtraction retain the displayed power
above a closed bound built from positive powers. -/
theorem square_power_lower_explicit {c e f g : Real}
    (hc : 0 < c) (he : 0 < e) (hf : 0 < f) (hg : 0 < g)
    (N : Nat) (hN : squarePowerThreshold c e f g ≤ N) :
    (N : Real) ^ (e * f * g / 4) ≤
      ((Nat.floor ((c * (N : Real) ^ e) ^ f) / 2 : Nat) : Real) ^ (g / 2) - 1 := by
  let C := (c ^ f / 4) ^ (g / 2)
  have hC : 0 < C := by dsimp [C]; positivity
  have hNr : (1 : Real) ≤ N :=
    (positivePowerThreshold_one_le _ _ _).trans ((le_max_left _ _).trans hN)
  have hNpos : (0 : Real) < N := zero_lt_one.trans_le hNr
  have hfour := positivePowerThreshold_spec (Real.rpow_pos_of_pos hc _) (mul_pos he hf)
    ((le_max_left _ _).trans hN)
  have htwo := positivePowerThreshold_spec hC (show 0 < e * f * g / 4 by positivity)
    ((le_max_right _ _).trans hN)
  have hfour' : 4 ≤ (c * (N : Real) ^ e) ^ f := by
    rw [Real.mul_rpow hc.le (Real.rpow_nonneg hNpos.le _), ← Real.rpow_mul hNpos.le]
    exact hfour
  have hquarter := quarter_le_floor_half hfour'
  have hpow : ((c * (N : Real) ^ e) ^ f / 4) ^ (g / 2) =
      C * (N : Real) ^ (e * f * (g / 2)) := by
    rw [Real.mul_rpow hc.le (Real.rpow_nonneg hNpos.le _), ← Real.rpow_mul hNpos.le,
      show c ^ f * (N : Real) ^ (e * f) / 4 = c ^ f / 4 * (N : Real) ^ (e * f) by ring,
      Real.mul_rpow (by positivity) (Real.rpow_nonneg hNpos.le _), ← Real.rpow_mul hNpos.le]
  have hpower : 2 * (N : Real) ^ (e * f * g / 4) ≤ C * (N : Real) ^ (e * f * (g / 2)) := by
    have h := mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hNpos.le (e * f * g / 4))
    rw [mul_assoc C _ _, ← Real.rpow_add hNpos] at h
    convert h using 1 <;> congr 2 <;> ring
  have hlarge : 2 * (N : Real) ^ (e * f * g / 4) ≤
      ((Nat.floor ((c * (N : Real) ^ e) ^ f) / 2 : Nat) : Real) ^ (g / 2) := by
    calc
      _ ≤ C * (N : Real) ^ (e * f * (g / 2)) := hpower
      _ = _ := hpow.symm
      _ ≤ _ := Real.rpow_le_rpow (by positivity) hquarter (by positivity)
  have hone : 1 ≤ (N : Real) ^ (e * f * g / 4) := Real.one_le_rpow hNr (by positivity)
  linarith only [hlarge, hone]

/-- The three remaining row, coefficient-width, and affine scale conditions
hold uniformly as the Stage 13.6 length tends to infinity. -/
theorem eventually_square_scales {f g W : Real} (hf : 0 < f) (hg : 0 < g) :
    ∀ᶠ L : Nat in atTop, 8 ≤ (L : Real) ^ f ∧ W ≤ (L : Real) ^ f ∧
      8 ≤ ((Nat.floor ((L : Real) ^ f) / 2 : Nat) : Real) ^ g := by
  filter_upwards [eventually_ge_atTop (Nat.ceil (squareLengthThreshold f g W))] with L hL
  exact square_scales_of_explicit_length hf hg L
    ((Nat.le_ceil _).trans (by exact_mod_cast hL))

/-- A positive power-law lower bound forces all three square scales for
large N, uniformly over every progression length above that lower bound. -/
theorem square_scales_above_power_lower_bound {c e f g W : Real}
    (hc : 0 < c) (he : 0 < e) (hf : 0 < f) (hg : 0 < g) :
    ∃ N₀ : Nat, ∀ N : Nat, N₀ ≤ N → ∀ L : Nat,
      c * (N : Real) ^ e ≤ L →
      8 ≤ (L : Real) ^ f ∧ W ≤ (L : Real) ^ f ∧
        8 ≤ ((Nat.floor ((L : Real) ^ f) / 2 : Nat) : Real) ^ g := by
  refine ⟨Nat.ceil (squareScaleThreshold c e f g W), ?_⟩
  intro N hN L hL
  exact square_scales_above_power_explicit hc he hf hg N L
    ((Nat.le_ceil _).trans (by exact_mod_cast hN)) hL

/-- The nested floors and final subtraction preserve a concrete positive
power of N. The factor four in the exponent absorbs all fixed constants. -/
theorem eventually_square_power_lower {c e f g : Real}
    (hc : 0 < c) (he : 0 < e) (hf : 0 < f) (hg : 0 < g) :
    ∀ᶠ N : Nat in atTop, (N : Real) ^ (e * f * g / 4) ≤
      ((Nat.floor ((c * (N : Real) ^ e) ^ f) / 2 : Nat) : Real) ^ (g / 2) - 1 := by
  filter_upwards [eventually_ge_atTop (Nat.ceil (squarePowerThreshold c e f g))] with N hN
  exact square_power_lower_explicit hc he hf hg N
    ((Nat.le_ceil _).trans (by exact_mod_cast hN))

end LeanProofs.GowersSzemeredi
