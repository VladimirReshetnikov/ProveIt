import GowersSzemeredi.Proofs16LocalizedCover

/-! # Absorbing localization and floor losses in the recurrence scale

The preliminary localization costs a factor eight before the small exponent,
and passing to an integer recurrence input costs at most two. After taking
the recurrence root their combined cost is at most sixteen.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- Above two, taking a natural floor loses at most a factor two. -/
theorem floor_half_lower {x : Real} (hx : 2 ≤ x) :
    0 < Nat.floor x ∧ x ≤ 2 * (Nat.floor x : Real) := by
  have hpos : 0 < Nat.floor x := Nat.floor_pos.mpr (by linarith)
  have hpos' : (1 : Real) ≤ Nat.floor x := by exact_mod_cast hpos
  have hlt := Nat.lt_floor_add_one x
  exact ⟨hpos, by linarith⟩

/-- Localization to m/8 and integer rounding reduce the recurrence root
by at most sixteen, uniformly for both exponents in (0,1]. -/
theorem localization_recurrence_root {m a e : Real}
    (hm : 0 < m) (_ha : 0 < a) (ha1 : a ≤ 1) (he : 0 < e) (he1 : e ≤ 1)
    (hx : 2 ≤ (m / 8) ^ a) :
    0 < Nat.floor ((m / 8) ^ a) ∧
      m ^ (a * e) ≤ 16 * (Nat.floor ((m / 8) ^ a) : Real) ^ e := by
  obtain ⟨hp, hfloor⟩ := floor_half_lower hx
  refine ⟨hp, ?_⟩
  have h8 : (8 : Real) ^ a ≤ 8 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) ≤ 8) ha1
  have h16 : (16 : Real) ^ e ≤ 16 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) ≤ 16) he1
  have hdecomp : m ^ a = (8 : Real) ^ a * (m / 8) ^ a := by
    rw [← Real.mul_rpow (by norm_num : (0 : Real) ≤ 8) (by positivity : 0 ≤ m / 8)]
    congr 1
    ring
  have hbase : m ^ a ≤ 16 * (Nat.floor ((m / 8) ^ a) : Real) := by
    rw [hdecomp]
    have h := mul_le_mul_of_nonneg_right h8 (Real.rpow_nonneg (by positivity : 0 ≤ m / 8) a)
    linarith
  calc
    m ^ (a * e) = (m ^ a) ^ e := Real.rpow_mul hm.le a e
    _ ≤ (16 * (Nat.floor ((m / 8) ^ a) : Real)) ^ e :=
      Real.rpow_le_rpow (Real.rpow_nonneg hm.le a) hbase he.le
    _ = (16 : Real) ^ e * (Nat.floor ((m / 8) ^ a) : Real) ^ e :=
      Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)
    _ ≤ 16 * (Nat.floor ((m / 8) ^ a) : Real) ^ e :=
      mul_le_mul_of_nonneg_right h16 (Real.rpow_nonneg (Nat.cast_nonneg _) e)

/-- Ceiling rounding for the original target still fits a recurrence root
that has lost a factor sixteen, provided the Bohr radius is at most 1/32. -/
theorem section16_localized_short_scale (s b zeta : Real)
    (hs : 0 < s) (hb : s ≤ 16 * b) (hz : 0 < zeta) (hz32 : zeta ≤ 1 / 32)
    (hl : 1 < (zeta / 2) * Real.sqrt s) :
    ∃ v : Nat, 2 ≤ v ∧ (zeta / 2) * Real.sqrt s ≤ (v - 1 : Nat) ∧
      (v : Real) ^ 2 + 1 ≤ b ∧ 2 / b ≤ zeta / v := by
  let l := (zeta / 2) * Real.sqrt s
  let v := Nat.ceil l + 1
  change 1 < l at hl
  have hl0 : 0 < l := by linarith
  have hv : 2 ≤ v := by
    have hc := Nat.ceil_pos.mpr hl0
    dsimp [v]
    omega
  have hvr : (0 : Real) < v := by exact_mod_cast (show 0 < v by omega)
  have hceil : l ≤ (v - 1 : Nat) := by simpa only [v, Nat.add_sub_cancel] using Nat.le_ceil l
  have hvle : (v : Real) ≤ l + 2 := by
    have hc := (Nat.ceil_lt_add_one hl0.le).le
    dsimp [v]
    push_cast
    linarith
  have hv3 : (v : Real) ≤ 3 * l := by linarith
  have hr : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
  have hrSq : (Real.sqrt s) ^ 2 = s := Real.sq_sqrt hs.le
  have hlr : l ≤ Real.sqrt s / 64 := by
    dsimp [l]
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 / 32 - zeta) hr]
  have hr64 : 64 < Real.sqrt s := by linarith
  have hvsqrt : (v : Real) ≤ 3 * Real.sqrt s / 64 := by linarith
  have hvSq : (v : Real) ^ 2 + 1 ≤ b := by
    have hv2 := pow_le_pow_left₀ hvr.le hvsqrt 2
    nlinarith
  have hrs : 48 * Real.sqrt s ≤ s := by nlinarith
  have hbudget : 2 * (v : Real) ≤ zeta * b := by
    have hmul := mul_le_mul_of_nonneg_left hrs hz.le
    have hmul' := mul_le_mul_of_nonneg_left hb hz.le
    dsimp [l] at hv3
    nlinarith
  have hb0 : 0 < b := by linarith
  exact ⟨v, hv, hceil, hvSq, (div_le_div_iff₀ hb0 hvr).mpr hbudget⟩

/-- A non-singleton original target forces enough scale for both the
quarter-width localization and the factor-two floor estimate. -/
theorem localization_inputs_of_large_target {m a e zeta : Real}
    (hm : 1 ≤ m) (ha : 0 < a) (ha1 : a ≤ 1) (_he : 0 < e) (he1 : e ≤ 1)
    (hz : 0 < zeta) (hz32 : zeta ≤ 1 / 32)
    (hl : 1 < (zeta / 2) * Real.sqrt (m ^ (a * e))) :
    4 ≤ m ∧ 2 ≤ (m / 8) ^ a := by
  have hm0 : 0 < m := by linarith
  have hs : 0 ≤ m ^ (a * e) := Real.rpow_nonneg hm0.le _
  have hr := Real.sqrt_nonneg (m ^ (a * e))
  have hrSq := Real.sq_sqrt hs
  have hlr : (zeta / 2) * Real.sqrt (m ^ (a * e)) ≤
      Real.sqrt (m ^ (a * e)) / 64 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ 1 / 32 - zeta) hr]
  have hr64 : 64 < Real.sqrt (m ^ (a * e)) := by linarith
  have hbig : 4096 < m ^ (a * e) := by nlinarith
  have hae : a * e ≤ a := by nlinarith
  have hpow : m ^ (a * e) ≤ m ^ a := Real.rpow_le_rpow_of_exponent_le hm hae
  have hpow' : m ^ a ≤ m := by
    simpa using Real.rpow_le_rpow_of_exponent_le hm ha1
  have h8 : (8 : Real) ^ a ≤ 8 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) ≤ 8) ha1
  have hdecomp : m ^ a = (8 : Real) ^ a * (m / 8) ^ a := by
    rw [← Real.mul_rpow (by norm_num : (0 : Real) ≤ 8) (by positivity : 0 ≤ m / 8)]
    congr 1
    ring
  have hsmall : m ^ a ≤ 8 * (m / 8) ^ a := by
    rw [hdecomp]
    exact mul_le_mul_of_nonneg_right h8 (Real.rpow_nonneg (by positivity : 0 ≤ m / 8) a)
  constructor <;> linarith

end LeanProofs.GowersSzemeredi
