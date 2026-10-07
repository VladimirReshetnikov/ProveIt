import GowersSzemeredi.Proofs13IntegerBudgets

/-! Finite integer budgets above the singleton scale. Explicit coefficient
inequalities replace the existential asymptotic threshold. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem finite_rounded_row_budgets {c d z e u v w : Real}
    (hc : 0 < c) (hd : 0 < d) (hz : 0 < z)
    (hv : 0 < v) (hw : 0 < w) (hcsmall : 2 * c ≤ 1)
    (hsquare : 2 * e ≤ 1) (hrec : 2 * e ≤ u * v) (hbohr : 2 * e ≤ u * w)
    (hrecCoeff : 6 * c ^ 2 ≤ d ^ v) (hbohrCoeff : 2 * c ^ 2 ≤ z * d ^ w)
    (N : Nat) (hN : 1 ≤ N) (P Q : Real)
    (hlarge : 1 ≤ c * (N : Real) ^ e)
    (hP : d * (N : Real) ^ u ≤ P) (hQ : P ^ v / 2 ≤ Q) :
    ∃ m : Nat, 0 < m ∧ m ^ 2 ≤ N ∧ (m : Real) + 1 ≤ Q ∧
      c * (N : Real) ^ e ≤ m ∧ P ^ (-w) ≤ z / m := by
  have hNpos : (0 : Real) < N := by exact_mod_cast (by omega : 0 < N)
  have hNone : (1 : Real) ≤ N := by exact_mod_cast hN
  let t : Real := c * (N : Real) ^ e
  let m := Nat.ceil t
  have htpos : 0 < t := mul_pos hc (Real.rpow_pos_of_pos hNpos e)
  have htone : 1 ≤ t := hlarge
  have hmpos : 0 < m := Nat.one_le_ceil_iff.mpr htpos
  have hmlower : t ≤ (m : Real) := Nat.le_ceil t
  have hmround : (m : Real) < t + 1 := Nat.ceil_lt_add_one htpos.le
  have hmupper : (m : Real) ≤ 2 * t := by linarith only [hmround, htone]
  have hmadd : (m : Real) + 1 ≤ 3 * t := by linarith only [hmround, htone]
  have hPpos : 0 < P := (mul_pos hd (Real.rpow_pos_of_pos hNpos u)).trans_le hP
  have hpow (s : Real) : (d * (N : Real) ^ u) ^ s = d ^ s * (N : Real) ^ (u * s) := by
    rw [Real.mul_rpow hd.le (Real.rpow_nonneg hNpos.le _), ← Real.rpow_mul hNpos.le]
  have ht2 : t ^ 2 = c ^ 2 * (N : Real) ^ (2 * e) := by
    dsimp [t]
    rw [mul_pow, ← Real.rpow_mul_natCast hNpos.le]
    congr 1
    congr 1
    ring
  have hmsquare : (m : Real) ^ 2 ≤ N := by
    calc
      _ ≤ (2 * t) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hmupper 2
      _ = (2 * c) ^ 2 * (N : Real) ^ (2 * e) := by rw [mul_pow, ht2]; ring
      _ ≤ 1 * (N : Real) ^ (2 * e) := mul_le_mul_of_nonneg_right
        (by nlinarith only [hc, hcsmall] : (2 * c) ^ 2 ≤ 1) (by positivity)
      _ ≤ N := by simpa only [one_mul, Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le hNone hsquare
  have hrecScale : 6 * t ^ 2 ≤ d ^ v * (N : Real) ^ (u * v) := by
    rw [ht2]
    calc
      _ = (6 * c ^ 2) * (N : Real) ^ (2 * e) := by ring
      _ ≤ d ^ v * (N : Real) ^ (2 * e) :=
        mul_le_mul_of_nonneg_right hrecCoeff (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hNone hrec) (by positivity)
  have hbohrScale : 2 * t ^ 2 ≤ z * d ^ w * (N : Real) ^ (u * w) := by
    rw [ht2]
    calc
      _ = (2 * c ^ 2) * (N : Real) ^ (2 * e) := by ring
      _ ≤ z * d ^ w * (N : Real) ^ (2 * e) :=
        mul_le_mul_of_nonneg_right hbohrCoeff (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hNone hbohr) (by positivity)
  refine ⟨m, hmpos, ?_, ?_, hmlower, ?_⟩
  · exact_mod_cast hmsquare
  · calc
      _ ≤ 3 * t := hmadd
      _ ≤ (d * (N : Real) ^ u) ^ v / 2 := by rw [hpow]; nlinarith only [hrecScale, htone]
      _ ≤ P ^ v / 2 := div_le_div_of_nonneg_right (Real.rpow_le_rpow
        (mul_pos hd (Real.rpow_pos_of_pos hNpos u)).le hP hv.le) (by norm_num)
      _ ≤ Q := hQ
  · have hmP : (m : Real) ≤ z * P ^ w := by
      calc
        _ ≤ 2 * t := hmupper
        _ ≤ z * (d * (N : Real) ^ u) ^ w := by rw [hpow]; nlinarith only [hbohrScale, htone]
        _ ≤ z * P ^ w := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (mul_pos hd (Real.rpow_pos_of_pos hNpos u)).le hP hw.le) hz.le
    rw [Real.rpow_neg hPpos.le, ← one_div]
    apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hPpos _) (by exact_mod_cast hmpos)).mpr
    simpa only [one_mul] using hmP

end LeanProofs.GowersSzemeredi
