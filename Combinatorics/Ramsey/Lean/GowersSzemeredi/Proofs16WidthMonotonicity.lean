import GowersSzemeredi.Proofs16Lemma6

/-! # Width comparisons for applying Lemma 16.6 on a partition

Different cells may produce different delta-side graph counts. Increasing
the count only weakens the required width, so a common bounded count can be
used in Lemma 16.9. The gamma-side count remains independent.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- More frequencies decrease the recurrence exponent. -/
theorem section16RecurrenceExponent_antitone (k : Nat) :
    Antitone (section16RecurrenceExponent k) := by
  intro p q hpq
  have hK : (1 : Real) ≤ section16K k := by
    have h : 0 < section16K k := by unfold section16K; positivity
    exact_mod_cast h
  simp only [section16RecurrenceExponent, zpow_neg, zpow_natCast]
  apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
  exact pow_le_pow_right₀ hK (Nat.mul_le_mul_left _ hpq)

/-- The corrected Lemma 16.6 width is monotone in the input width. -/
theorem section16Lemma6Width_mono {m n q k : Nat} {sigma delta theta1 zeta : Real}
    (hmn : m ≤ n) (hz : 0 ≤ zeta)
    (ha : 0 ≤ (multipleC ((section16T delta theta1 k)⁻¹ * sigma) delta k) ^
      section16T delta theta1 k) :
    section16Lemma6Width m q k sigma delta theta1 zeta ≤
      section16Lemma6Width n q k sigma delta theta1 zeta := by
  rw [section16Lemma6Width_eq_sqrt, section16Lemma6Width_eq_sqrt]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.sqrt_le_sqrt
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hmn)
    (mul_nonneg ha (section16RecurrenceExponent_pos_le_one k q).1.le)

/-- Padding local delta-side counts to one common count is width-safe,
including the zero initial-width case. -/
theorem section16Lemma6Width_antitone_count {m p q k : Nat} {sigma delta theta1 zeta : Real}
    (hpq : p ≤ q) (hz : 0 ≤ zeta)
    (ha : 0 < (multipleC ((section16T delta theta1 k)⁻¹ * sigma) delta k) ^
      section16T delta theta1 k) :
    section16Lemma6Width m q k sigma delta theta1 zeta ≤
      section16Lemma6Width m p k sigma delta theta1 zeta := by
  rw [section16Lemma6Width_eq_sqrt, section16Lemma6Width_eq_sqrt]
  by_cases hm : m = 0
  · subst m
    simp only [Nat.cast_zero, Real.zero_rpow (mul_pos ha (section16RecurrenceExponent_pos_le_one k q).1).ne',
      Real.zero_rpow (mul_pos ha (section16RecurrenceExponent_pos_le_one k p).1).ne', le_refl]
  · have hm1 : (1 : Real) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.sqrt_le_sqrt
    exact Real.rpow_le_rpow_of_exponent_le hm1
      (mul_le_mul_of_nonneg_left (section16RecurrenceExponent_antitone k hpq) ha.le)

/-- Taking the Lemma 16.6 width on a cell of the gamma-side partition
produces exactly the composite exponent displayed in Lemma 16.9. -/
theorem section16Lemma9Width_le_cell_width {m n q k : Nat}
    {sigma theta gamma delta theta1 zeta : Real} (hz : 0 ≤ zeta)
    (ha : 0 ≤ (multipleC ((section16T delta theta1 k)⁻¹ * (sigma / 2)) delta k) ^
      section16T delta theta1 k)
    (hcell : (m : Real) ^ ((multipleC (sigma / (2 * section16Lemma9R theta gamma k)) gamma (k + 1)) ^
      section16Lemma9R theta gamma k) ≤ n) :
    section16Lemma9Width m q k sigma theta gamma delta theta1 zeta ≤
      section16Lemma6Width n q k (sigma / 2) delta theta1 zeta := by
  let t := section16T delta theta1 k
  let a := (multipleC (sigma / (2 * section16Lemma9R theta gamma k)) gamma (k + 1)) ^
    section16Lemma9R theta gamma k
  let b := (multipleC (sigma / (2 * t)) delta k) ^ t
  have harg : t⁻¹ * (sigma / 2) = sigma / (2 * t) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  have hb : 0 ≤ b := by
    dsimp only [b]
    rw [← harg]
    exact ha
  have he : 0 ≤ b / (2 * (section16K k : Real) ^ (2 ^ (k + 1) * q)) := by positivity
  have hleft : section16Lemma9Width m q k sigma theta gamma delta theta1 zeta =
      (zeta / 2) * ((m : Real) ^ a) ^ (b / (2 * (section16K k : Real) ^ (2 ^ (k + 1) * q))) := by
    unfold section16Lemma9Width
    dsimp only
    rw [← Real.rpow_mul (Nat.cast_nonneg m)]
    congr 2
    change a * b / _ = a * (b / _)
    ring
  have hright : section16Lemma6Width n q k (sigma / 2) delta theta1 zeta =
      (zeta / 2) * (n : Real) ^ (b / (2 * (section16K k : Real) ^ (2 ^ (k + 1) * q))) := by
    unfold section16Lemma6Width
    dsimp only
    have harg' : (sigma / 2) / t = sigma / (2 * t) := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [harg']
  rw [hleft, hright]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) _) hcell he

end LeanProofs.GowersSzemeredi
