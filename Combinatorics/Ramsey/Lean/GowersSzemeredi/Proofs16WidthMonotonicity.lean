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

theorem lemma6WidthWith_antitone_count {m p q k : Nat} {a zeta : Real}
    (hpq : p ≤ q) (hz : 0 ≤ zeta) (ha : 0 < a) :
    lemma6WidthWith m q k a zeta ≤ lemma6WidthWith m p k a zeta := by
  unfold lemma6WidthWith
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.sqrt_le_sqrt
  rcases Nat.eq_zero_or_pos m with hm0 | hm0
  · subst hm0
    have h1 := mul_pos ha ((section16RecurrenceExponent_pos_le_one k q).1)
    have h2 := mul_pos ha ((section16RecurrenceExponent_pos_le_one k p).1)
    simp [Real.zero_rpow h1.ne', Real.zero_rpow h2.ne']
  · apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm0)
    exact mul_le_mul_of_nonneg_left (section16RecurrenceExponent_antitone k hpq) ha.le

/-- Padding local delta-side counts to one common count is width-safe,
including the zero initial-width case. -/
theorem section16Lemma6Width_antitone_count {m p q k : Nat} {sigma delta theta1 zeta : Real}
    (hpq : p ≤ q) (hz : 0 ≤ zeta)
    (ha : 0 < (multipleC ((section16T delta theta1 k)⁻¹ * sigma) delta k) ^
      section16T delta theta1 k) :
    section16Lemma6Width m q k sigma delta theta1 zeta ≤
      section16Lemma6Width m p k sigma delta theta1 zeta := by
  rw [section16Lemma6Width_eq_sqrt, section16Lemma6Width_eq_sqrt]
  exact lemma6WidthWith_antitone_count hpq hz ha

/-- The Lemma 16.9 width for spectrum controls with count `q` and exponent `a`. -/
def lemma9WidthWith (m q k : Nat) (sigma theta gamma a zeta : Real) : Real :=
  (zeta / 2) * Real.sqrt ((m : Real) ^
    ((multipleC (sigma / (2 * section16Lemma9R theta gamma k)) gamma (k + 1)) ^
      section16Lemma9R theta gamma k * (a * section16RecurrenceExponent k q)))

theorem lemma9WidthWith_le_cell_width {m n q k : Nat}
    {sigma theta gamma a zeta : Real} (hz : 0 ≤ zeta) (ha : 0 ≤ a)
    (hcell : (m : Real) ^ ((multipleC (sigma / (2 * section16Lemma9R theta gamma k)) gamma
      (k + 1)) ^ section16Lemma9R theta gamma k) ≤ n) :
    lemma9WidthWith m q k sigma theta gamma a zeta ≤ lemma6WidthWith n q k a zeta := by
  unfold lemma9WidthWith lemma6WidthWith
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.sqrt_le_sqrt
  have he := (section16RecurrenceExponent_pos_le_one k q).1
  rw [Real.rpow_mul (Nat.cast_nonneg m)]
  exact Real.rpow_le_rpow (by positivity) hcell (mul_nonneg ha he.le)

/-- The printed Lemma 16.9 width is exactly the arbitrary-control width
at its printed spectrum exponent. -/
theorem section16Lemma9Width_eq_with (m q k : Nat)
    (sigma theta gamma delta theta1 zeta : Real) :
    section16Lemma9Width m q k sigma theta gamma delta theta1 zeta =
      lemma9WidthWith m q k sigma theta gamma
        ((multipleC (sigma / (2 * section16T delta theta1 k)) delta k) ^
          section16T delta theta1 k) zeta := by
  unfold section16Lemma9Width lemma9WidthWith
  dsimp only
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (Nat.cast_nonneg m)]
  congr 2
  simp only [section16RecurrenceExponent, zpow_neg, zpow_natCast, div_eq_mul_inv, mul_inv_rev]
  ring

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
  have harg : (section16T delta theta1 k)⁻¹ * (sigma / 2) =
      sigma / (2 * section16T delta theta1 k) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [section16Lemma9Width_eq_with, section16Lemma6Width_eq_sqrt]
  simpa only [lemma6WidthWith, harg] using lemma9WidthWith_le_cell_width hz ha hcell

end LeanProofs.GowersSzemeredi
