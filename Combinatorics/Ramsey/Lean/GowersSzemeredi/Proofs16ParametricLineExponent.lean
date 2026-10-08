import GowersSzemeredi.Proofs16CubicUniformControls

/-! Power form and uniform count control for the parametric line width.
These estimates keep the spectrum exponent explicit, so a cubic spectrum
provider can be used without restoring the original sequential loss. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

def lemma9WidthWithExponent (q k : Nat) (sigma theta gamma a : Real) : Real :=
  (multipleC (sigma / (2 * section16Lemma9R theta gamma k)) gamma (k + 1)) ^
    section16Lemma9R theta gamma k * (a * section16RecurrenceExponent k q) / 2

theorem lemma9WidthWith_eq_power (m q k : Nat) (sigma theta gamma a zeta : Real) :
    lemma9WidthWith m q k sigma theta gamma a zeta =
      (zeta / 2) * (m : Real) ^ lemma9WidthWithExponent q k sigma theta gamma a := by
  simp only [lemma9WidthWith, lemma9WidthWithExponent, Real.sqrt_eq_rpow,
    ← Real.rpow_mul (Nat.cast_nonneg m), div_eq_mul_inv, one_mul]

theorem lemma9WidthWithExponent_pos {k : Nat} (hk : 0 < k)
    {sigma theta gamma a : Real} (hs : 0 < sigma) (ht : 0 < theta)
    (hg : 0 < gamma) (ha : 0 < a) (q : Nat) :
    0 < lemma9WidthWithExponent q k sigma theta gamma a := by
  have hr : 0 < section16Lemma9R theta gamma k := by
    have htwo : 1 < (2 : Nat) ^ k := one_lt_pow₀ (by norm_num) hk.ne'
    have hn : (0 : Real) < ((2 ^ k - 1 : Nat) : Real) :=
      by exact_mod_cast (show 0 < 2 ^ k - 1 by omega)
    unfold section16Lemma9R multipleS
    positivity
  have he := (section16RecurrenceExponent_pos_le_one k q).1
  unfold lemma9WidthWithExponent multipleC
  positivity

theorem lemma9WidthWithExponent_antitone_count (k : Nat) (sigma theta gamma : Real)
    {a : Real} (ha : 0 ≤ a) :
    Antitone (fun q => lemma9WidthWithExponent q k sigma theta gamma a) := by
  intro q Q hqQ
  unfold lemma9WidthWithExponent
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg _ _)
  · exact mul_le_mul_of_nonneg_left (section16RecurrenceExponent_antitone k hqQ) ha
  · exact (even_two.pow_of_ne_zero
      (by positivity : (2 : Nat) ^ (k + 1 + 8) ≠ 0)).pow_nonneg _

theorem lemma9WidthWith_uniform_count {m q Q k : Nat} {sigma theta gamma a zeta : Real}
    (hm : 1 ≤ m) (hqQ : q ≤ Q) (ha : 0 ≤ a) (hz : 0 ≤ zeta) :
    (zeta / 2) * (m : Real) ^ lemma9WidthWithExponent Q k sigma theta gamma a ≤
      lemma9WidthWith m q k sigma theta gamma a zeta := by
  rw [lemma9WidthWith_eq_power]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm)
    (lemma9WidthWithExponent_antitone_count k sigma theta gamma ha hqQ)

end LeanProofs.GowersSzemeredi
