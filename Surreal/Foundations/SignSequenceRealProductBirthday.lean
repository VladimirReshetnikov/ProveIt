import Surreal.Foundations.SignSequenceDyadicBirthday
import Surreal.Foundations.SignSequenceRealBirthday
import Surreal.Foundations.DyadicBirthdayProduct

/-!
# The real scalar product birthday bound

This proves `lem:realproduct` in
`docs/surreal/gonshor-laurent-birthdays/article.tex` for the actual ordinary
real embedding in the sign field. Finite dyadic birthdays are controlled
by their ceilings and reduced denominators. A nondyadic factor has birthday
`ω`, while every real product has birthday at most `ω`.

The bound uses `NatOrdinal` multiplication, namely Hessenberg natural
multiplication, rather than ordinary ordinal multiplication.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

/-- Only the empty sign sequence has birthday zero. -/
@[simp] theorem birthday_eq_zero_iff (x : SignSequence.{u}) :
    x.birthday = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply ext
    intro i
    change x.signAt i = 0
    exact (x.signAt_eq_zero_iff i).mpr (by rw [h]; exact bot_le)
  · rintro rfl
    exact birthday_zero

/-- A nonzero ordinary real has a positive, hence at least one, birthday. -/
theorem one_le_birthday_ofReal {r : ℝ} (hr : r ≠ 0) :
    1 ≤ NatOrdinal.of (ofReal r : SignSequence.{u}).birthday := by
  apply Order.one_le_iff_ne_zero.mpr
  intro h
  have hb : (ofReal r : SignSequence.{u}).birthday = 0 := h
  have he := (birthday_eq_zero_iff _).mp hb
  rw [← ofReal_zero] at he
  exact hr ((ofReal_inj _ _).mp he)

private theorem dyadic_product_bound_of_height (p q : Dyadic)
    (h : DyadicBirthdayArithmetic.height (p * q) ≤
      DyadicBirthdayArithmetic.height p * DyadicBirthdayArithmetic.height q) :
    NatOrdinal.of ((p.toRat : SignSequence.{u}) * (q.toRat : SignSequence.{u})).birthday ≤
      NatOrdinal.of (p.toRat : SignSequence.{u}).birthday *
        NatOrdinal.of (q.toRat : SignSequence.{u}).birthday := by
  rw [← Rat.cast_mul, ← Dyadic.toRat_mul]
  simp only [birthday_dyadicCast_formula, NatOrdinal.of_natCast]
  change (DyadicBirthdayArithmetic.height (p * q) : NatOrdinal.{u}) ≤
    (DyadicBirthdayArithmetic.height p : NatOrdinal.{u}) *
      (DyadicBirthdayArithmetic.height q : NatOrdinal.{u})
  exact_mod_cast h

private theorem real_product_bound_of_nondyadic_left (r s : ℝ)
    (hr : ¬∃ q : Dyadic, (q.toRat : ℝ) = r) (hs : s ≠ 0) :
    NatOrdinal.of (ofReal r * ofReal s : SignSequence.{u}).birthday ≤
      NatOrdinal.of (ofReal r : SignSequence.{u}).birthday *
        NatOrdinal.of (ofReal s : SignSequence.{u}).birthday := by
  have hb : NatOrdinal.of (ofReal r * ofReal s : SignSequence.{u}).birthday ≤
      NatOrdinal.of Ordinal.omega0 := by
    rw [← ofReal_mul]
    exact birthday_ofReal_le_omega0 (r * s)
  rw [← birthday_ofReal_eq_omega0_of_not_dyadic r hr] at hb
  exact hb.trans (by
    simpa only [mul_one] using
      mul_le_mul_right (one_le_birthday_ofReal hs)
        (NatOrdinal.of (ofReal r : SignSequence.{u}).birthday))

private theorem real_product_bound_of_nondyadic_right (r s : ℝ)
    (hr : r ≠ 0) (hs : ¬∃ q : Dyadic, (q.toRat : ℝ) = s) :
    NatOrdinal.of (ofReal r * ofReal s : SignSequence.{u}).birthday ≤
      NatOrdinal.of (ofReal r : SignSequence.{u}).birthday *
        NatOrdinal.of (ofReal s : SignSequence.{u}).birthday := by
  simpa only [mul_comm] using real_product_bound_of_nondyadic_left s r hs hr

/-- The finite case of the product birthday bound, using the exact dyadic
formula and the proved reduced-denominator and ceiling estimates. -/
theorem birthday_dyadicCast_mul_le_natural (p q : Dyadic) :
    NatOrdinal.of ((p.toRat : SignSequence.{u}) * (q.toRat : SignSequence.{u})).birthday ≤
      NatOrdinal.of (p.toRat : SignSequence.{u}).birthday *
        NatOrdinal.of (q.toRat : SignSequence.{u}).birthday :=
  dyadic_product_bound_of_height p q (DyadicBirthdayArithmetic.height_mul_le p q)

/-- The complete real scalar product bound `lem:realproduct`. It uses
the actual sign-field product and includes zero factors and all mixtures
of dyadic and nondyadic ordinary reals. -/
theorem birthday_ofReal_mul_le_natural (r s : ℝ) :
    NatOrdinal.of (ofReal r * ofReal s : SignSequence.{u}).birthday ≤
      NatOrdinal.of (ofReal r : SignSequence.{u}).birthday *
        NatOrdinal.of (ofReal s : SignSequence.{u}).birthday := by
  by_cases hr0 : r = 0
  · simp [hr0]
  by_cases hs0 : s = 0
  · simp [hs0]
  by_cases hr : ∃ p : Dyadic, (p.toRat : ℝ) = r
  · by_cases hs : ∃ q : Dyadic, (q.toRat : ℝ) = s
    · obtain ⟨p, rfl⟩ := hr
      obtain ⟨q, rfl⟩ := hs
      simpa only [ofReal_ratCast] using birthday_dyadicCast_mul_le_natural p q
    · exact real_product_bound_of_nondyadic_right r s hr0 hs
  · exact real_product_bound_of_nondyadic_left r s hr hs0

/-- An ordinal-valued form of the real product bound, with the natural
product still explicitly represented by `NatOrdinal`. -/
theorem birthday_ofReal_mul_le (r s : ℝ) :
    (ofReal r * ofReal s : SignSequence.{u}).birthday ≤
      NatOrdinal.val (NatOrdinal.of (ofReal r : SignSequence.{u}).birthday *
        NatOrdinal.of (ofReal s : SignSequence.{u}).birthday) :=
  birthday_ofReal_mul_le_natural r s

end

end Surreal.Foundations.SignSequence
