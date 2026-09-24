import Surreal.Foundations.SignSequenceDyadics
import Surreal.Foundations.DyadicBirthdayArithmetic
import Surreal.Foundations.SignSequenceReal

/-!
# Exact finite birthdays of dyadic sign numbers

The finite birthday formula is `eq:realbirth` in
`docs/surreal/gonshor-laurent-birthdays/article.tex` and
`eq:dyadic-birthday` in
`docs/surreal/gonshor-product-birthdays/surreal_product_birthdays.tex`.
The dyadic neighbor cuts are related to actual sign prefixes before their
raw-game birthdays are used: equivalence of games alone does not preserve
raw birthdays.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

private theorem orderIso_symm_mk_dyadic (q : Dyadic) :
    toSurrealOrderIso.symm (_root_.Surreal.mk (Dyadic.toIGame q)) =
      (q.toRat : SignSequence.{u}) := by
  apply (toSurreal_inj _ _).mp
  rw [toSurreal_orderIso_symm, _root_.Surreal.mk_dyadic, toSurreal_ratCast]

/-- Any sign number strictly between a dyadic's two arithmetic neighbors
extends that dyadic's sign sequence. This also applies to integral dyadics,
whose raw game may omit one of these two bounds. -/
theorem dyadicCast_isPrefix_of_between (q : Dyadic) (x : SignSequence.{u})
    (hl : (q.lower.toRat : SignSequence.{u}) < x)
    (hr : x < (q.upper.toRat : SignSequence.{u})) :
    IsPrefix (q.toRat : SignSequence.{u}) x := by
  have hc : cut (numericGameSignCut (Dyadic.toIGame q)) =
      (q.toRat : SignSequence.{u}) := by
    rw [cut_numericGameSignCut, orderIso_symm_mk_dyadic]
  rw [← hc]
  apply cut_isPrefix
  constructor
  · intro i
    let a := (equivShrink ((Dyadic.toIGame q).moves .left)).symm i
    change toSurrealOrderIso.symm (_root_.Surreal.mk a.val) < x
    have ha := Dyadic.eq_lower_of_mem_leftMoves_toIGame a.property
    simp only [ha, orderIso_symm_mk_dyadic]
    exact hl
  · intro i
    let a := (equivShrink ((Dyadic.toIGame q).moves .right)).symm i
    change x < toSurrealOrderIso.symm (_root_.Surreal.mk a.val)
    have ha := Dyadic.eq_upper_of_mem_rightMoves_toIGame a.property
    simp only [ha, orderIso_symm_mk_dyadic]
    exact hr

private theorem dyadic_lt_upper_lower (q : Dyadic) (hq : q.den ≠ 1) :
    q < q.lower.upper := by
  rw [← Dyadic.coe_lt_coe, Dyadic.coe_upper, Dyadic.coe_lower]
  have h : (q.den : ℚ)⁻¹ < (q.lower.den : ℚ)⁻¹ :=
    inv_lt_inv₀ (by exact_mod_cast q.den_pos) (by exact_mod_cast q.lower.den_pos) |>.mpr
      (by exact_mod_cast Dyadic.den_lower_lt hq)
  linarith

private theorem dyadic_lower_upper_lt (q : Dyadic) (hq : q.den ≠ 1) :
    q.upper.lower < q := by
  have h := dyadic_lt_upper_lower (-q) (by simpa using hq)
  simpa only [Dyadic.lower_neg, Dyadic.upper_neg, _root_.neg_lt_neg_iff] using h

/-- The lower arithmetic neighbor of a nonintegral dyadic is a sign prefix. -/
theorem lower_dyadicCast_isPrefix (q : Dyadic) (hq : q.den ≠ 1) :
    IsPrefix (q.lower.toRat : SignSequence.{u}) (q.toRat : SignSequence.{u}) := by
  apply dyadicCast_isPrefix_of_between
  · exact_mod_cast (Dyadic.lower_lt q.lower).trans (Dyadic.lower_lt q)
  · exact_mod_cast dyadic_lt_upper_lower q hq

/-- The upper arithmetic neighbor is also a sign prefix. -/
theorem upper_dyadicCast_isPrefix (q : Dyadic) (hq : q.den ≠ 1) :
    IsPrefix (q.upper.toRat : SignSequence.{u}) (q.toRat : SignSequence.{u}) := by
  apply dyadicCast_isPrefix_of_between
  · exact_mod_cast dyadic_lower_upper_lt q hq
  · exact_mod_cast (Dyadic.lt_upper q).trans (Dyadic.lt_upper q.upper)

private theorem birthday_lt_of_isPrefix_ne {x y : SignSequence.{u}}
    (hp : IsPrefix x y) (hne : x ≠ y) : x.birthday < y.birthday := by
  apply lt_of_le_of_ne hp.1
  intro h
  apply hne
  apply hp.antisymm
  exact ⟨h.ge, fun i hi => (hp.2 i (by simpa only [h] using hi)).symm⟩

theorem birthday_lower_dyadicCast_lt (q : Dyadic) (hq : q.den ≠ 1) :
    (q.lower.toRat : SignSequence.{u}).birthday <
      (q.toRat : SignSequence.{u}).birthday := by
  apply birthday_lt_of_isPrefix_ne (lower_dyadicCast_isPrefix q hq)
  exact ne_of_lt (by exact_mod_cast Dyadic.lower_lt q)

theorem birthday_upper_dyadicCast_lt (q : Dyadic) (hq : q.den ≠ 1) :
    (q.upper.toRat : SignSequence.{u}).birthday <
      (q.toRat : SignSequence.{u}).birthday := by
  apply birthday_lt_of_isPrefix_ne (upper_dyadicCast_isPrefix q hq)
  exact ne_of_gt (by exact_mod_cast Dyadic.lt_upper q)

/-- Integral sign birthdays are the natural absolute value, including zero. -/
@[simp] theorem birthday_intCast (n : ℤ) :
    (n : SignSequence.{u}).birthday = (n.natAbs : Ordinal.{u}) := by
  cases n with
  | ofNat n =>
    change (n : SignSequence.{u}).birthday = (n : Ordinal.{u})
    exact birthday_natCast n
  | negSucc n =>
    simp only [Int.cast_negSucc, birthday_neg, birthday_natCast, Int.natAbs_negSucc]

/-- The native dyadic raw game has minimum birthday among all numeric
representatives of its value. This is proved using actual sign prefixes. -/
theorem birthday_dyadicCast_eq_game (q : Dyadic) :
    (q.toRat : SignSequence.{u}).birthday =
      NatOrdinal.val (Dyadic.toIGame.{u} q).birthday := by
  apply le_antisymm
  · exact birthday_le_of_toSurreal_eq_mk _ (Dyadic.toIGame q)
      (by rw [toSurreal_ratCast, _root_.Surreal.mk_dyadic])
  · change (Dyadic.toIGame.{u} q).birthday ≤
      NatOrdinal.of (q.toRat : SignSequence.{u}).birthday
    by_cases hq : q.den = 1
    · have he : q = (q.num : Dyadic) := (Dyadic.intCast_num_eq_self_of_den_eq_one hq).symm
      rw [he, Dyadic.toIGame_intCast, Dyadic.toRat_intCast, Rat.cast_intCast,
        birthday_intCast]
      cases q.num with
      | ofNat n => simp
      | negSucc n =>
        simp [Nat.cast_add_one_comm]
    · apply IGame.birthday_le_iff.mpr
      intro p a ha
      cases p with
      | left =>
        rw [Dyadic.eq_lower_of_mem_leftMoves_toIGame ha]
        change NatOrdinal.val (Dyadic.toIGame.{u} q.lower).birthday <
          (q.toRat : SignSequence.{u}).birthday
        rw [← birthday_dyadicCast_eq_game q.lower]
        exact birthday_lower_dyadicCast_lt q hq
      | right =>
        rw [Dyadic.eq_upper_of_mem_rightMoves_toIGame ha]
        change NatOrdinal.val (Dyadic.toIGame.{u} q.upper).birthday <
          (q.toRat : SignSequence.{u}).birthday
        rw [← birthday_dyadicCast_eq_game q.upper]
        exact birthday_upper_dyadicCast_lt q hq
termination_by q.den
decreasing_by all_goals first | exact Dyadic.den_lower_lt hq | exact Dyadic.den_upper_lt hq

/-- The exact birthday recursion for a nonintegral dyadic, now stated for
the numerical sign value rather than only its raw game representation. -/
theorem birthday_dyadicCast_eq_max (q : Dyadic) (hq : q.den ≠ 1) :
    (q.toRat : SignSequence.{u}).birthday =
      max (q.lower.toRat : SignSequence.{u}).birthday
        (q.upper.toRat : SignSequence.{u}).birthday + 1 := by
  rw [birthday_dyadicCast_eq_game, Dyadic.toIGame_of_den_ne_one hq,
    IGame.birthday_ofSets]
  simp only [Set.image_singleton, csSup_singleton, Function.comp_apply,
    Order.succ_eq_add_one]
  rw [NatOrdinal.val.monotone.map_max, NatOrdinal.val_add_one, NatOrdinal.val_add_one,
    ← birthday_dyadicCast_eq_game, ← birthday_dyadicCast_eq_game]
  rw [← max_add_add_right]

/-- Every numeric game with a given dyadic value has birthday at least
that of the native dyadic game. No canonical-form axiom is used. -/
theorem dyadic_game_birthday_minimal (q : Dyadic) (g : IGame.{u})
    [IGame.Numeric g] (h : _root_.Surreal.mk (Dyadic.toIGame q) = _root_.Surreal.mk g) :
    (Dyadic.toIGame.{u} q).birthday ≤ g.birthday := by
  have hc : toSurreal (q.toRat : SignSequence.{u}) = _root_.Surreal.mk g := by
    rw [toSurreal_ratCast, ← _root_.Surreal.mk_dyadic]
    exact h
  have hb := birthday_le_of_toSurreal_eq_mk _ g hc
  rwa [birthday_dyadicCast_eq_game] at hb

private theorem birthday_dyadicCast_eq_nat_of_recursion (f : Dyadic → ℕ)
    (hfint : ∀ q, q.den = 1 → f q = q.num.natAbs)
    (hfstep : ∀ q, q.den ≠ 1 → max (f q.lower) (f q.upper) + 1 = f q)
    (q : Dyadic) : (q.toRat : SignSequence.{u}).birthday = (f q : Ordinal.{u}) := by
  by_cases hq : q.den = 1
  · rw [hfint q hq]
    have he : q = (q.num : Dyadic) := (Dyadic.intCast_num_eq_self_of_den_eq_one hq).symm
    conv_lhs => rw [he, Dyadic.toRat_intCast, Rat.cast_intCast, birthday_intCast]
  · rw [birthday_dyadicCast_eq_max q hq,
      birthday_dyadicCast_eq_nat_of_recursion f hfint hfstep q.lower,
      birthday_dyadicCast_eq_nat_of_recursion f hfint hfstep q.upper]
    have hm : Monotone (Nat.cast : ℕ → Ordinal.{u}) := fun _ _ h => by exact_mod_cast h
    have hc := congrArg (Nat.cast : ℕ → Ordinal.{u}) (hfstep q hq)
    simpa only [Nat.cast_add, Nat.cast_one, hm.map_max] using hc
termination_by q.den
decreasing_by all_goals first | exact Dyadic.den_lower_lt hq | exact Dyadic.den_upper_lt hq

/-- The exact finite birthday formula `eq:realbirth` /
`eq:dyadic-birthday`. The logarithm is the exponent of the reduced
power-of-two denominator. The formula also holds at zero. -/
theorem birthday_dyadicCast_formula (q : Dyadic) :
    (q.toRat : SignSequence.{u}).birthday =
      ((Nat.ceil |q.toRat| + Nat.log 2 q.den : ℕ) : Ordinal.{u}) :=
  birthday_dyadicCast_eq_nat_of_recursion DyadicBirthdayArithmetic.height
    (fun _ h => DyadicBirthdayArithmetic.height_of_den_eq_one h)
    (fun _ h => DyadicBirthdayArithmetic.max_height_lower_upper_add_one h) q

/-- The manuscript's reduced-denominator version, with the exponent
specified explicitly rather than recovered by a natural logarithm. -/
theorem birthday_dyadicCast_of_den_eq_two_pow (q : Dyadic) (k : ℕ)
    (hq : q.den = 2 ^ k) :
    (q.toRat : SignSequence.{u}).birthday =
      ((Nat.ceil |q.toRat| + k : ℕ) : Ordinal.{u}) := by
  rw [birthday_dyadicCast_formula, hq, Nat.log_pow (by decide : 1 < 2)]

/-- The same exact formula for the constructed embedding of an ordinary
dyadic real number. -/
theorem birthday_ofReal_dyadic_formula (q : Dyadic) :
    (ofReal (q.toRat : ℝ) : SignSequence.{u}).birthday =
      ((Nat.ceil |q.toRat| + Nat.log 2 q.den : ℕ) : Ordinal.{u}) := by
  rw [ofReal_ratCast, birthday_dyadicCast_formula]

end

end Surreal.Foundations.SignSequence
