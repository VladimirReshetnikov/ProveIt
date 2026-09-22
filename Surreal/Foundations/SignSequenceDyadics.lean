import Surreal.Foundations.SignSequenceGameBirthday
import Surreal.Foundations.SignSequenceRationals
import CombinatorialGames.Surreal.Dyadic

/-!
# Finite birthdays are exactly dyadic rationals

The finite-birthday assertion of `found:sub:cutoffs` follows by combining
the canonical birthday bridge with the upstream classification of short
numeric games. These signs form a subring of the actual sign field, but
are not closed under its inverse: `3` has finite birthday and `1 / 3`
does not. Thus this birthday cutoff is not an ambient subfield.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

/-- A canonical sign game is short precisely when its sign length is
finite. -/
theorem short_toIGame_iff (x : SignSequence.{u}) :
    IGame.Short (toIGame x) ↔ x.birthday < Ordinal.omega0 := by
  rw [IGame.short_iff_birthday_finite, birthday_toIGame]
  rfl

/-- Every embedded dyadic rational has finite sign birthday. -/
theorem birthday_dyadicCast_lt_omega0 (q : Dyadic) :
    (q.toRat : SignSequence.{u}).birthday < Ordinal.omega0 := by
  have h := birthday_le_of_toSurreal_eq_mk (q.toRat : SignSequence.{u})
    (Dyadic.toIGame q) (by rw [toSurreal_ratCast, _root_.Surreal.mk_dyadic])
  exact h.trans_lt (NatOrdinal.val.strictMono (IGame.Short.birthday_lt_omega0 (Dyadic.toIGame q)))

/-- The finite-birthday sign sequences are exactly the dyadic rational
casts, including negative values and zero. -/
theorem birthday_lt_omega0_iff_dyadic (x : SignSequence.{u}) :
    x.birthday < Ordinal.omega0 ↔ ∃ q : Dyadic, (q.toRat : SignSequence.{u}) = x := by
  constructor
  · intro hx
    haveI : IGame.Short (toIGame x) := (short_toIGame_iff x).mpr hx
    refine ⟨IGame.toDyadic (toIGame x), ?_⟩
    apply (toSurreal_inj _ _).mp
    rw [toSurreal_ratCast]
    exact _root_.Surreal.ratCast_toDyadic (toIGame x)
  · rintro ⟨q, rfl⟩
    exact birthday_dyadicCast_lt_omega0 q

/-- The ordinary dyadic rational ring embedded in the actual sign field. -/
def dyadicRingHom : Dyadic →+* SignSequence.{u} :=
  (Rat.castHom _).comp Dyadic.coeRingHom

@[simp] theorem dyadicRingHom_apply (q : Dyadic) :
    dyadicRingHom q = (q.toRat : SignSequence.{u}) := rfl

theorem dyadicRingHom_injective :
    Function.Injective (dyadicRingHom : Dyadic → SignSequence.{u}) :=
  Rat.cast_injective.comp (fun _ _ h => Dyadic.toRat_inj.mp h)

/-- The finite-birthday fragment inherits the ring operations of the
ambient sign field. -/
def finiteBirthdaySubring : Subring SignSequence.{u} := dyadicRingHom.range

@[simp] theorem mem_finiteBirthdaySubring (x : SignSequence.{u}) :
    x ∈ finiteBirthdaySubring ↔ x.birthday < Ordinal.omega0 :=
  (birthday_lt_omega0_iff_dyadic x).symm

/-- Finite sign birthdays are closed under addition. -/
theorem birthday_add_lt_omega0 {x y : SignSequence.{u}}
    (hx : x.birthday < Ordinal.omega0) (hy : y.birthday < Ordinal.omega0) :
    (x + y).birthday < Ordinal.omega0 :=
  (mem_finiteBirthdaySubring _).mp (finiteBirthdaySubring.add_mem
    ((mem_finiteBirthdaySubring _).mpr hx) ((mem_finiteBirthdaySubring _).mpr hy))

/-- Finite sign birthdays are closed under multiplication. -/
theorem birthday_mul_lt_omega0 {x y : SignSequence.{u}}
    (hx : x.birthday < Ordinal.omega0) (hy : y.birthday < Ordinal.omega0) :
    (x * y).birthday < Ordinal.omega0 :=
  (mem_finiteBirthdaySubring _).mp (finiteBirthdaySubring.mul_mem
    ((mem_finiteBirthdaySubring _).mpr hx) ((mem_finiteBirthdaySubring _).mpr hy))

private theorem dyadic_toRat_ne_one_third (q : Dyadic) : q.toRat ≠ 1 / 3 := by
  intro h
  have hd : q.den = 3 := by
    change q.toRat.den = 3
    rw [h, one_div, Rat.inv_ofNat_den]
  have he := Dyadic.even_den (x := q) (by rw [hd]; decide)
  rw [hd] at he
  exact (by decide : ¬Even (3 : ℕ)) he

/-- The reciprocal of three is not dyadic, hence its birthday is not
finite. The denominator argument takes place in `ℚ`. -/
theorem not_birthday_one_third_lt_omega0 :
    ¬(1 / 3 : SignSequence.{u}).birthday < Ordinal.omega0 := by
  intro h
  obtain ⟨q, hq⟩ := (birthday_lt_omega0_iff_dyadic _).mp h
  have hq' : (q.toRat : SignSequence.{u}) = ((1 / 3 : ℚ) : SignSequence.{u}) := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hq
  exact dyadic_toRat_ne_one_third q (Rat.cast_injective hq')

/-- The explicit inverse-closure counterexample for the finite cutoff. -/
theorem three_finite_birthday_inverse_not :
    (3 : SignSequence.{u}).birthday < Ordinal.omega0 ∧
      ¬((3 : SignSequence.{u})⁻¹).birthday < Ordinal.omega0 := by
  constructor
  · change ((3 : ℕ) : SignSequence.{u}).birthday < Ordinal.omega0
    rw [birthday_natCast]
    exact Ordinal.natCast_lt_omega0 3
  · simpa only [one_div] using not_birthday_one_third_lt_omega0.{u}

/-- No ambient subfield has exactly the finite-birthday sign sequences
as its elements. This concerns the actual field operations. -/
theorem not_exists_subfield_finite_birthday :
    ¬∃ K : Subfield SignSequence.{u}, ∀ x, x ∈ K ↔ x.birthday < Ordinal.omega0 := by
  rintro ⟨K, hK⟩
  have h3 := (hK 3).mpr three_finite_birthday_inverse_not.1
  exact three_finite_birthday_inverse_not.2 ((hK _).mp (K.inv_mem h3))

end

end Surreal.Foundations.SignSequence
