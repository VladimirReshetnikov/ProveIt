import Surreal.Foundations.SignSequenceField
import CombinatorialGames.Surreal.Ordinal

/-!
# Ordinal signs and Hessenberg arithmetic

The all-plus sign sequence of length `a` has literally the same raw game
as the upstream ordinal embedding. Consequently the arithmetic on these
signs agrees with the natural (Hessenberg) sum and product supplied by
`NatOrdinal`, as asserted in `found:rem:ordinals`.

The usual ordinal operations remain distinct: `1 + omega` is `omega` for
ordinary ordinal addition, but is the successor of `omega` in this field.
No arithmetic instance on `Ordinal` is replaced or used as a field
homomorphism.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

/-- All-plus signs and the upstream ordinal embedding agree even before
passing to numerical equivalence classes of games. -/
@[simp] theorem toIGame_ofOrdinal (a : Ordinal.{u}) :
    toIGame (ofOrdinal a) = NatOrdinal.toIGame (NatOrdinal.of a) := by
  induction a using WellFoundedLT.induction with
  | ind a ih =>
    apply IGame.ext
    intro p
    cases p with
    | left =>
      rw [leftMoves_toIGame, NatOrdinal.leftMoves_toIGame]
      apply Set.Subset.antisymm
      · rintro _ ⟨i, rfl⟩
        dsimp only
        rw [leftOption_ofOrdinal, ih _ i.val.property]
        exact ⟨NatOrdinal.of i.val.val, i.val.property, rfl⟩
      · rintro _ ⟨b, hb, rfl⟩
        have hb' : NatOrdinal.val b < a := hb
        let i : LeftIndex (ofOrdinal a) :=
          ⟨⟨NatOrdinal.val b, hb'⟩, by simp [signAt_ofOrdinal, hb']⟩
        refine ⟨i, ?_⟩
        dsimp only
        rw [leftOption_ofOrdinal, ih _ hb']
        rfl
    | right =>
      rw [rightMoves_toIGame, NatOrdinal.rightMoves_toIGame]
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro _ ⟨i, rfl⟩
      exact rightIndex_ofOrdinal_false a i

/-- The sign/game isomorphism preserves the canonical ordinal embedding. -/
@[simp] theorem toSurreal_ofOrdinal (a : Ordinal.{u}) :
    toSurreal (ofOrdinal a) = NatOrdinal.toSurreal (NatOrdinal.of a) := by
  apply _root_.Surreal.mk_eq_mk.mpr
  change toIGame (ofOrdinal a) ≈ NatOrdinal.toIGame (NatOrdinal.of a)
  rw [toIGame_ofOrdinal]

/-- The sum of embedded ordinals is their Hessenberg natural sum. -/
theorem ofOrdinal_natural_add (a b : Ordinal.{u}) :
    ofOrdinal (NatOrdinal.val (NatOrdinal.of a + NatOrdinal.of b)) =
      ofOrdinal a + ofOrdinal b := by
  apply (toSurreal_inj _ _).mp
  simp only [toSurreal_ofOrdinal, NatOrdinal.of_val, toSurreal_add, NatOrdinal.toSurreal_add]

/-- The product of embedded ordinals is their Hessenberg natural product. -/
theorem ofOrdinal_natural_mul (a b : Ordinal.{u}) :
    ofOrdinal (NatOrdinal.val (NatOrdinal.of a * NatOrdinal.of b)) =
      ofOrdinal a * ofOrdinal b := by
  apply (toSurreal_inj _ _).mp
  simp only [toSurreal_ofOrdinal, NatOrdinal.of_val, toSurreal_mul, NatOrdinal.toSurreal_mul]

/-- The ordinal embedding is an ordered semiring homomorphism when its
domain explicitly carries natural, rather than usual, ordinal arithmetic. -/
def naturalOrdinalRingHom : NatOrdinal.{u} →+*o SignSequence.{u} where
  toFun a := ofOrdinal (NatOrdinal.val a)
  map_zero' := ofOrdinal_zero
  map_one' := one_eq_ofOrdinal.symm
  map_add' a b := by simpa only [NatOrdinal.of_val] using
    ofOrdinal_natural_add (NatOrdinal.val a) (NatOrdinal.val b)
  map_mul' a b := by simpa only [NatOrdinal.of_val] using
    ofOrdinal_natural_mul (NatOrdinal.val a) (NatOrdinal.val b)
  monotone' := ofOrdinal_strictMono.monotone.comp NatOrdinal.val.monotone

@[simp] theorem naturalOrdinalRingHom_apply (a : NatOrdinal.{u}) :
    naturalOrdinalRingHom a = ofOrdinal (NatOrdinal.val a) := rfl

theorem naturalOrdinalRingHom_injective :
    Function.Injective (naturalOrdinalRingHom : NatOrdinal.{u} → SignSequence.{u}) :=
  ofOrdinal_strictMono.injective.comp NatOrdinal.val.injective

/-- Adding one to any embedded ordinal gives its ordinal successor. -/
theorem ofOrdinal_add_one (a : Ordinal.{u}) :
    ofOrdinal a + 1 = ofOrdinal (a + 1) := by
  rw [one_eq_ofOrdinal, ← ofOrdinal_natural_add]
  simp only [NatOrdinal.of_one, ← NatOrdinal.of_add_one, NatOrdinal.val_of]

/-- In the field, `1 + omega` is `omega + 1`, the successor ordinal sign. -/
theorem one_add_ofOrdinal_omega0 :
    1 + ofOrdinal (Ordinal.omega0 : Ordinal.{u}) = ofOrdinal (Ordinal.omega0 + 1) := by
  rw [_root_.add_comm, ofOrdinal_add_one]

theorem one_add_ofOrdinal_omega0_ne :
    1 + ofOrdinal (Ordinal.omega0 : Ordinal.{u}) ≠ ofOrdinal Ordinal.omega0 :=
  ne_of_gt (lt_add_of_pos_left _ zero_lt_one)

/-- The concrete failure of preservation of ordinary ordinal addition. -/
theorem ofOrdinal_one_add_omega0_ne :
    ofOrdinal ((1 : Ordinal.{u}) + Ordinal.omega0) ≠
      ofOrdinal 1 + ofOrdinal Ordinal.omega0 := by
  rw [Ordinal.one_add_omega0, ← one_eq_ofOrdinal]
  exact one_add_ofOrdinal_omega0_ne.symm

/-- The all-plus embedding cannot be a homomorphism for the usual ordinal
addition, despite preserving the order and the natural operations. -/
theorem not_ofOrdinal_preserves_ordinal_add :
    ¬ ∀ a b : Ordinal.{u}, ofOrdinal (a + b) = ofOrdinal a + ofOrdinal b := by
  intro h
  exact ofOrdinal_one_add_omega0_ne (h 1 Ordinal.omega0)

end

end Surreal.Foundations.SignSequence
