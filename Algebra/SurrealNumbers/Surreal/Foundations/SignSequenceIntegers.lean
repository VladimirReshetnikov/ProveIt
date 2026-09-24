import Surreal.Foundations.SignSequenceAddGroup
import Surreal.Foundations.SignSequenceBounds
import Mathlib.Algebra.Order.Ring.Cast
import Mathlib.Data.Int.Cast.Lemmas

/-!
# Finite integers in the additive sign carrier

The one-plus sequence is `1`. Native natural-number casts for the
constructed Conway addition are precisely the finite all-plus sequences;
integer casts give an injective, order-preserving additive embedding.
No multiplication, field structure, rational embedding, or Archimedean
property is assumed.

The final results prove the subtraction-by-one argument in
`found:prop:incomplete` for the native natural-number range and identify it
with the earlier finite-ordinal witness.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

@[simp] theorem ofOrdinal_zero : ofOrdinal (0 : Ordinal.{u}) = 0 := by
  apply ext
  intro i
  simp [signAt_ofOrdinal]

/-- The one-plus sequence, compatible with the forthcoming multiplicative
unit but defined here using only the sign carrier. -/
instance signSequenceOne : One SignSequence.{u} := ⟨ofOrdinal 1⟩

theorem one_eq_ofOrdinal : (1 : SignSequence.{u}) = ofOrdinal 1 := rfl

theorem zero_lt_one : (0 : SignSequence.{u}) < 1 := by
  rw [one_eq_ofOrdinal, ← ofOrdinal_zero]
  exact ofOrdinal_strictMono (by simp)

instance signSequenceZeroLEOneClass : ZeroLEOneClass SignSequence.{u} := ⟨zero_lt_one.le⟩

instance signSequenceOneNeZero : NeZero (1 : SignSequence.{u}) := ⟨zero_lt_one.ne'⟩

/-- Truncating an all-plus sequence keeps it all-plus. -/
theorem truncate_ofOrdinal (a b : Ordinal.{u}) (hb : b ≤ a) :
    truncate (ofOrdinal a) b hb = ofOrdinal b := by
  apply ext
  intro i
  by_cases hi : i < b
  · simp [signAt_truncate, signAt_ofOrdinal, hi, hi.trans_le hb]
  · simp [signAt_truncate, signAt_ofOrdinal, hi]

/-- Canonical left options of an ordinal are precisely its earlier
all-plus truncations. -/
theorem leftOption_ofOrdinal (a : Ordinal.{u}) (i : LeftIndex (ofOrdinal a)) :
    leftOption (ofOrdinal a) i = ofOrdinal i.val.val :=
  truncate_ofOrdinal a _ i.val.property.le

/-- An all-plus sequence has no canonical right option. -/
theorem rightIndex_ofOrdinal_false (a : Ordinal.{u}) (i : RightIndex (ofOrdinal a)) : False := by
  have h := i.property
  have hi : i.val.val < a := i.val.property
  rw [signAt_ofOrdinal, if_pos hi] at h
  exact (by decide : (1 : SignType) ≠ -1) h

/-- A singleton lower option with no upper options. -/
def ordinalSuccCut (a : Ordinal.{u}) :
    SmallCutData.{u, u + 1} SignSequence.{u} (· < ·) where
  Left := PUnit
  Right := PEmpty
  left _ := ofOrdinal a
  right := PEmpty.elim
  separated _ i := PEmpty.elim i

@[simp] theorem ordinalSuccCut_realizes_iff (a : Ordinal.{u}) (z : SignSequence.{u}) :
    (ordinalSuccCut a).IsRealizedBy z ↔ ofOrdinal a < z := by
  simp [SmallCutData.IsRealizedBy, ordinalSuccCut]

/-- The simplest sequence strictly above an ordinal is its successor. -/
@[simp] theorem cut_ordinalSuccCut (a : Ordinal.{u}) :
    cut (ordinalSuccCut a) = ofOrdinal (a + 1) := by
  apply IsPrefix.antisymm
  · apply cut_isPrefix
    exact (ordinalSuccCut_realizes_iff _ _).mpr
      (ofOrdinal_strictMono (Order.lt_succ a))
  · apply isPrefix_of_separates_options
    · intro i
      rw [leftOption_ofOrdinal]
      have hi : i.val.val ≤ a := Order.lt_succ_iff.mp i.val.property
      exact (ofOrdinal_strictMono.monotone hi).trans_lt
        ((ordinalSuccCut_realizes_iff _ _).mp (cut_realizes _))
    · intro i
      exact (rightIndex_ofOrdinal_false _ i).elim

/-- Adding the one-plus sequence to a finite ordinal gives its successor,
as a theorem about actual Conway addition. -/
theorem ofOrdinal_nat_add_one (n : ℕ) :
    ofOrdinal (n : Ordinal.{u}) + 1 = ofOrdinal ((n + 1 : ℕ) : Ordinal.{u}) := by
  induction n with
  | zero => simp [one_eq_ofOrdinal]
  | succ n ih =>
    have hsum : ofOrdinal ((n + 1 : ℕ) : Ordinal.{u}) + 1 =
        cut (sumCut (ordinalSuccCut (n : Ordinal.{u})) (ordinalSuccCut 0)) := by
      rw [cut_sumCut, cut_ordinalSuccCut, cut_ordinalSuccCut]
      simp only [Nat.cast_add, Nat.cast_one, _root_.zero_add, one_eq_ofOrdinal]
    rw [hsum]
    calc
      cut (sumCut (ordinalSuccCut (n : Ordinal.{u})) (ordinalSuccCut 0)) =
          cut (ordinalSuccCut ((n + 1 : ℕ) : Ordinal.{u})) := by
        apply cut_congr
        intro z
        rw [sumCut_realizes_iff, ordinalSuccCut_realizes_iff]
        simp only [cut_ordinalSuccCut, _root_.zero_add, ← one_eq_ofOrdinal]
        simp [ordinalSuccCut, ih, Nat.cast_add, Nat.cast_one]
      _ = ofOrdinal ((n + 1 + 1 : ℕ) : Ordinal.{u}) := by
        simp only [cut_ordinalSuccCut, Nat.cast_add, Nat.cast_one]

/-- The native casts use the constructed additive group and the one-plus
sequence, without installing any multiplication. -/
instance signSequenceAddCommGroupWithOne : AddCommGroupWithOne SignSequence.{u} where
  __ := signSequenceAddCommGroup
  one := 1

/-- Native natural numbers agree exactly with finite all-plus sequences. -/
theorem natCast_eq_ofOrdinal (n : ℕ) :
    (n : SignSequence.{u}) = ofOrdinal (n : Ordinal.{u}) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ, ih, ofOrdinal_nat_add_one]

/-- A negative integer is the corresponding finite all-minus sequence. -/
theorem intCast_negSucc_eq_neg_ofOrdinal (n : ℕ) :
    (Int.negSucc n : SignSequence.{u}) = -ofOrdinal ((n + 1 : ℕ) : Ordinal.{u}) := by
  rw [Int.cast_negSucc, natCast_eq_ofOrdinal]

/-- The birthday of a native natural number is its finite ordinal. -/
@[simp] theorem birthday_natCast (n : ℕ) :
    (n : SignSequence.{u}).birthday = (n : Ordinal.{u}) := by
  rw [natCast_eq_ofOrdinal, birthday_ofOrdinal]

instance signSequenceCharZero : CharZero SignSequence.{u} where
  cast_injective m n h := by
    rw [natCast_eq_ofOrdinal, natCast_eq_ofOrdinal] at h
    exact Nat.cast_injective (ofOrdinal_strictMono.injective h)

/-- Natural-number casts preserve and reflect the numerical order. -/
theorem natCast_strictMono : StrictMono (Nat.cast : ℕ → SignSequence.{u}) :=
  Nat.strictMono_cast

/-- Integer casts preserve and reflect numerical order; no Archimedean
property is used. -/
theorem intCast_strictMono : StrictMono (Int.cast : ℤ → SignSequence.{u}) :=
  Int.cast_strictMono

/-- The ordered additive integer embedding, as a native additive homomorphism. -/
def integerAddHom : ℤ →+ SignSequence.{u} := Int.castAddHom _

theorem integerAddHom_injective : Function.Injective (integerAddHom : ℤ → SignSequence.{u}) :=
  intCast_strictMono.injective

/-- The same integer embedding bundled with its order preservation. -/
def integerOrderEmbedding : ℤ ↪o SignSequence.{u} :=
  OrderEmbedding.ofStrictMono Int.cast intCast_strictMono

/-- The two natural-number witnesses now define the very same subset. -/
theorem range_natCast_eq_finite_ordinals :
    Set.range (Nat.cast : ℕ → SignSequence.{u}) =
      Set.range (fun n : ℕ => ofOrdinal (n : Ordinal.{u})) := by
  congr 1
  exact funext natCast_eq_ofOrdinal

/-- The all-plus sequence of length `ω` is the explicit strict upper bound
of the natural numbers used in `found:prop:incomplete`. -/
theorem natCast_lt_omega0 (n : ℕ) :
    (n : SignSequence.{u}) < ofOrdinal Ordinal.omega0 := by
  rw [natCast_eq_ofOrdinal]
  exact ofOrdinal_strictMono (Ordinal.natCast_lt_omega0 n)

/-- The concrete subtraction-by-one proof of `found:prop:incomplete`: an
upper bound of the native natural numbers remains an upper bound after
subtracting one, and is strictly decreased. -/
theorem sub_one_mem_upperBounds_natCast {b : SignSequence.{u}}
    (hb : b ∈ upperBounds (Set.range (Nat.cast : ℕ → SignSequence.{u}))) :
    b - 1 ∈ upperBounds (Set.range (Nat.cast : ℕ → SignSequence.{u})) ∧ b - 1 < b := by
  constructor
  · rintro x ⟨n, rfl⟩
    apply le_sub_iff_add_le.mpr
    simpa only [Nat.cast_add, Nat.cast_one] using hb (Set.mem_range_self (n + 1))
  · exact sub_lt_self b zero_lt_one

/-- The native natural-number range has no least upper bound. -/
theorem natCast_range_no_isLUB :
    ¬ ∃ b : SignSequence.{u}, IsLUB (Set.range (Nat.cast : ℕ → SignSequence.{u})) b := by
  rintro ⟨b, hb⟩
  obtain ⟨hbound, hlt⟩ := sub_one_mem_upperBounds_natCast hb.1
  exact hlt.not_ge (hb.2 hbound)

/-- The additive natural-number range is a nonempty bounded set without a
supremum, identical to the finite-ordinal witness. -/
theorem natural_numbers_bounded_without_supremum :
    let s := Set.range (Nat.cast : ℕ → SignSequence.{u})
    s.Nonempty ∧ BddAbove s ∧ ¬ ∃ b, IsLUB s b := by
  dsimp only
  rw [range_natCast_eq_finite_ordinals]
  exact finite_ordinals_bounded_without_supremum

end

end Surreal.Foundations.SignSequence
