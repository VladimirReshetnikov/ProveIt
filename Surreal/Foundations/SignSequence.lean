import Surreal.Foundations.SizeObstructions
import Mathlib.Data.Sign.Defs
import Mathlib.Order.PiLex
import Mathlib.SetTheory.Ordinal.Family

/-!
# The universe-indexed sign-sequence carrier

This begins the independent foundational track in `found:sub:signs`.
A sequence has an ordinal birthday, with signs `-1` or `1` before that
birthday and termination `0` afterwards. The zero extension makes the
first-disagreement order a direct instance of Mathlib's lexicographic
order. It does not supply field arithmetic or identify Hahn series with
surreal numbers.

Ordinals and the whole carrier live one universe above their bounded
fragments. The bounds and smallness results below formalize the size
claims in `found:prop:proper` with explicit universe levels.
-/

universe u v

namespace Surreal.Foundations

/-- An ordinal-length sign sequence, represented by its zero extension.
Nonzero `SignType` values are precisely the two signs. -/
structure SignSequence : Type (u + 1) where
  birthday : Ordinal.{u}
  signAt : Ordinal.{u} → SignType
  signAt_ne_zero_iff : ∀ i, signAt i ≠ 0 ↔ i < birthday

namespace SignSequence

noncomputable section

@[simp] theorem signAt_eq_zero_iff (x : SignSequence.{u}) (i : Ordinal.{u}) :
    x.signAt i = 0 ↔ x.birthday ≤ i := by
  simpa only [not_not, not_lt] using (x.signAt_ne_zero_iff i).not

/-- The zero extension determines the birthday as well as every sign. -/
theorem signAt_injective : Function.Injective (signAt : SignSequence.{u} → _) := by
  intro x y h
  have hb : x.birthday = y.birthday := by
    apply le_antisymm
    · by_contra! hlt
      have hn := (x.signAt_ne_zero_iff y.birthday).mpr hlt
      rw [h] at hn
      exact hn ((y.signAt_eq_zero_iff _).mpr le_rfl)
    · by_contra! hlt
      have hn := (y.signAt_ne_zero_iff x.birthday).mpr hlt
      rw [← h] at hn
      exact hn ((x.signAt_eq_zero_iff _).mpr le_rfl)
  cases x
  cases y
  cases hb
  cases h
  rfl

@[ext] theorem ext {x y : SignSequence.{u}}
    (h : ∀ i, x.signAt i = y.signAt i) : x = y :=
  signAt_injective (funext h)

/-- Numerical comparison uses `-1 < termination < 1` at the first
disagreement, not birthday comparison. -/
instance : LinearOrder SignSequence.{u} :=
  LinearOrder.lift' (fun x => toLex x.signAt) signAt_injective

/-- The order is exactly the first-disagreement rule in `found:sub:signs`. -/
theorem lt_iff (x y : SignSequence.{u}) :
    x < y ↔ ∃ i, (∀ j < i, x.signAt j = y.signAt j) ∧ x.signAt i < y.signAt i :=
  Iff.rfl

/-- The empty sign sequence. -/
instance : Zero SignSequence.{u} :=
  ⟨⟨0, fun _ => 0, by simp⟩⟩

instance : Inhabited SignSequence.{u} := ⟨0⟩

@[simp] theorem birthday_zero : (0 : SignSequence.{u}).birthday = 0 := rfl
@[simp] theorem signAt_zero (i : Ordinal.{u}) : (0 : SignSequence.{u}).signAt i = 0 := rfl

/-- The all-plus sequence representing an ordinal. No arithmetic
homomorphism is asserted: ordinal arithmetic is a separate structure. -/
def ofOrdinal (a : Ordinal.{u}) : SignSequence.{u} where
  birthday := a
  signAt i := if i < a then 1 else 0
  signAt_ne_zero_iff i := by split_ifs <;> simp_all

@[simp] theorem birthday_ofOrdinal (a : Ordinal.{u}) : (ofOrdinal a).birthday = a := rfl

@[simp] theorem signAt_ofOrdinal (a i : Ordinal.{u}) :
    (ofOrdinal a).signAt i = if i < a then 1 else 0 := rfl

/-- Every arbitrary two-sign sequence of ordinal length gives an element
of the carrier. `true` denotes plus and `false` denotes minus. -/
def ofSigns (a : Ordinal.{u}) (s : Set.Iio a → Bool) : SignSequence.{u} where
  birthday := a
  signAt i := if hi : i < a then if s ⟨i, hi⟩ then 1 else -1 else 0
  signAt_ne_zero_iff i := by
    by_cases hi : i < a
    · simp only [dif_pos hi]
      cases s ⟨i, hi⟩ <;> simp [hi]
    · simp [hi]

@[simp] theorem birthday_ofSigns (a : Ordinal.{u}) (s : Set.Iio a → Bool) :
    (ofSigns a s).birthday = a := rfl

@[simp] theorem signAt_ofSigns (a : Ordinal.{u}) (s : Set.Iio a → Bool)
    (i : Set.Iio a) : (ofSigns a s).signAt i = if s i then 1 else -1 := by
  exact dif_pos i.property

/-- The ordinal embedding preserves the canonical order. -/
theorem ofOrdinal_strictMono : StrictMono (ofOrdinal : Ordinal.{u} → SignSequence.{u}) := by
  intro a b hab
  apply (lt_iff _ _).mpr
  refine ⟨a, ?_, ?_⟩
  · intro j hj
    simp [signAt_ofOrdinal, hj, hj.trans hab]
  · simp [signAt_ofOrdinal, hab]

/-- An all-plus sequence whose birthday exceeds that of `x` lies above
`x` numerically. This compares two distinct notions of order explicitly. -/
theorem lt_ofOrdinal_of_birthday_lt (x : SignSequence.{u}) (b : Ordinal.{u})
    (hb : x.birthday < b) : x < ofOrdinal b := by
  have hle : x.signAt ≤ (ofOrdinal b).signAt := by
    intro i
    by_cases hi : i < b
    · simpa only [signAt_ofOrdinal, if_pos hi] using SignType.le_one (x.signAt i)
    · rw [signAt_ofOrdinal, if_neg hi,
        (x.signAt_eq_zero_iff i).mpr (hb.le.trans (le_of_not_gt hi))]
  apply Pi.toLex_strictMono
  apply lt_of_le_of_ne hle
  intro heq
  have hc := congrFun heq x.birthday
  simp [signAt_ofOrdinal, hb, (x.signAt_eq_zero_iff x.birthday).mpr le_rfl] at hc

/-- The ordinal order embedding is distinct from any future arithmetic map. -/
def ordinalOrderEmbedding : Ordinal.{u} ↪o SignSequence.{u} :=
  OrderEmbedding.ofStrictMono ofOrdinal ofOrdinal_strictMono

/-- Every small family of birthdays has a strict ordinal bound, using the
supremum of successor birthdays as in `found:prop:proper`. -/
theorem birthdays_bounded {I : Type v} [Small.{u} I] (f : I → SignSequence.{u}) :
    ∃ b : Ordinal.{u}, ∀ i, (f i).birthday < b :=
  ⟨⨆ i, (f i).birthday + 1, fun i => Ordinal.lt_iSup_add_one (fun i => (f i).birthday) i⟩

/-- The constructed carrier satisfies the small-family strict upper-bound
property, without assuming any general cut-filling axiom. -/
theorem small_strict_upper_bounds :
    HasSmallStrictUpperBounds.{u, u + 1} SignSequence.{u} (· < ·) := by
  intro I f
  obtain ⟨b, hb⟩ := birthdays_bounded f
  exact ⟨ofOrdinal b, fun i => lt_ofOrdinal_of_birthday_lt (f i) b (hb i)⟩

/-- The canonical carrier cannot fit in the universe of its ordinal lengths. -/
theorem not_small : ¬ Small.{u} SignSequence.{u} := by
  intro h
  letI := h
  have hs : Function.Surjective (birthday : SignSequence.{u} → Ordinal.{u}) :=
    fun a => ⟨ofOrdinal a, rfl⟩
  exact not_small_ordinal (small_of_surjective hs)

/-- A fixed birthday bound cuts out a small fragment. The restriction of
the zero extension to that bound determines the sequence. -/
instance small_bounded (b : Ordinal.{u}) :
    Small.{u} {x : SignSequence.{u} // x.birthday ≤ b} := by
  apply small_of_injective (f := fun x : {x : SignSequence.{u} // x.birthday ≤ b} =>
    fun i : Set.Iio b => x.val.signAt i)
  intro x y h
  apply Subtype.ext
  apply ext
  intro i
  by_cases hi : i < b
  · exact congrFun h ⟨i, hi⟩
  · have hbi := le_of_not_gt hi
    rw [(x.val.signAt_eq_zero_iff i).mpr (x.property.trans hbi),
      (y.val.signAt_eq_zero_iff i).mpr (y.property.trans hbi)]

/-- Initial-segment comparison, kept separate from numerical order. -/
def IsPrefix (x y : SignSequence.{u}) : Prop :=
  x.birthday ≤ y.birthday ∧ ∀ i < x.birthday, x.signAt i = y.signAt i

theorem IsPrefix.refl (x : SignSequence.{u}) : IsPrefix x x := ⟨le_rfl, fun _ _ => rfl⟩

theorem IsPrefix.trans {x y z : SignSequence.{u}} (hxy : IsPrefix x y)
    (hyz : IsPrefix y z) : IsPrefix x z :=
  ⟨hxy.1.trans hyz.1, fun i hi => (hxy.2 i hi).trans (hyz.2 i (hi.trans_le hxy.1))⟩

theorem IsPrefix.antisymm {x y : SignSequence.{u}} (hxy : IsPrefix x y)
    (hyx : IsPrefix y x) : x = y := by
  apply ext
  intro i
  by_cases hi : i < x.birthday
  · exact hxy.2 i hi
  · rw [(x.signAt_eq_zero_iff i).mpr (le_of_not_gt hi),
      (y.signAt_eq_zero_iff i).mpr (hyx.1.trans (le_of_not_gt hi))]

/-- The well-founded simplicity relation is proper prefix extension. -/
def Simpler (x y : SignSequence.{u}) : Prop :=
  IsPrefix x y ∧ x.birthday < y.birthday

theorem simpler_wellFounded : WellFounded (Simpler : SignSequence.{u} → _ → Prop) :=
  (InvImage.wf birthday Ordinal.lt_wf).mono (fun _ _ h => h.2)

/-- Truncate at an ordinal no greater than the birthday. -/
def truncate (x : SignSequence.{u}) (b : Ordinal.{u}) (hb : b ≤ x.birthday) :
    SignSequence.{u} where
  birthday := b
  signAt i := if i < b then x.signAt i else 0
  signAt_ne_zero_iff i := by
    by_cases hi : i < b
    · simp only [if_pos hi]
      exact iff_of_true ((x.signAt_ne_zero_iff i).mpr (hi.trans_le hb)) hi
    · simp [hi]

@[simp] theorem birthday_truncate (x : SignSequence.{u}) (b : Ordinal.{u})
    (hb : b ≤ x.birthday) : (truncate x b hb).birthday = b := rfl

@[simp] theorem signAt_truncate (x : SignSequence.{u}) (b : Ordinal.{u})
    (hb : b ≤ x.birthday) (i : Ordinal.{u}) :
    (truncate x b hb).signAt i = if i < b then x.signAt i else 0 := rfl

theorem truncate_isPrefix (x : SignSequence.{u}) (b : Ordinal.{u})
    (hb : b ≤ x.birthday) : IsPrefix (truncate x b hb) x :=
  ⟨hb, fun _ hi => if_pos hi⟩

theorem truncate_simpler (x : SignSequence.{u}) (b : Ordinal.{u}) (hb : b < x.birthday) :
    Simpler (truncate x b hb.le) x := ⟨truncate_isPrefix x b hb.le, hb⟩

/-- Truncating immediately before a plus gives a smaller number. -/
theorem truncate_lt_of_pos (x : SignSequence.{u}) (b : Ordinal.{u})
    (hb : b < x.birthday) (hs : x.signAt b = 1) : truncate x b hb.le < x := by
  apply (lt_iff _ _).mpr
  refine ⟨b, fun j hj => if_pos hj, ?_⟩
  simp [signAt_truncate, hs]

/-- Truncating immediately before a minus gives a larger number. -/
theorem lt_truncate_of_neg (x : SignSequence.{u}) (b : Ordinal.{u})
    (hb : b < x.birthday) (hs : x.signAt b = -1) : x < truncate x b hb.le := by
  apply (lt_iff _ _).mpr
  refine ⟨b, fun j hj => (if_pos hj).symm, ?_⟩
  simp [signAt_truncate, hs]

/-- The canonical left options are indexed by plus positions. -/
def LeftIndex (x : SignSequence.{u}) := {i : Set.Iio x.birthday // x.signAt i = 1}

/-- The canonical right options are indexed by minus positions. -/
def RightIndex (x : SignSequence.{u}) := {i : Set.Iio x.birthday // x.signAt i = -1}

instance small_leftIndex (x : SignSequence.{u}) : Small.{u} (LeftIndex x) :=
  inferInstanceAs (Small.{u} {i : Set.Iio x.birthday // x.signAt i = 1})

instance small_rightIndex (x : SignSequence.{u}) : Small.{u} (RightIndex x) :=
  inferInstanceAs (Small.{u} {i : Set.Iio x.birthday // x.signAt i = -1})

def leftOption (x : SignSequence.{u}) (i : LeftIndex x) : SignSequence.{u} :=
  truncate x i.val.val i.val.property.le

def rightOption (x : SignSequence.{u}) (i : RightIndex x) : SignSequence.{u} :=
  truncate x i.val.val i.val.property.le

theorem leftOption_lt (x : SignSequence.{u}) (i : LeftIndex x) : leftOption x i < x :=
  truncate_lt_of_pos x _ i.val.property i.property

theorem lt_rightOption (x : SignSequence.{u}) (i : RightIndex x) : x < rightOption x i :=
  lt_truncate_of_neg x _ i.val.property i.property

/-- The canonical options form an actual small separated cut, with indices
in the lower universe. This does not postulate fillers for arbitrary cuts. -/
def canonicalCut (x : SignSequence.{u}) : SmallCutData.{u, u + 1} SignSequence.{u} (· < ·) where
  Left := Shrink (LeftIndex x)
  Right := Shrink (RightIndex x)
  left i := leftOption x ((equivShrink (LeftIndex x)).symm i)
  right i := rightOption x ((equivShrink (RightIndex x)).symm i)
  separated _ _ := (leftOption_lt x _).trans (lt_rightOption x _)

/-- Every sign sequence realizes its own canonical small cut. -/
theorem canonicalCut_realized (x : SignSequence.{u}) : (canonicalCut x).IsRealizedBy x :=
  ⟨fun _ => leftOption_lt x _, fun _ => lt_rightOption x _⟩

/-- Sign reversal preserves the birthday and reverses numerical order. -/
instance : Neg SignSequence.{u} where
  neg x :=
    { birthday := x.birthday
      signAt i := -x.signAt i
      signAt_ne_zero_iff i := by
        simpa only [SignType.neg_eq_zero_iff, ne_eq] using x.signAt_ne_zero_iff i }

@[simp] theorem birthday_neg (x : SignSequence.{u}) : (-x).birthday = x.birthday := rfl
@[simp] theorem signAt_neg (x : SignSequence.{u}) (i : Ordinal.{u}) :
    (-x).signAt i = -x.signAt i := rfl

@[simp] theorem neg_neg (x : SignSequence.{u}) : -(-x) = x := by
  apply ext
  intro i
  simp only [signAt_neg, _root_.neg_neg]

theorem neg_lt_neg_iff (x y : SignSequence.{u}) : -x < -y ↔ y < x := by
  simp only [lt_iff, signAt_neg, _root_.neg_inj, SignType.neg_lt_neg_iff]
  constructor <;> rintro ⟨i, h, hi⟩ <;> exact ⟨i, fun j hj => (h j hj).symm, hi⟩

/-- The explicit counterexample in `found:rem:simplicity`: the one-plus
sequence is shorter than two minuses, but is not their initial segment. -/
theorem birthday_precedence_not_prefix :
    (ofOrdinal 1).birthday < (-ofOrdinal 2 : SignSequence.{u}).birthday ∧
      ¬ IsPrefix (ofOrdinal 1) (-ofOrdinal 2 : SignSequence.{u}) := by
  constructor
  · simp only [birthday_ofOrdinal, birthday_neg]
    exact_mod_cast (by decide : (1 : ℕ) < 2)
  · intro h
    have h0 := h.2 0 (by simp)
    have hz : (0 : Ordinal.{u}) < 2 := by exact_mod_cast (by decide : (0 : ℕ) < 2)
    simp [signAt_ofOrdinal, hz] at h0

end

end SignSequence
end Surreal.Foundations
