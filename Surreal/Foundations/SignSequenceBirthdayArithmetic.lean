import Surreal.Foundations.SignSequenceGameBirthday
import Surreal.Foundations.SignSequenceOrdinals
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Additive birthday bounds and the natural-sum recursion measure

The canonical representative has no larger birthday than any numeric game
representing the same value. The raw game sum has birthday exactly the
Hessenberg sum, giving the additive bound and its finite-sum consequence
in `lem:add` of the Laurent-birthday report.

The same natural sum strictly decreases when either sign argument is
replaced by a proper prefix, as required in `found:eq:natsum`.
All natural arithmetic is explicit on `NatOrdinal`; ordinary ordinal
addition and multiplication are not substituted for it.
-/

universe u v

namespace Surreal.Foundations.SignSequence

noncomputable section

/-- The birthday of a sum is bounded by the natural sum of the birthdays. -/
theorem birthday_add_le_natural (x y : SignSequence.{u}) :
    NatOrdinal.of (x + y).birthday ≤ NatOrdinal.of x.birthday + NatOrdinal.of y.birthday := by
  have h := birthday_le_of_toSurreal_eq_mk (x + y) (toIGame x + toIGame y)
    (by rw [toSurreal_add, _root_.Surreal.mk_add]; rfl)
  rw [IGame.birthday_add, birthday_toIGame, birthday_toIGame] at h
  exact h

/-- The same bound with an ordinal-valued conclusion. -/
theorem birthday_add_le (x y : SignSequence.{u}) :
    (x + y).birthday ≤ NatOrdinal.val (NatOrdinal.of x.birthday + NatOrdinal.of y.birthday) :=
  birthday_add_le_natural x y

/-- Negation does not change a birthday, so subtraction has the same bound. -/
theorem birthday_sub_le_natural (x y : SignSequence.{u}) :
    NatOrdinal.of (x - y).birthday ≤ NatOrdinal.of x.birthday + NatOrdinal.of y.birthday := by
  simpa only [sub_eq_add_neg, birthday_neg] using birthday_add_le_natural x (-y)

/-- The finite-sum conclusion of `lem:add`, including the empty sum. -/
theorem birthday_finset_sum_le {ι : Type v} (s : Finset ι) (f : ι → SignSequence.{u}) :
    NatOrdinal.of (∑ i ∈ s, f i).birthday ≤ ∑ i ∈ s, NatOrdinal.of (f i).birthday := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (birthday_add_le_natural _ _).trans (_root_.add_le_add le_rfl ih)

/-- A finite multiple has birthday at most the corresponding natural multiple. -/
theorem birthday_nsmul_le (n : ℕ) (x : SignSequence.{u}) :
    NatOrdinal.of (n • x).birthday ≤ n • NatOrdinal.of x.birthday := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [succ_nsmul, succ_nsmul]
    exact (birthday_add_le_natural _ _).trans (_root_.add_le_add ih le_rfl)

/-- The natural-sum birthday measure used for binary recursion. -/
def pairBirthday (p : SignSequence.{u} × SignSequence.{u}) : NatOrdinal.{u} :=
  NatOrdinal.of p.1.birthday + NatOrdinal.of p.2.birthday

/-- Replacing the first input by a proper sign prefix strictly lowers the measure. -/
theorem pairBirthday_lt_left {x' x : SignSequence.{u}} (h : Simpler x' x)
    (y : SignSequence.{u}) : pairBirthday (x', y) < pairBirthday (x, y) :=
  _root_.add_lt_add_of_lt_of_le (NatOrdinal.of.strictMono h.2) le_rfl

/-- Replacing the second input by a proper sign prefix strictly lowers the measure. -/
theorem pairBirthday_lt_right (x : SignSequence.{u}) {y' y : SignSequence.{u}}
    (h : Simpler y' y) : pairBirthday (x, y') < pairBirthday (x, y) :=
  _root_.add_lt_add_of_le_of_lt le_rfl (NatOrdinal.of.strictMono h.2)

/-- The existing game-addition recursion relation is measured by the
Hessenberg sum of sign lengths. -/
theorem pairBirthday_lt_of_pairSimpler {p q : SignSequence.{u} × SignSequence.{u}}
    (h : PairSimpler p q) : pairBirthday p < pairBirthday q := by
  cases h with
  | fst h => exact pairBirthday_lt_left h _
  | snd h => exact pairBirthday_lt_right _ h

/-- A separate well-foundedness proof directly from the ordinal measure. -/
theorem pairSimpler_wellFounded_by_birthday : WellFounded (PairSimpler :
    (SignSequence.{u} × SignSequence.{u}) → _ → Prop) :=
  (InvImage.wf pairBirthday wellFounded_lt).mono
    (fun _ _ h => pairBirthday_lt_of_pairSimpler h)

/-- On ordinal signs the additive birthday bound is an equality. -/
theorem birthday_add_ofOrdinal (a b : Ordinal.{u}) :
    NatOrdinal.of (ofOrdinal a + ofOrdinal b).birthday = NatOrdinal.of a + NatOrdinal.of b := by
  rw [← ofOrdinal_natural_add, birthday_ofOrdinal, NatOrdinal.of_val]

/-- On ordinal signs the product birthday is exactly the natural product. -/
theorem birthday_mul_ofOrdinal (a b : Ordinal.{u}) :
    NatOrdinal.of (ofOrdinal a * ofOrdinal b).birthday = NatOrdinal.of a * NatOrdinal.of b := by
  rw [← ofOrdinal_natural_mul, birthday_ofOrdinal, NatOrdinal.of_val]

end

end Surreal.Foundations.SignSequence
