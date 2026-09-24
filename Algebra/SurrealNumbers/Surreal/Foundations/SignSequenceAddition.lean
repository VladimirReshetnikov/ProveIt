import Surreal.Foundations.SignSequenceCutComparison
import Surreal.Foundations.SignSequenceTruncation
import Mathlib.Order.GameAdd

/-!
# Conway addition on sign sequences

The sum in `found:eq:addcut` is defined by well-founded recursion on the
birthdays of both inputs. Its left options are `xᴸ + y` and `x + yᴸ`,
and its right options are `xᴿ + y` and `x + yᴿ`.

Separation is proved before the addition operation is exposed. Canonical
options are nested truncations, so same-input option comparisons follow
from earlier recursive cuts. Mixed comparisons pass through the sum of
the two relevant options. Only small option families enter a cut.
-/

universe u

namespace Surreal.Foundations.SignSequence

open scoped Classical

noncomputable section

private abbrev BirthdayLT (x y : SignSequence.{u}) : Prop := x.birthday < y.birthday
private theorem birthdayLT_wf : WellFounded (BirthdayLT : SignSequence.{u} → _ → Prop) :=
  InvImage.wf birthday Ordinal.lt_wf

private def indexedCut {L R : Type (u + 1)} [Small.{u} L] [Small.{u} R]
    (l : L → SignSequence.{u}) (r : R → SignSequence.{u}) (h : ∀ i j, l i < r j) :
    SmallCutData.{u, u + 1} SignSequence.{u} (· < ·) where
  Left := Shrink L
  Right := Shrink R
  left i := l ((equivShrink L).symm i)
  right j := r ((equivShrink R).symm j)
  separated _ _ := h _ _

private theorem indexedCut_realizes_iff {L R : Type (u + 1)} [Small.{u} L] [Small.{u} R]
    (l : L → SignSequence.{u}) (r : R → SignSequence.{u}) (h : ∀ i j, l i < r j)
    (x : SignSequence.{u}) :
    (indexedCut l r h).IsRealizedBy x ↔ (∀ i, l i < x) ∧ (∀ j, x < r j) := by
  constructor
  · rintro ⟨hl, hr⟩
    constructor
    · intro i
      simpa only [indexedCut, Equiv.symm_apply_apply] using hl ((equivShrink L) i)
    · intro j
      simpa only [indexedCut, Equiv.symm_apply_apply] using hr ((equivShrink R) j)
  · rintro ⟨hl, hr⟩
    exact ⟨fun _ => hl _, fun _ => hr _⟩

/-- Internal totalization only; the fallback is eliminated by the
recursive separation proof before defining the public addition. -/
private def tentativeCut {L R : Type (u + 1)} [Small.{u} L] [Small.{u} R]
    (l : L → SignSequence.{u}) (r : R → SignSequence.{u}) : SignSequence.{u} :=
  if h : ∀ i j, l i < r j then cut (indexedCut l r h) else 0

private theorem tentativeCut_realizes {L R : Type (u + 1)} [Small.{u} L] [Small.{u} R]
    (l : L → SignSequence.{u}) (r : R → SignSequence.{u}) (h : ∀ i j, l i < r j) :
    (∀ i, l i < tentativeCut l r) ∧ (∀ j, tentativeCut l r < r j) := by
  rw [tentativeCut, dif_pos h]
  exact (indexedCut_realizes_iff l r h _).mp (cut_realizes _)

private def addStep (x y : SignSequence.{u})
    (f : ∀ x' y', Prod.GameAdd BirthdayLT BirthdayLT (x', y') (x, y) → SignSequence.{u}) :
    SignSequence.{u} :=
  tentativeCut
    (Sum.elim
      (fun i : LeftIndex x => f (leftOption x i) y (Prod.GameAdd.fst i.val.property))
      (fun i : LeftIndex y => f x (leftOption y i) (Prod.GameAdd.snd i.val.property)))
    (Sum.elim
      (fun i : RightIndex x => f (rightOption x i) y (Prod.GameAdd.fst i.val.property))
      (fun i : RightIndex y => f x (rightOption y i) (Prod.GameAdd.snd i.val.property)))

private def tentativeAdd : SignSequence.{u} → SignSequence.{u} → SignSequence.{u} :=
  Prod.GameAdd.recursion birthdayLT_wf birthdayLT_wf addStep

private theorem tentativeAdd_eq (x y : SignSequence.{u}) :
    tentativeAdd x y = tentativeCut
      (Sum.elim (fun i : LeftIndex x => tentativeAdd (leftOption x i) y)
        (fun i : LeftIndex y => tentativeAdd x (leftOption y i)))
      (Sum.elim (fun i : RightIndex x => tentativeAdd (rightOption x i) y)
        (fun i : RightIndex y => tentativeAdd x (rightOption y i))) :=
  Prod.GameAdd.recursion_eq birthdayLT_wf birthdayLT_wf addStep x y

private def AddOptionBounds (f : SignSequence.{u} → SignSequence.{u} → SignSequence.{u})
    (x y : SignSequence.{u}) : Prop :=
  (∀ i : LeftIndex x, f (leftOption x i) y < f x y) ∧
  (∀ i : LeftIndex y, f x (leftOption y i) < f x y) ∧
  (∀ i : RightIndex x, f x y < f (rightOption x i) y) ∧
  (∀ i : RightIndex y, f x y < f x (rightOption y i))

private theorem tentativeAdd_bounds (x y : SignSequence.{u}) : AddOptionBounds tentativeAdd x y := by
  induction x, y using Prod.GameAdd.recursion birthdayLT_wf birthdayLT_wf with
  | IH x y ih =>
    have hlx (i : LeftIndex x) := ih (leftOption x i) y (Prod.GameAdd.fst i.val.property)
    have hrx (i : RightIndex x) := ih (rightOption x i) y (Prod.GameAdd.fst i.val.property)
    have hly (i : LeftIndex y) := ih x (leftOption y i) (Prod.GameAdd.snd i.val.property)
    have hry (i : RightIndex y) := ih x (rightOption y i) (Prod.GameAdd.snd i.val.property)
    have hsep : ∀ i j,
        Sum.elim (fun i : LeftIndex x => tentativeAdd (leftOption x i) y)
          (fun i : LeftIndex y => tentativeAdd x (leftOption y i)) i <
        Sum.elim (fun j : RightIndex x => tentativeAdd (rightOption x j) y)
          (fun j : RightIndex y => tentativeAdd x (rightOption y j)) j := by
      rintro (l | l) (r | r)
      · rcases left_right_option_nested x l r with ⟨i, hi⟩ | ⟨i, hi⟩
        · simpa only [Sum.elim_inl, hi] using (hrx r).1 i
        · simpa only [Sum.elim_inl, hi] using (hlx l).2.2.1 i
      · exact ((hlx l).2.2.2 r).trans ((hry r).1 l)
      · exact ((hly l).2.2.1 r).trans ((hrx r).2.1 l)
      · rcases left_right_option_nested y l r with ⟨i, hi⟩ | ⟨i, hi⟩
        · simpa only [Sum.elim_inr, hi] using (hry r).2.1 i
        · simpa only [Sum.elim_inr, hi] using (hly l).2.2.2 i
    have hb := tentativeCut_realizes _ _ hsep
    rw [← tentativeAdd_eq] at hb
    exact ⟨fun i => hb.1 (Sum.inl i), fun i => hb.1 (Sum.inr i),
      fun i => hb.2 (Sum.inl i), fun i => hb.2 (Sum.inr i)⟩

/-- Conway addition on the actual sign carrier. The internal recursion's
option families have been proved separated in `tentativeAdd_bounds`. -/
def add (x y : SignSequence.{u}) : SignSequence.{u} := tentativeAdd x y

instance : Add SignSequence.{u} := ⟨add⟩

/-- Every canonical left option of the first summand gives a lower sum. -/
theorem add_leftOption_left (x y : SignSequence.{u}) (i : LeftIndex x) :
    leftOption x i + y < x + y := (tentativeAdd_bounds x y).1 i

/-- Every canonical left option of the second summand gives a lower sum. -/
theorem add_leftOption_right (x y : SignSequence.{u}) (i : LeftIndex y) :
    x + leftOption y i < x + y := (tentativeAdd_bounds x y).2.1 i

/-- Every canonical right option of the first summand gives an upper sum. -/
theorem add_rightOption_left (x y : SignSequence.{u}) (i : RightIndex x) :
    x + y < rightOption x i + y := (tentativeAdd_bounds x y).2.2.1 i

/-- Every canonical right option of the second summand gives an upper sum. -/
theorem add_rightOption_right (x y : SignSequence.{u}) (i : RightIndex y) :
    x + y < x + rightOption y i := (tentativeAdd_bounds x y).2.2.2 i

/-- The two small left-option families of Conway addition. -/
def addLeft (x y : SignSequence.{u}) : LeftIndex x ⊕ LeftIndex y → SignSequence.{u} :=
  Sum.elim (fun i => leftOption x i + y) (fun i => x + leftOption y i)

/-- The two small right-option families of Conway addition. -/
def addRight (x y : SignSequence.{u}) : RightIndex x ⊕ RightIndex y → SignSequence.{u} :=
  Sum.elim (fun i => rightOption x i + y) (fun i => x + rightOption y i)

/-- The recursive addition options are genuinely separated. -/
theorem add_options_separated (x y : SignSequence.{u}) (i j) : addLeft x y i < addRight x y j := by
  have hl : addLeft x y i < x + y := by
    cases i with
    | inl i => exact add_leftOption_left x y i
    | inr i => exact add_leftOption_right x y i
  have hr : x + y < addRight x y j := by
    cases j with
    | inl j => exact add_rightOption_left x y j
    | inr j => exact add_rightOption_right x y j
  exact hl.trans hr

/-- The certified small cut from `found:eq:addcut`. -/
def addCut (x y : SignSequence.{u}) : SmallCutData.{u, u + 1} SignSequence.{u} (· < ·) :=
  indexedCut (addLeft x y) (addRight x y) (add_options_separated x y)

/-- Addition obeys the actual Conway cut equation, with separation proved. -/
theorem add_eq_cut (x y : SignSequence.{u}) : x + y = cut (addCut x y) := by
  change tentativeAdd x y = _
  rw [tentativeAdd_eq]
  unfold tentativeCut
  exact dif_pos (add_options_separated x y)

/-- The addition cut has precisely the usual two families on each side. -/
theorem addCut_realizes_iff (x y z : SignSequence.{u}) :
    (addCut x y).IsRealizedBy z ↔
      ((∀ i : LeftIndex x, leftOption x i + y < z) ∧
        (∀ i : LeftIndex y, x + leftOption y i < z)) ∧
      ((∀ i : RightIndex x, z < rightOption x i + y) ∧
        (∀ i : RightIndex y, z < x + rightOption y i)) := by
  rw [addCut, indexedCut_realizes_iff]
  simp only [addLeft, addRight, Sum.forall, Sum.elim_inl, Sum.elim_inr]


/-- Conway addition is commutative. The two summand-option families are
exchanged, and all recursive sums agree by pair induction. -/
theorem add_comm (x y : SignSequence.{u}) : x + y = y + x := by
  induction x, y using Prod.GameAdd.recursion birthdayLT_wf birthdayLT_wf with
  | IH x y ih =>
    have hlx (i : LeftIndex x) := ih (leftOption x i) y (Prod.GameAdd.fst i.val.property)
    have hrx (i : RightIndex x) := ih (rightOption x i) y (Prod.GameAdd.fst i.val.property)
    have hly (i : LeftIndex y) := ih x (leftOption y i) (Prod.GameAdd.snd i.val.property)
    have hry (i : RightIndex y) := ih x (rightOption y i) (Prod.GameAdd.snd i.val.property)
    rw [add_eq_cut x y, add_eq_cut y x]
    apply cut_congr
    intro z
    rw [addCut_realizes_iff, addCut_realizes_iff]
    simp only [hlx, hrx, hly, hry]
    constructor <;> rintro ⟨⟨h₁, h₂⟩, ⟨h₃, h₄⟩⟩ <;> exact ⟨⟨h₂, h₁⟩, ⟨h₄, h₃⟩⟩

/-- The empty sign sequence is a right additive identity. -/
@[simp] theorem add_zero (x : SignSequence.{u}) : x + 0 = x := by
  induction x using birthdayLT_wf.induction with
  | h x ih =>
    rw [add_eq_cut]
    apply Eq.trans ?_ (cut_canonicalCut x)
    apply cut_congr
    intro z
    rw [addCut_realizes_iff]
    constructor
    · rintro ⟨⟨hl, _⟩, ⟨hr, _⟩⟩
      constructor
      · intro i
        let j := (equivShrink (LeftIndex x)).symm i
        change leftOption x j < z
        simpa only [ih (leftOption x j) j.val.property] using hl j
      · intro i
        let j := (equivShrink (RightIndex x)).symm i
        change z < rightOption x j
        simpa only [ih (rightOption x j) j.val.property] using hr j
    · rintro ⟨hl, hr⟩
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · intro i
        rw [ih (leftOption x i) i.val.property]
        simpa only [canonicalCut, Equiv.symm_apply_apply] using hl ((equivShrink (LeftIndex x)) i)
      · intro i
        have hi := i.val.property
        simp at hi
      · intro i
        rw [ih (rightOption x i) i.val.property]
        simpa only [canonicalCut, Equiv.symm_apply_apply] using hr ((equivShrink (RightIndex x)) i)
      · intro i
        have hi := i.val.property
        simp at hi

/-- The empty sign sequence is a left additive identity. -/
@[simp] theorem zero_add (x : SignSequence.{u}) : 0 + x = x := by
  rw [add_comm, add_zero]

/-- A map strictly preserving the canonical option bounds preserves
numerical order. The proof uses well-founded comparison of its inputs. -/
theorem strictMono_of_option_bounds (f : SignSequence.{u} → SignSequence.{u})
    (hl : ∀ x (i : LeftIndex x), f (leftOption x i) < f x)
    (hr : ∀ x (i : RightIndex x), f x < f (rightOption x i)) : StrictMono f := by
  intro x y
  induction x, y using Prod.GameAdd.recursion birthdayLT_wf birthdayLT_wf with
  | IH x y ih =>
    intro hxy
    rcases (lt_iff_exists_option x y).mp hxy with ⟨i, hi⟩ | ⟨i, hi⟩
    · rcases lt_or_eq_of_le hi with hlt | heq
      · exact (ih x (leftOption y i) (Prod.GameAdd.snd i.val.property) hlt).trans (hl y i)
      · simpa only [heq] using hl y i
    · rcases lt_or_eq_of_le hi with hlt | heq
      · exact (hr x i).trans (ih (rightOption x i) y (Prod.GameAdd.fst i.val.property) hlt)
      · simpa only [heq] using hr x i

/-- Translation on the right strictly preserves numerical order. -/
theorem add_right_strictMono (y : SignSequence.{u}) : StrictMono (fun x => x + y) :=
  strictMono_of_option_bounds _ (fun x i => add_leftOption_left x y i)
    (fun x i => add_rightOption_left x y i)

/-- Translation on the left strictly preserves numerical order. -/
theorem add_left_strictMono (x : SignSequence.{u}) : StrictMono (fun y => x + y) :=
  strictMono_of_option_bounds _ (fun y i => add_leftOption_right x y i)
    (fun y i => add_rightOption_right x y i)

@[simp] theorem add_le_add_right_iff (x y z : SignSequence.{u}) : x + z ≤ y + z ↔ x ≤ y :=
  (add_right_strictMono z).le_iff_le

@[simp] theorem add_lt_add_right_iff (x y z : SignSequence.{u}) : x + z < y + z ↔ x < y :=
  (add_right_strictMono z).lt_iff_lt

@[simp] theorem add_le_add_left_iff (x y z : SignSequence.{u}) : z + x ≤ z + y ↔ x ≤ y :=
  (add_left_strictMono z).le_iff_le

@[simp] theorem add_lt_add_left_iff (x y z : SignSequence.{u}) : z + x < z + y ↔ x < y :=
  (add_left_strictMono z).lt_iff_lt

/-- Cancellation holds before any group structure is assumed. -/
theorem add_right_cancel {x y z : SignSequence.{u}} (h : x + z = y + z) : x = y :=
  (add_right_strictMono z).injective h

/-- Cancellation holds in the other argument as well. -/
theorem add_left_cancel {x y z : SignSequence.{u}} (h : z + x = z + y) : x = y :=
  (add_left_strictMono z).injective h

end

end Surreal.Foundations.SignSequence
