import MoserWorm.Common.Box.Basic
import MoserWorm.Common.Interval.Sound

/-! Every accepted subdivision tree proves its predicate on the entire root box. -/

namespace MoserWorm

variable {n : Nat}

namespace DyadicBox

def Mem (box : DyadicBox n) (x : Fin n → ℝ) : Prop :=
  ∀ i, x i ∈ box[i]

theorem mem_left_or_right {box : DyadicBox n} {x : Fin n → ℝ}
    (h : box.Mem x) (axis : Fin n) :
    (box.left axis).Mem x ∨ (box.right axis).Mem x := by
  rcases le_total (x axis) (DIval.val (midpoint box[axis])) with hl | hr
  · left
    intro i
    by_cases hi : axis = i
    · subst i
      change x axis ∈ (box.set axis.val
        ⟨box[axis].lo, midpoint box[axis]⟩ axis.isLt)[axis.val]
      rw [Vector.getElem_set_self]
      exact DIval.mem_iff_val.mpr ⟨(DIval.mem_iff_val.mp (h axis)).1, hl⟩
    · change x i ∈ (box.set axis.val
        ⟨box[axis].lo, midpoint box[axis]⟩ axis.isLt)[i.val]
      rw [Vector.getElem_set_ne axis.isLt i.isLt (Fin.val_ne_of_ne hi)]
      exact h i
  · right
    intro i
    by_cases hi : axis = i
    · subst i
      change x axis ∈ (box.set axis.val
        ⟨midpoint box[axis], box[axis].hi⟩ axis.isLt)[axis.val]
      rw [Vector.getElem_set_self]
      exact DIval.mem_iff_val.mpr ⟨hr, (DIval.mem_iff_val.mp (h axis)).2⟩
    · change x i ∈ (box.set axis.val
        ⟨midpoint box[axis], box[axis].hi⟩ axis.isLt)[i.val]
      rw [Vector.getElem_set_ne axis.isLt i.isLt (Fin.val_ne_of_ne hi)]
      exact h i

/-- This also combines independently checked certificate shards. -/
theorem of_split {P : (Fin n → ℝ) → Prop} {box : DyadicBox n} (axis : Fin n)
    (hl : ∀ x, (box.left axis).Mem x → P x)
    (hr : ∀ x, (box.right axis).Mem x → P x) :
    ∀ x, box.Mem x → P x := by
  intro x hx
  exact (mem_left_or_right hx axis).elim (hl x) (hr x)

end DyadicBox

namespace BoxTree

variable {α : Type}

theorem check_sound (checkLeaf : DyadicBox n → α → Bool)
    (P : (Fin n → ℝ) → Prop)
    (hLeaf : ∀ box witness, checkLeaf box witness = true →
      ∀ x, box.Mem x → P x)
    (tree : BoxTree n α) (box : DyadicBox n) (h : check checkLeaf box tree = true) :
    ∀ x, box.Mem x → P x := by
  induction tree generalizing box with
  | leaf witness => exact hLeaf box witness h
  | split axis left right ihl ihr =>
    simp only [check, Bool.and_eq_true] at h
    exact DyadicBox.of_split axis (ihl _ h.1) (ihr _ h.2)

end BoxTree

end MoserWorm
