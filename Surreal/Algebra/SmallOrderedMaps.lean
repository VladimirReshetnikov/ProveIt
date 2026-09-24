import Mathlib.Algebra.Order.Group.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Logic.Small.Basic

/-!
# Small images of monotone additive maps

The ordered-group argument behind `osq:nm:lem:orderedmap`.
If every small family in the source is bounded above, a monotone
additive map with small image must vanish. Choose one preimage of
each image value and bound those preimages. The image then has a
greatest element, which an ordered additive subgroup can only have
when it is zero. No Archimedean hypothesis is used.
-/

universe u v w
namespace Surreal.SmallOrderedMaps

/-- A monotone additive map with small range vanishes if all small source families are bounded. -/
theorem eq_zero_of_small_range {A : Type v} {G : Type w}
    [AddCommGroup A] [Preorder A] [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G]
    (hbound : ∀ (ι : Type u) (a : ι → A), ∃ b : A, ∀ i, a i ≤ b)
    (f : A →+ G) [Small.{u} (Set.range f)] (hf : Monotone f) : f = 0 := by
  classical
  let pick (y : Set.range f) : A := Classical.choose y.property
  have hpick (y : Set.range f) : f (pick y) = y := Classical.choose_spec y.property
  obtain ⟨b, hb⟩ := hbound (Shrink.{u} (Set.range f))
    (fun i => pick ((equivShrink (Set.range f)).symm i))
  have hmax (x : A) : f x ≤ f b := by
    let y : Set.range f := ⟨f x, x, rfl⟩
    have h := hf (hb (equivShrink (Set.range f) y))
    simpa only [Equiv.symm_apply_apply, hpick] using h
  have hnonpos (x : A) : f x ≤ 0 := by
    have h := hmax (b + x)
    rw [map_add] at h
    exact nonpos_of_add_le_right h
  apply AddMonoidHom.ext
  intro x
  apply le_antisymm (hnonpos x)
  have h := hnonpos (-x)
  rwa [map_neg, neg_nonpos] at h

end Surreal.SmallOrderedMaps
