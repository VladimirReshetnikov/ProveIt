import Surreal.Algebra.SmallOrderedMaps
import Surreal.Foundations.SignSequenceReal

/-!
# No nonzero small-valued ordered additive maps from the surreals

The full universe-indexed form of `osq:nm:lem:orderedmap`.
The actual sign-sequence carrier bounds every lower-universe-small
family. A monotone additive map into a group small in that universe
therefore vanishes, with no assumption about ordinal scalar products.
-/

universe u v
namespace Surreal.Foundations.SignSequence

/-- A monotone additive map from the actual surreals with small image is zero. -/
theorem ordered_addHom_eq_zero_of_small_range {G : Type v}
    [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G]
    (f : SignSequence.{u} →+ G) [Small.{u} (Set.range f)] (hf : Monotone f) : f = 0 := by
  have hbound (ι : Type u) (a : ι → SignSequence.{u}) : ∃ b, ∀ i, a i ≤ b := by
    obtain ⟨b, hb⟩ := small_strict_upper_bounds ι a
    exact ⟨b, fun i => (hb i).le⟩
  exact SmallOrderedMaps.eq_zero_of_small_range hbound f hf

/-- In particular every monotone additive map to a small ordered group vanishes. -/
theorem ordered_addHom_eq_zero {G : Type v}
    [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G] [Small.{u} G]
    (f : SignSequence.{u} →+ G) (hf : Monotone f) : f = 0 :=
  ordered_addHom_eq_zero_of_small_range f hf

end Surreal.Foundations.SignSequence
