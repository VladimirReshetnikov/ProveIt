import Surreal.Foundations.SizeObstructions
import Mathlib.Logic.Small.Basic

/-!
# Reindexing small cut data

The indexed and predicate-based interfaces in `found:sub:cutdata` have the
same separator predicate. A pair of option sets can be used only when
their element types are small at the cut-index universe.
-/

universe u v

namespace Surreal.Foundations

namespace SmallCutData

variable {X : Type v} {lt : X → X → Prop}

/-- Change the small option indices by equivalences. -/
def reindex (c : SmallCutData.{u, v} X lt) {L R : Type u}
    (eL : L ≃ c.Left) (eR : R ≃ c.Right) : SmallCutData.{u, v} X lt where
  Left := L
  Right := R
  left l := c.left (eL l)
  right r := c.right (eR r)
  separated l r := c.separated (eL l) (eR r)

/-- Reindexing preserves precisely the same separators. -/
@[simp] theorem reindex_isRealizedBy_iff (c : SmallCutData.{u, v} X lt)
    {L R : Type u} (eL : L ≃ c.Left) (eR : R ≃ c.Right) (x : X) :
    (c.reindex eL eR).IsRealizedBy x ↔ c.IsRealizedBy x := by
  constructor
  · rintro ⟨hl, hr⟩
    exact ⟨fun l => by simpa only [reindex, Equiv.apply_symm_apply] using hl (eL.symm l),
      fun r => by simpa only [reindex, Equiv.apply_symm_apply] using hr (eR.symm r)⟩
  · rintro ⟨hl, hr⟩
    exact ⟨fun l => hl (eL l), fun r => hr (eR r)⟩

/-- A separated pair of small sets supplies cut data with lower-universe
indices by shrinking their element types. -/
noncomputable def ofSmallSets (L R : Set X) [Small.{u} L] [Small.{u} R]
    (h : ∀ l ∈ L, ∀ r ∈ R, lt l r) : SmallCutData.{u, v} X lt where
  Left := Shrink L
  Right := Shrink R
  left l := ((equivShrink L).symm l).val
  right r := ((equivShrink R).symm r).val
  separated l r := h _ ((equivShrink L).symm l).property _
    ((equivShrink R).symm r).property

/-- The indexed cut constructed from small sets has exactly the
predicate-based separator condition in `found:sub:cutdata`. -/
@[simp] theorem ofSmallSets_isRealizedBy_iff (L R : Set X)
    [Small.{u} L] [Small.{u} R] (h : ∀ l ∈ L, ∀ r ∈ R, lt l r) (x : X) :
    (ofSmallSets L R h).IsRealizedBy x ↔
      (∀ l ∈ L, lt l x) ∧ (∀ r ∈ R, lt x r) := by
  constructor
  · rintro ⟨hl, hr⟩
    constructor
    · intro l hlL
      simpa only [ofSmallSets, Equiv.symm_apply_apply] using
        hl ((equivShrink L) ⟨l, hlL⟩)
    · intro r hrR
      simpa only [ofSmallSets, Equiv.symm_apply_apply] using
        hr ((equivShrink R) ⟨r, hrR⟩)
  · rintro ⟨hl, hr⟩
    exact ⟨fun l => hl _ ((equivShrink L).symm l).property,
      fun r => hr _ ((equivShrink R).symm r).property⟩

end SmallCutData

/-- A proved filler property applies to predicate-based option sets only
with explicit smallness of both option types. -/
theorem HasSmallCutFillers.exists_separator_of_small_sets
    {X : Type v} {lt : X → X → Prop} (hf : HasSmallCutFillers.{u, v} X lt)
    (L R : Set X) [Small.{u} L] [Small.{u} R]
    (h : ∀ l ∈ L, ∀ r ∈ R, lt l r) :
    ∃ x, (∀ l ∈ L, lt l x) ∧ (∀ r ∈ R, lt x r) := by
  obtain ⟨x, hx⟩ := hf (SmallCutData.ofSmallSets L R h)
  exact ⟨x, (SmallCutData.ofSmallSets_isRealizedBy_iff L R h x).mp hx⟩

end Surreal.Foundations
