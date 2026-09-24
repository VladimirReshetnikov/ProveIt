import Surreal.Foundations.SignSequenceCutOperation
import Mathlib.Logic.Small.Set
import Mathlib.Order.Bounds.Basic

/-!
# Small bounds are not numerical suprema

This proves the cut-based generalization following `found:prop:incomplete`:
a small set with no greatest member has no least upper bound. The embedded
finite ordinals give a concrete nonempty bounded small set without a supremum,
before any field operations are constructed on the sign carrier.
-/

universe u

namespace Surreal.Foundations.SignSequence

/-- A small set with no greatest member has an upper bound strictly below
every proposed upper bound. -/
theorem exists_smaller_upper_bound (s : Set SignSequence.{u}) [Small.{u} s]
    (hs : ∀ x ∈ s, ∃ y ∈ s, x < y) {b : SignSequence.{u}} (hb : b ∈ upperBounds s) :
    ∃ c, c ∈ upperBounds s ∧ c < b := by
  have hsep : ∀ x ∈ s, ∀ y ∈ ({b} : Set SignSequence.{u}), x < y := by
    intro x hx y hy
    obtain rfl := Set.mem_singleton_iff.mp hy
    obtain ⟨z, hz, hxz⟩ := hs x hx
    exact hxz.trans_le (hb hz)
  obtain ⟨c, hc, hcb⟩ := exists_separator_of_small_sets s {b} hsep
  exact ⟨c, fun _ hx => (hc _ hx).le, hcb b (Set.mem_singleton b)⟩

/-- A small set without a greatest member has no least upper bound. This
does not assert Dedekind completeness for the full sign carrier. -/
theorem no_isLUB_of_no_greatest (s : Set SignSequence.{u}) [Small.{u} s]
    (hs : ∀ x ∈ s, ∃ y ∈ s, x < y) : ¬ ∃ b, IsLUB s b := by
  rintro ⟨b, hb⟩
  obtain ⟨c, hc, hcb⟩ := exists_smaller_upper_bound s hs hb.1
  exact (not_le_of_gt hcb) (hb.2 hc)

/-- The embedded finite ordinals are a concrete witness to the
order-theoretic failure of Dedekind completeness in `found:prop:incomplete`.
Identifying this embedding with field natural numbers remains an arithmetic
comparison theorem for the future field construction. -/
theorem finite_ordinals_bounded_without_supremum :
    let s := Set.range (fun n : ℕ => ofOrdinal (n : Ordinal.{u}))
    s.Nonempty ∧ BddAbove s ∧ ¬ ∃ b, IsLUB s b := by
  dsimp only
  let s := Set.range (fun n : ℕ => ofOrdinal (n : Ordinal.{u}))
  have hbound := small_strict_upper_bounds.exists_bound_of_small_set s
  obtain ⟨b, hb⟩ := hbound
  refine ⟨⟨ofOrdinal 0, ⟨0, rfl⟩⟩, ⟨b, fun x hx => (hb x hx).le⟩, ?_⟩
  apply no_isLUB_of_no_greatest s
  rintro x ⟨n, rfl⟩
  refine ⟨ofOrdinal ((n + 1 : ℕ) : Ordinal.{u}), ⟨n + 1, rfl⟩, ?_⟩
  apply ofOrdinal_strictMono
  exact_mod_cast Nat.lt_succ_self n

end Surreal.Foundations.SignSequence
