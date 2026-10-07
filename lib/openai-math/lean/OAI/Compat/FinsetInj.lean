/-
Added for ProveIt (not an upstream file; distributed under Apache-2.0).
Injective finite-sum comparison needed by the quantitative port. This local
proof uses Mathlib v4.32.0's sum_image and subset comparison; no upstream
proof text is copied.
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option autoImplicit false

theorem Finset.sum_le_sum_of_injOn {ι κ α : Type*} [DecidableEq κ]
    [AddCommMonoid α] [Preorder α] [AddLeftMono α]
    {s : Finset ι} {t : Finset κ} {f : ι → α} {g : κ → α}
    (e : ι → κ) (he : Set.InjOn e (s : Set ι)) (hsub : s.image e ⊆ t)
    (hle : ∀ i ∈ s, f i ≤ g (e i))
    (hzero : ∀ j ∈ t, j ∉ s.image e → 0 ≤ g j) :
    ∑ i ∈ s, f i ≤ ∑ j ∈ t, g j := by
  calc
    _ ≤ ∑ i ∈ s, g (e i) := Finset.sum_le_sum hle
    _ = ∑ j ∈ s.image e, g j := (Finset.sum_image he).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub hzero
