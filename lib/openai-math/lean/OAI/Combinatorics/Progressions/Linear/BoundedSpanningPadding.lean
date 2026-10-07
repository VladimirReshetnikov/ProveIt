/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.BoundedSubmoduleIntersection

namespace OAI

section

namespace Erdos3

open Module

variable {ι η L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  (e : Basis ι ℚ L) (K : LieSubalgebra ℚ L)

theorem exists_bounded_ambient_spanning (v : η → K)
    (hspan : Submodule.span ℚ (Set.range v) = ⊤) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ a i, RationalHeightLE (e.repr (v a : L) i) H) :
    ∃ w : Fin (Fintype.card ι) → L,
      Submodule.span ℚ (Set.range w) = K.toSubmodule ∧
        ∀ a i, RationalHeightLE (e.repr (w a) i) H := by
  classical
  obtain ⟨b, hb⟩ := exists_bounded_lie_subalgebra_basis e K v hspan hv
  have hr := lie_subalgebra_finrank_le e K
  let w : Fin (Fintype.card ι) → L := fun a =>
    if ha : a.val < Module.finrank ℚ K then (b ⟨a.val, ha⟩ : L) else 0
  have hw (i : Fin (Module.finrank ℚ K)) :
      w ⟨i.val, lt_of_lt_of_le i.isLt hr⟩ = (b i : L) := by
    simp only [w, dite_eq_left i.isLt]
  refine ⟨w, ?_, ?_⟩
  · apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro x ⟨a, rfl⟩
      dsimp only [w]
      split_ifs with ha
      · exact (b ⟨a.val, ha⟩).property
      · exact K.zero_mem
    · have htop : (⊤ : Submodule ℚ K) ≤
          (Submodule.span ℚ (Set.range w)).comap K.incl.toLinearMap := by
        rw [← b.span_eq]
        apply Submodule.span_le.mpr
        rintro y ⟨i, rfl⟩
        change (b i : L) ∈ Submodule.span ℚ (Set.range w)
        rw [← hw i]
        exact Submodule.subset_span ⟨_, rfl⟩
      intro x hx
      exact htop (show (⟨x, hx⟩ : K) ∈ (⊤ : Submodule ℚ K) by trivial)
  · intro a i
    dsimp only [w]
    split_ifs with ha
    · exact hb ⟨a.val, ha⟩ i
    · simpa only [map_zero, Finsupp.zero_apply] using rationalHeightLE_zero hH

theorem bounded_spanning_mem_heightBoundedLieSubalgebras (v : η → K)
    (hspan : Submodule.span ℚ (Set.range v) = ⊤) {H : ℕ} (hH : 1 ≤ H)
    (hv : ∀ a i, RationalHeightLE (e.repr (v a : L) i) H) :
    K ∈ heightBoundedLieSubalgebras e (Fintype.card ι) H := by
  obtain ⟨w, hw, hh⟩ := exists_bounded_ambient_spanning e K v hspan hH hv
  exact (mem_heightBoundedSubspaces e (Fintype.card ι) H K.toSubmodule).mpr ⟨w, hw, hh⟩

end Erdos3

end

end OAI
