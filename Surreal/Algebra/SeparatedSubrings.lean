import Surreal.Algebra.NormalizationConductor
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.DiscreteSubset

/-!
# Uniformly separated subrings of ordered fields

The algebraic and topological steps of `osq:nm:thm:discrete`.
A common positive denominator into an integer part separates all distinct
points. The induced topology is discrete, and Mathlib's closed discrete
subgroup theorem supplies closedness without any cardinality assumption.
-/

namespace Surreal.SeparatedSubrings
noncomputable section

variable {R F : Type*} [CommRing R] [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  [Algebra R F]

/-- A common positive denominator into an integer part gives the reciprocal separation bound. -/
theorem separation_of_absorption (A : Subalgebra R F)
    (hfloor : ∀ x : F, ∃! a : R, algebraMap R F a ≤ x ∧ x < algebraMap R F a + 1)
    (d : F) (hd : 0 < d)
    (hclear : ∀ x ∈ A, ∃ a : R, algebraMap R F a = d * x) :
    ∀ x ∈ A, ∀ y ∈ A, x ≠ y → 1 / d ≤ |x - y| := by
  intro x hx y hy hne
  obtain ⟨a, ha⟩ := hclear (x - y) (A.sub_mem hx hy)
  have hn : algebraMap R F a ≠ 0 := by
    rw [ha]
    exact mul_ne_zero hd.ne' (sub_ne_zero.mpr hne)
  have h := NormalizationConductor.one_le_abs hfloor a hn
  rw [ha, abs_mul, abs_of_pos hd] at h
  exact (div_le_iff₀ hd).mpr (by nlinarith)

variable [TopologicalSpace F] [OrderTopology F]

/-- A positive uniform absolute-difference gap isolates every member of a subset. -/
theorem isDiscrete_of_separation (s : Set F) (r : F) (hr : 0 < r)
    (hsep : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → r ≤ |x - y|) : IsDiscrete s := by
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro x hx
  refine ⟨Set.Ioo (x - r) (x + r), isOpen_Ioo, ?_⟩
  ext y
  constructor
  · rintro ⟨hy, hys⟩
    apply Set.mem_singleton_iff.mpr
    by_contra hne
    have hlt : |y - x| < r := abs_lt.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
    exact (not_lt_of_ge (hsep y hys x hx hne)) hlt
  · intro hy
    obtain rfl := Set.mem_singleton_iff.mp hy
    exact ⟨⟨by linarith, by linarith⟩, hx⟩

/-- A uniformly separated subring is closed in the ambient order topology. -/
theorem isClosed_of_separation (A : Subring F) (r : F) (hr : 0 < r)
    (hsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → r ≤ |x - y|) : IsClosed (A : Set F) := by
  letI : DiscreteTopology A.toAddSubgroup :=
    isDiscrete_iff_discreteTopology.mp (isDiscrete_of_separation (A : Set F) r hr hsep)
  exact AddSubgroup.isClosed_of_discrete (H := A.toAddSubgroup)

end
end Surreal.SeparatedSubrings
