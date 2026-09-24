import Surreal.Algebra.IdealCongruenceTopology
import Mathlib.RingTheory.Ideal.Lattice

/-!+# Closure of ideals in congruence topologies

Generic topological input to `osq:thm:closure`. For any directed ideal
neighborhood basis, closure of an ideal is the intersection of its sums
with the basic ideals. No separation assumption is needed.
-/

namespace Surreal.IdealCongruenceTopology

variable {R ι : Type*} [CommRing R] [Nonempty ι]
    (I : ι → Ideal R) (hI : ∀ i j, ∃ k, I k ≤ I i ⊓ I j)

/-- Congruence closure of any ideal is the intersection of its basic-neighborhood sums. -/
theorem closure_ideal (J : Ideal R) :
    @closure R (topology I hI) (J : Set R) = (⨅ i, J ⊔ I i : Ideal R) := by
  letI := topology I hI
  ext x
  rw [mem_closure_iff_nhds_basis (hasBasis_nhds I hI x)]
  simp only [SetLike.mem_coe, Ideal.mem_iInf]
  constructor
  · intro h i
    obtain ⟨y, hy, hxy⟩ := h i trivial
    have hneg := (I i).neg_mem hxy
    have he : y + -(y - x) = x := by ring
    exact he ▸ (J ⊔ I i).add_mem (Ideal.mem_sup_left hy) (Ideal.mem_sup_right hneg)
  · intro h i _
    obtain ⟨y, hy, z, hz, he⟩ := Submodule.mem_sup.mp (h i)
    refine ⟨y, hy, ?_⟩
    change y - x ∈ I i
    rw [← he, sub_add_cancel_left]
    exact (I i).neg_mem hz

end Surreal.IdealCongruenceTopology
