import Mathlib.Topology.Algebra.Nonarchimedean.Bases
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.UniformRing

/-!
# Congruence topologies from families of ideals

Generic prerequisites for the topology assertions following `odg:eq:profinite`.
A downward directed, nonempty family of ideals defines a ring topology. Its
closure of zero is their intersection, so the intersection detects both
topological indistinguishability and the Hausdorff property.
-/

namespace Surreal.IdealCongruenceTopology

open Topology

variable {R ι : Type*} [CommRing R] [Nonempty ι]
    (I : ι → Ideal R) (hI : ∀ i j, ∃ k, I k ≤ I i ⊓ I j)

include hI in
omit [Nonempty ι] in
/-- A directed family of ideals supplies Mathlib's ring subgroup basis. -/
theorem basis : RingSubgroupsBasis (fun i => (I i).toAddSubgroup) := by
  apply RingSubgroupsBasis.of_comm
  · intro i j
    obtain ⟨k, hk⟩ := hI i j
    exact ⟨k, hk⟩
  · intro i
    refine ⟨i, ?_⟩
    rintro _ ⟨x, _, y, hy, rfl⟩
    exact (I i).mul_mem_left x hy
  · intro x i
    exact ⟨i, fun _ hy => (I i).mul_mem_left x hy⟩

/-- The ring topology whose basic neighborhoods of zero are the given ideals. -/
@[implicit_reducible] def topology : TopologicalSpace R := (basis I hI).topology

/-- Ring operations are continuous for the congruence topology. -/
theorem isTopologicalRing : @IsTopologicalRing R (topology I hI) _ :=
  (basis I hI).toRingFilterBasis.isTopologicalRing

/-- The ideal cosets form the neighborhood basis at every point. -/
theorem hasBasis_nhds (x : R) :
    (@nhds R (topology I hI) x).HasBasis (fun _ : ι => True)
      (fun i => {y | y - x ∈ I i}) :=
  (basis I hI).hasBasis_nhds x

/-- The given ideals themselves are a neighborhood basis at zero. -/
theorem hasBasis_nhds_zero :
    (@nhds R (topology I hI) 0).HasBasis (fun _ : ι => True)
      (fun i => (I i : Set R)) :=
  (basis I hI).hasBasis_nhds_zero

omit [Nonempty ι] in
/-- Any ideal neighborhood basis identifies the closure of zero with its intersection. -/
theorem closure_zero_of_hasBasis [TopologicalSpace R] [IsTopologicalRing R]
    (h : (𝓝 (0 : R)).HasBasis (fun _ : ι => True) (fun i => (I i : Set R))) :
    closure ({0} : Set R) = (⨅ i, I i : Ideal R) := by
  rw [R0Space.closure_singleton, h.ker, Submodule.coe_iInf]
  simp only [Set.iInter_true]

/-- The closure of zero in a congruence topology is precisely the ideal intersection. -/
theorem closure_zero :
    @closure R (topology I hI) {0} = (⨅ i, I i : Ideal R) := by
  letI := topology I hI
  letI := isTopologicalRing I hI
  exact closure_zero_of_hasBasis I (hasBasis_nhds_zero I hI)

/-- Two points are indistinguishable exactly when their difference lies in every ideal. -/
theorem inseparable_iff (x y : R) :
    @Inseparable R (topology I hI) x y ↔ x - y ∈ ⨅ i, I i := by
  letI := topology I hI
  letI := isTopologicalRing I hI
  rw [addGroup_inseparable_iff]
  change x - y ∈ closure ({0} : Set R) ↔ _
  rw [closure_zero]
  rfl

/-- A congruence topology is Hausdorff exactly when the ideal intersection is zero. -/
theorem t2Space_iff : @T2Space R (topology I hI) ↔ (⨅ i, I i) = ⊥ := by
  letI := topology I hI
  letI := isTopologicalRing I hI
  rw [IsTopologicalAddGroup.t2Space_iff_zero_closed, ← closure_eq_iff_isClosed, closure_zero]
  constructor
  · intro h
    exact SetLike.coe_injective h
  · intro h
    rw [h]
    rfl

/-- Identifying the closure of zero identifies Mathlib's separation quotient as a ring. -/
noncomputable def separationQuotientEquiv [TopologicalSpace R] [IsTopologicalRing R]
    (J : Ideal R) (h : closure ({0} : Set R) = (J : Set R)) :
    SeparationQuotient R ≃+* R ⧸ J :=
  (UniformSpace.sepQuotRingEquivRingQuot R).trans
    (Ideal.quotEquivOfEq (show (⊥ : Ideal R).closure = J from SetLike.coe_injective h))

/-- The separation-quotient equivalence preserves the class of each ring element. -/
@[simp] theorem separationQuotientEquiv_mk [TopologicalSpace R] [IsTopologicalRing R]
    (J : Ideal R) (h : closure ({0} : Set R) = (J : Set R)) (x : R) :
    separationQuotientEquiv J h (SeparationQuotient.mk x) = Ideal.Quotient.mk J x := rfl

end Surreal.IdealCongruenceTopology
