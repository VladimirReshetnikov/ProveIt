import Surreal.Algebra.IntegerCongruenceLimitTopology
import Surreal.Foundations.OmnificProfiniteCompletion
import Surreal.Foundations.OmnificCongruenceTopology
import Mathlib.Topology.DenseEmbedding

/-!
# The profinite topology and omnific completion homeomorphism

The profinite topological isomorphism in `odg:eq:profinite`. Both inverse
limits have their standard subspace topologies in products of finite
discrete quotient rings. They are compact Hausdorff totally disconnected
topological rings. The previously proved ring isomorphism is a homeomorphism,
and the canonical map from the omnific congruence topology is continuous.
-/

universe u

namespace Surreal.Foundations.SignSequence

open IntegerCongruenceLimit Topology

noncomputable section

/-- Finiteness of all actual omnific residue rings makes their inverse limit compact. -/
instance omnificProfiniteCompletionCompactSpace : CompactSpace OmnificProfiniteCompletion.{u} := by
  letI : ∀ n, Finite (OmnificInteger.{u} ⧸ ideal OmnificInteger n) :=
    omnificCongruenceQuotient_finite
  infer_instance

/-- The ordinary profinite integer ring is compact in its inverse-limit topology. -/
instance profiniteIntegerCompactSpace : CompactSpace ProfiniteInteger := by
  letI : ∀ n, Finite (ℤ ⧸ ideal ℤ n) := fun n => by
    letI : NeZero n.val := ⟨n.positive.ne'⟩
    exact Finite.of_injective (Int.quotientSpanNatEquivZMod n.val)
      (Int.quotientSpanNatEquivZMod n.val).injective
  infer_instance

/-- The profinite ring isomorphism is a homeomorphism for the inverse-limit topologies. -/
def omnificProfiniteHomeomorph : OmnificProfiniteCompletion.{u} ≃ₜ ProfiniteInteger :=
  IntegerCongruenceLimit.congrHomeomorph omnificCongruenceQuotientEquiv
    omnificCongruenceQuotientEquiv_compatible

/-- The homeomorphism has exactly the previously constructed ring isomorphism as its function. -/
@[simp] theorem omnificProfiniteHomeomorph_apply (x : OmnificProfiniteCompletion.{u}) :
    omnificProfiniteHomeomorph x = omnificProfiniteCompletionEquiv x := rfl

/-- The topological identification preserves the canonical constant-term completion map. -/
theorem omnificProfiniteHomeomorph_of (x : OmnificInteger.{u}) :
    omnificProfiniteHomeomorph (omnificProfiniteMap x) =
      IntegerCongruenceLimit.of ℤ (omnificConstantCoeff x) :=
  omnificProfiniteCompletionEquiv_of x

/-- Actual omnific integers have dense image in their profinite completion. -/
theorem denseRange_omnificProfiniteMap : DenseRange omnificProfiniteMap.{u} :=
  IntegerCongruenceLimit.denseRange_of OmnificInteger

/-- Ordinary integer constants have dense image in the ordinary profinite integer ring. -/
theorem denseRange_profiniteInteger_of : DenseRange (IntegerCongruenceLimit.of ℤ) :=
  IntegerCongruenceLimit.denseRange_of ℤ

/-- The canonical map into the profinite completion is continuous for ordinary congruences. -/
theorem continuous_omnificProfiniteMap :
    @Continuous OmnificInteger.{u} OmnificProfiniteCompletion omnificCongruenceTopology
      inferInstance omnificProfiniteMap := by
  letI := omnificCongruenceTopology.{u}
  apply (IntegerCongruenceLimit.continuous_iff OmnificInteger _).mpr
  intro n
  rw [continuous_def]
  intro s _
  rw [isOpen_iff_mem_nhds]
  intro x hx
  apply (omnificCongruenceTopology_hasBasis x).mem_iff.mpr
  refine ⟨⟨n.val, n.positive⟩, trivial, ?_⟩
  intro y hy
  have hxy : Ideal.Quotient.mk (ideal OmnificInteger n) y =
      Ideal.Quotient.mk (ideal OmnificInteger n) x := by
    apply Ideal.Quotient.eq.mpr
    rw [ideal, Ideal.mem_span_singleton]
    change omnificIntCast (n.val : ℤ) ∣ y - x at hy
    simpa only [map_natCast] using hy
  change Ideal.Quotient.mk (ideal OmnificInteger n) y ∈ s
  rw [hxy]
  exact hx

/-- The congruence topology is exactly the topology induced by the profinite completion map. -/
theorem isInducing_omnificProfiniteMap :
    @Topology.IsInducing OmnificInteger.{u} OmnificProfiniteCompletion omnificCongruenceTopology
      inferInstance omnificProfiniteMap := by
  letI := omnificCongruenceTopology.{u}
  apply Topology.isInducing_iff_nhds.mpr
  intro x
  apply le_antisymm
  · exact continuous_omnificProfiniteMap.continuousAt.le_comap
  · apply ((IntegerCongruenceLimit.hasBasis_nhds OmnificInteger (omnificProfiniteMap x)).comap
      omnificProfiniteMap).le_basis_iff (omnificCongruenceTopology_hasBasis x) |>.mpr
    intro n _
    let m : Modulus := ⟨n.val, n.property⟩
    refine ⟨{m}, Set.finite_singleton m, ?_⟩
    intro y hy
    have hxy := hy m (Set.mem_singleton m)
    change Ideal.Quotient.mk (ideal OmnificInteger m) y =
      Ideal.Quotient.mk (ideal OmnificInteger m) x at hxy
    have hm := Ideal.Quotient.eq.mp hxy
    change omnificIntCast (n.val : ℤ) ∣ y - x
    rw [map_natCast]
    exact Ideal.mem_span_singleton.mp hm

/-- The canonical completion map is dense and induces exactly the original congruence topology. -/
theorem isDenseInducing_omnificProfiniteMap :
    @IsDenseInducing OmnificInteger.{u} OmnificProfiniteCompletion omnificCongruenceTopology
      inferInstance omnificProfiniteMap := by
  letI := omnificCongruenceTopology.{u}
  exact ⟨isInducing_omnificProfiniteMap, denseRange_omnificProfiniteMap⟩

end
end Surreal.Foundations.SignSequence
