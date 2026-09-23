import Surreal.Algebra.IntegerCongruenceLimit
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Profinite

/-!
# The topology of the ordinary congruence inverse limit

Topological prerequisites for `odg:eq:profinite`. Each quotient ring carries
the discrete topology, and the compatible sections carry the subspace
topology from their product. This is a Hausdorff, totally disconnected
topological ring, compact whenever all the quotient rings are finite.
Compatible component isomorphisms induce homeomorphisms of the inverse limits.
-/

universe u v

namespace Surreal.IntegerCongruenceLimit

open CategoryTheory Topology

variable (R : Type u) [CommRing R]

local instance quotientTopology (n : Modulus) : TopologicalSpace (R ⧸ ideal R n) := ⊥
local instance quotientDiscrete (n : Modulus) : DiscreteTopology (R ⧸ ideal R n) := ⟨rfl⟩

local instance diagramQuotientTopology (n : Modulus) :
    TopologicalSpace ((diagram R ⋙ forget₂ CommRingCat RingCat).obj n) := ⊥
local instance diagramQuotientDiscrete (n : Modulus) :
    DiscreteTopology ((diagram R ⋙ forget₂ CommRingCat RingCat).obj n) := ⟨rfl⟩

private abbrev sections : Subring (∀ n, R ⧸ ideal R n) :=
  RingCat.sectionsSubring (diagram R ⋙ forget₂ CommRingCat RingCat)

/-- The inverse limit has the subspace topology in the product of discrete quotient rings. -/
instance completionTopology : TopologicalSpace (Completion R) :=
  inferInstanceAs (TopologicalSpace ↥(sections R))

instance completionIsTopologicalRing : IsTopologicalRing (Completion R) :=
  inferInstanceAs (IsTopologicalRing ↥(sections R))

instance completionT2Space : T2Space (Completion R) :=
  inferInstanceAs (T2Space ↥(sections R))

instance completionTotallyDisconnectedSpace : TotallyDisconnectedSpace (Completion R) :=
  inferInstanceAs (TotallyDisconnectedSpace ↥(sections R))

/-- Every residue projection is continuous for the discrete topology on its target. -/
theorem continuous_projection (n : Modulus) : Continuous (projection R n) :=
  (continuous_apply n).comp
    (@continuous_subtype_val (∀ n, R ⧸ ideal R n) _ (fun x => x ∈ sections R))

/-- Continuity into the inverse limit is equivalent to continuity of all residue coordinates. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] (f : X → Completion R) :
    Continuous f ↔ ∀ n, Continuous (fun x => projection R n (f x)) := by
  have h : Continuous f ↔ Continuous (fun x => ((f x).val : ∀ n, R ⧸ ideal R n)) :=
    continuous_induced_rng
  exact h.trans continuous_pi_iff

/-- Fixing finitely many residues gives a neighborhood basis in the inverse limit. -/
theorem hasBasis_nhds (x : Completion R) :
    (𝓝 x).HasBasis Set.Finite
      (fun I : Set Modulus => {y | ∀ n ∈ I, projection R n y = projection R n x}) := by
  have h : (𝓝 (x.val : ∀ n, R ⧸ ideal R n)).HasBasis Set.Finite
      (fun I : Set Modulus => {y | ∀ n ∈ I, y n = x.val n}) := by
    rw [nhds_pi]
    simp only [nhds_discrete]
    exact Filter.hasBasis_pi_pure _
  rw [show (𝓝 x) = Filter.comap (fun y : Completion R => (y.val : ∀ n, R ⧸ ideal R n))
    (𝓝 (x.val : ∀ n, R ⧸ ideal R n)) from nhds_induced _ _]
  exact h.comap (fun y : Completion R => (y.val : ∀ n, R ⧸ ideal R n))

/-- The original ring is dense: any finite list of compatible residues has a common representative. -/
theorem denseRange_of : DenseRange (of R) := by
  classical
  intro x
  rw [mem_closure_iff_nhds_basis (hasBasis_nhds R x)]
  intro I hI
  let N : Modulus := ⟨∏ n ∈ hI.toFinset, n.val,
    Finset.prod_pos (fun n _ => n.positive)⟩
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (projection R N x)
  refine ⟨of R r, ⟨r, rfl⟩, ?_⟩
  intro n hn
  have hN : N ≤ n := Finset.dvd_prod_of_mem (fun n : Modulus => n.val) (hI.mem_toFinset.mpr hn)
  rw [← compatible R x hN, ← hr, projection_of, Ideal.Quotient.factor_mk]

/-- Compatibility is a closed condition in the product of discrete residue rings. -/
theorem isClosed_sections : IsClosed (sections R : Set (∀ n, R ⧸ ideal R n)) := by
  change IsClosed {x : ∀ n, R ⧸ ideal R n | ∀ (m n : Modulus) (f : m ⟶ n),
    Ideal.Quotient.factor (ideal_le R (leOfHom f)) (x m) = x n}
  simp only [Set.setOf_forall]
  apply isClosed_iInter
  intro m
  apply isClosed_iInter
  intro n
  apply isClosed_iInter
  intro f
  exact isClosed_eq (continuous_of_discreteTopology.comp (continuous_apply m)) (continuous_apply n)

/-- Finite quotient rings make the inverse limit compact. -/
instance completionCompactSpace [∀ n, Finite (R ⧸ ideal R n)] : CompactSpace (Completion R) :=
  isCompact_iff_compactSpace.mp (isClosed_sections R).isCompact

variable {R} {S : Type v} [CommRing S]
    (e : ∀ n, R ⧸ ideal R n ≃+* S ⧸ ideal S n)
    (he : ∀ {m n} (h : m ≤ n) x,
      e n (Ideal.Quotient.factor (ideal_le R h) x) =
        Ideal.Quotient.factor (ideal_le S h) (e m x))

/-- The isomorphism induced by component isomorphisms is continuous. -/
theorem continuous_congr : Continuous (congr e he) := by
  apply (continuous_iff S _).mpr
  intro n
  change Continuous (fun x => e n (projection R n x))
  exact continuous_of_discreteTopology.comp (continuous_projection R n)

/-- Its inverse is continuous as well. -/
theorem continuous_congr_symm : Continuous (congr e he).symm := by
  apply (continuous_iff R _).mpr
  intro n
  change Continuous (fun x => (e n).symm (projection S n x))
  exact continuous_of_discreteTopology.comp (continuous_projection S n)

/-- Compatible quotient isomorphisms give a homeomorphism for the inverse-limit topologies. -/
def congrHomeomorph : Completion R ≃ₜ Completion S where
  toEquiv := (congr e he).toEquiv
  continuous_toFun := continuous_congr e he
  continuous_invFun := continuous_congr_symm e he

@[simp] theorem congrHomeomorph_apply (x : Completion R) :
    congrHomeomorph e he x = congr e he x := rfl

end Surreal.IntegerCongruenceLimit
