import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Topology.Separation.Profinite

/-!
# The inverse-limit topology on Mathlib's adic completion

Topological prerequisites for `odg:eq:profinite`. The residue projections
embed the algebraic adic completion in the product of discrete ideal-power
quotients. A single residue class is a neighborhood basis, since the powers
form a chain. The canonical map has dense image and induces the original
ideal-adic topology, including when that topology is not Hausdorff.
-/

namespace Surreal.AdicCompletionTopology

open Topology

noncomputable section

variable {R : Type*} [CommRing R] (I : Ideal R)

local instance quotientTopology (n : ℕ) : TopologicalSpace (R ⧸ I ^ n) := ⊥
local instance quotientDiscrete (n : ℕ) : DiscreteTopology (R ⧸ I ^ n) := ⟨rfl⟩

/-- All ordinary ideal-power residue projections, as a single ring map. -/
def residues : AdicCompletion I R →+* ∀ n, R ⧸ I ^ n :=
  RingHom.pi (fun n => (AdicCompletion.evalₐ I n).toRingHom)

/-- The completion topology is induced from the product of discrete residue rings. -/
instance completionTopology : TopologicalSpace (AdicCompletion I R) :=
  TopologicalSpace.induced (residues I) inferInstance

/-- The residue map embeds the completion into the product of its discrete quotients. -/
theorem isEmbedding_residues : IsEmbedding (residues I) :=
  ⟨.induced _, fun _ _ h => AdicCompletion.ext_evalₐ (fun n => congrFun h n)⟩

/-- Every residue projection is continuous. -/
theorem continuous_eval (n : ℕ) : Continuous (AdicCompletion.evalₐ I n) :=
  (continuous_apply n).comp (isEmbedding_residues I).continuous

/-- Continuity into the completion can be checked on all residue projections. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] (f : X → AdicCompletion I R) :
    Continuous f ↔ ∀ n, Continuous (fun x => AdicCompletion.evalₐ I n (f x)) :=
  (isEmbedding_residues I).isInducing.continuous_iff.trans continuous_pi_iff

instance completionIsTopologicalRing : IsTopologicalRing (AdicCompletion I R) where
  continuous_add := (continuous_iff I _).mpr fun n => by
    simp only [map_add]
    exact
      ((continuous_eval I n).comp continuous_fst).add ((continuous_eval I n).comp continuous_snd)
  continuous_mul := (continuous_iff I _).mpr fun n => by
    simp only [map_mul]
    exact
      ((continuous_eval I n).comp continuous_fst).mul ((continuous_eval I n).comp continuous_snd)
  continuous_neg := (continuous_iff I _).mpr fun n => by
    simp only [map_neg]
    exact (continuous_eval I n).neg

instance completionT2Space : T2Space (AdicCompletion I R) :=
  (isEmbedding_residues I).t2Space

instance completionTotallyDisconnectedSpace : TotallyDisconnectedSpace (AdicCompletion I R) :=
  (isEmbedding_residues I).isTotallyDisconnected_range.mp
    (isTotallyDisconnected_of_totallyDisconnectedSpace _)

/-- Evaluation is compatible with all reductions to smaller ideal powers. -/
theorem eval_compatible {m n : ℕ} (h : m ≤ n) (x : AdicCompletion I R) :
    Ideal.Quotient.factorPow I h (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I m x := by
  obtain ⟨r, rfl⟩ := AdicCompletion.mk_surjective I R x
  simp only [AdicCompletion.evalₐ_mk, Ideal.Quotient.factor_mk]
  exact AdicCompletion.Ideal.mk_eq_mk I h r

/-- Fixing finitely many residues gives a neighborhood basis. -/
theorem hasBasis_nhds_finite (x : AdicCompletion I R) :
    (𝓝 x).HasBasis Set.Finite (fun s : Set ℕ =>
      {y | ∀ n ∈ s, AdicCompletion.evalₐ I n y = AdicCompletion.evalₐ I n x}) := by
  have h : (𝓝 (residues I x)).HasBasis Set.Finite
      (fun s : Set ℕ => {y | ∀ n ∈ s, y n = residues I x n}) := by
    rw [nhds_pi]
    simp only [nhds_discrete]
    exact Filter.hasBasis_pi_pure _
  exact (isEmbedding_residues I).isInducing.basis_nhds h

/-- One sufficiently high residue class refines every finite list of residue conditions. -/
theorem hasBasis_nhds (x : AdicCompletion I R) :
    (𝓝 x).HasBasis (fun _ : ℕ => True)
      (fun n => {y | AdicCompletion.evalₐ I n y = AdicCompletion.evalₐ I n x}) := by
  classical
  apply (hasBasis_nhds_finite I x).to_hasBasis
  · intro s hs
    refine ⟨hs.toFinset.sup id, trivial, ?_⟩
    intro y hy n hn
    have hle : n ≤ hs.toFinset.sup id := Finset.le_sup (f := id) (hs.mem_toFinset.mpr hn)
    rw [← eval_compatible I hle y, ← eval_compatible I hle x]
    exact congrArg (Ideal.Quotient.factorPow I hle) hy
  · intro n _
    exact ⟨{n}, Set.finite_singleton n, fun _ h => h n (Set.mem_singleton n)⟩

/-- The canonical completion map has dense image. -/
theorem denseRange_of : DenseRange (AdicCompletion.of I R) := by
  intro x
  rw [mem_closure_iff_nhds_basis (hasBasis_nhds I x)]
  intro n _
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  exact ⟨AdicCompletion.of I R r, ⟨r, rfl⟩, (AdicCompletion.evalₐ_of I n r).trans hr⟩

/-- The topology of the original ring is exactly that induced by its completion map. -/
theorem isInducing_of :
    @IsInducing R (AdicCompletion I R) I.adicTopology inferInstance (AdicCompletion.of I R) := by
  letI := I.adicTopology
  apply isInducing_iff_nhds.mpr
  intro x
  apply (I.hasBasis_nhds_adic x).eq_of_same_basis
  apply ((hasBasis_nhds I (AdicCompletion.of I R x)).comap (AdicCompletion.of I R)).congr
    (fun _ => Iff.rfl)
  intro n _
  ext y
  change AdicCompletion.evalₐ I n (AdicCompletion.of I R y) =
    AdicCompletion.evalₐ I n (AdicCompletion.of I R x) ↔ _
  rw [AdicCompletion.evalₐ_of, AdicCompletion.evalₐ_of, Ideal.Quotient.eq]
  constructor
  · intro hy
    exact ⟨y - x, hy, add_sub_cancel _ _⟩
  · rintro ⟨z, hz, rfl⟩
    rwa [add_sub_cancel_left]

end
end Surreal.AdicCompletionTopology
