/- Modified for ProveIt: explicitly provide the finite chosen-basis index
instances for the lattice layers, avoiding a Lean 4.32 instance-search
timeout. The upstream theorem statement is unchanged. -/
import OAI.Combinatorics.Progressions.Fourier.EuclideanJetTorus

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module

theorem coefficientTorus_compact_of_lattice {K : Type*} [Fintype K] {m : ℕ}
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [∀ j, IsZLattice ℝ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] :
    CompactSpace (CoefficientTorus (K := K) U) := by
  classical
  let Λ := fun j => latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))
  let : ∀ j, Module.Finite ℤ (Λ j) := fun j => ZLattice.module_finite ℝ (Λ j)
  let : ∀ j, Fintype (Module.Free.ChooseBasisIndex ℤ (Λ j)) := fun j => inferInstance
  let b := fun j => Module.Free.chooseBasis ℤ (Λ j)
  let e := fun j => (euclideanSubspaceArrayEquiv (U j)).toLinearEquiv.trans
    (LinearEquiv.piUnique ℝ (fun _ : Unit => U j))
  apply coefficientTorus_compact_of_basis U
    (fun j => ((b j).ofZLatticeBasis ℝ (Λ j)).map (e j))
  intro j i a
  have hi := (euclideanSubspaceArrayEquiv_mem_lattice (U j)
    ((b j i : Λ j) : euclideanSubspace (U j))).mpr (b j i).property
  simpa only [Basis.map_apply, Basis.ofZLatticeBasis_apply, e,
    LinearEquiv.trans_apply, LinearEquiv.piUnique_apply, Equiv.piUnique,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv] using hi default a

end Erdos3.VectorPolynomial

end

end OAI
