import OAI.Combinatorics.Progressions.Estimates.ComparisonAmbient

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

variable {σ : Type} {L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

noncomputable def comparisonLattice (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.SquarefreeGridStable p B) : Subgroup
      (M.filtration.comparisonFiltration (fun i : ReplicatedIndex bound => i.1)).Group :=
  (M.comparisonAmbient p B hB hstable).lattice.comap
    (NilpotentLieBCHGroup.mapOfSteps M.comparisonToAmbient)

theorem comparisonLattice_first (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.SquarefreeGridStable p B) :
    M.comparisonLattice p B hB hstable ≤ D.lattice.comap
      (NilpotentLieBCHGroup.mapOfSteps
        (M.filtration.comparisonFirst (fun i : ReplicatedIndex bound => i.1))) := by
  intro g hg
  have hg' : NilpotentLieBCHGroup.mapOfSteps M.comparisonToAmbient g ∈
      (M.comparisonAmbient p B hB hstable).lattice := hg
  have h := (mem_piBCHSubgroup _ _ _).mp hg' none
  exact D.raiseStep_lattice_back (Nat.le_max_left s (Fintype.card (ReplicatedIndex bound))) h

theorem comparisonLattice_second (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.SquarefreeGridStable p B) :
    M.comparisonLattice p B hB hstable ≤ (M.squarefreeModel p B hB hstable).lattice.comap
      (NilpotentLieBCHGroup.mapOfSteps
        (M.filtration.comparisonSecond (fun i : ReplicatedIndex bound => i.1))) := by
  intro g hg
  have hg' : NilpotentLieBCHGroup.mapOfSteps M.comparisonToAmbient g ∈
      (M.comparisonAmbient p B hB hstable).lattice := hg
  have h := (mem_piBCHSubgroup _ _ _).mp hg' (some PUnit.unit)
  exact (M.squarefreeModel p B hB hstable).raiseStep_lattice_back
    (Nat.le_max_right s (Fintype.card (ReplicatedIndex bound))) h

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
