import OAI.Combinatorics.Progressions.Sampling.NativeSquarefreeGrids

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

def SquarefreeGridStable (p : ℝ) (B : ℕ) : Prop :=
  ∀ x ∈ coordinateGridModule (M.squarefreeBasis p) B,
    ∀ y ∈ coordinateGridModule (M.squarefreeBasis p) B,
      lieBCH (Fintype.card (ReplicatedIndex bound)) x y ∈ coordinateGridModule (M.squarefreeBasis p) B

noncomputable def squarefreeLattice (p : ℝ) (B : ℕ) (hstable : M.SquarefreeGridStable p B) :
    Subgroup (M.filtration.squarefreeOrdinaryFiltration (fun j : ReplicatedIndex bound => j.1)).Group :=
  coordinateGridBCHSubgroup (M.squarefreeBasis p) B
    (M.filtration.squarefreeOrdinaryFiltration (fun j : ReplicatedIndex bound => j.1)).lowerCentralSeries_eq_bot
    hstable

theorem squarefreeLattice_coordinates (p : ℝ) (B : ℕ) (hstable : M.SquarefreeGridStable p B) :
    bchSubgroupCoordinates (M.squarefreeBasis p) (M.squarefreeLattice p B hstable) = scaledIntegerGrid B :=
  coordinateGridBCHSubgroup_coordinates _ _ _ hstable

theorem squarefreeLattice_permute (p : ℝ) (B : ℕ) (hstable : M.SquarefreeGridStable p B)
    (e : Equiv.Perm (ReplicatedIndex bound)) (he : ∀ j, (e j).1 = j.1)
    (g : (M.filtration.squarefreeOrdinaryFiltration (fun j : ReplicatedIndex bound => j.1)).Group) :
    NilpotentLieBCHGroup.map
        (M.filtration.squarefreeBlockPermute (fun j : ReplicatedIndex bound => j.1) e he).toLieHom g ∈
        M.squarefreeLattice p B hstable ↔ g ∈ M.squarefreeLattice p B hstable :=
  M.squarefreeGrid_permute_iff p e he B g.coord

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
