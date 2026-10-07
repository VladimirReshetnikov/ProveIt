import OAI.Combinatorics.Progressions.Linear.ComparisonChosenLayerBasis

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem squarefreeGrid_permute (p : ℝ) (e : Equiv.Perm (ReplicatedIndex bound))
    (he : ∀ j, (e j).1 = j.1) (B : ℕ)
    {x : M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1)}
    (hx : x ∈ coordinateGridModule (M.squarefreeBasis p) B) :
    M.filtration.squarefreeBlockPermute (fun j : ReplicatedIndex bound => j.1) e he x ∈
      coordinateGridModule (M.squarefreeBasis p) B :=
  coordinateGridModule_map_of_basis (M.squarefreeBasis p) (M.squarefreeBasis p)
    (M.filtration.squarefreeBlockPermute (fun j : ReplicatedIndex bound => j.1) e he).toLinearEquiv.toLinearMap
    (M.squarefreeBasis_permute p e he) B hx

theorem squarefreeGrid_permute_iff (p : ℝ) (e : Equiv.Perm (ReplicatedIndex bound))
    (he : ∀ j, (e j).1 = j.1) (B : ℕ)
    (x : M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1)) :
    M.filtration.squarefreeBlockPermute (fun j : ReplicatedIndex bound => j.1) e he x ∈
      coordinateGridModule (M.squarefreeBasis p) B ↔ x ∈ coordinateGridModule (M.squarefreeBasis p) B := by
  constructor
  · intro hx
    have h := M.squarefreeGrid_permute p e.symm
      (MultidegreeLieFiltration.blockPermutation_symm _ e he) B hx
    have heq : M.filtration.squarefreeBlockPermute (fun j : ReplicatedIndex bound => j.1) e.symm
        (MultidegreeLieFiltration.blockPermutation_symm _ e he)
        (M.filtration.squarefreeBlockPermute (fun j : ReplicatedIndex bound => j.1) e he x) = x :=
      Subtype.ext (squarefreePermute_symm_apply e x.val)
    rwa [heq] at h
  · exact M.squarefreeGrid_permute p e he B

theorem exists_squarefree_stable_grid {p : ℝ} (hM : M.ComplexityLE p) (l : ℕ) (hl : 0 < l) :
    ∃ B : ℕ, 0 < B ∧ l ∣ B ∧
      B ≤ bchIntegralDenominatorBound (Fintype.card (ReplicatedIndex bound)) *
        squarefreeStructureHeight d ⌈Real.exp p⌉₊ ^ (Fintype.card M.SquarefreeBasisIndex ^ 3) * l ∧
      ∀ x ∈ coordinateGridModule (M.squarefreeBasis p) B,
        ∀ y ∈ coordinateGridModule (M.squarefreeBasis p) B,
          lieBCH (Fintype.card (ReplicatedIndex bound)) x y ∈ coordinateGridModule (M.squarefreeBasis p) B :=
  exists_bch_stable_integral_grid (M.squarefreeBasis p)
    (M.filtration.squarefreeOrdinaryFiltration (fun j : ReplicatedIndex bound => j.1)).lowerCentralSeries_eq_bot
    l hl (M.squarefreeBasis_structure_height hM)

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
