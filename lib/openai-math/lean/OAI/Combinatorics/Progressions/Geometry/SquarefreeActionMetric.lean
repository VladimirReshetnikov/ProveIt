import OAI.Combinatorics.Progressions.Estimates.SquarefreeQuotientAction

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem nativeMap_dist_le
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)] {s t d e : ℕ}
    (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M t e)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hlattice : D.lattice ≤ E.lattice.comap (mapOfSteps
      (hL := D.filtration.lowerCentralSeries_eq_bot) (hM := E.filtration.lowerCentralSeries_eq_bot) φ))
    {p : ℝ} (hp : 0 ≤ p) (hD : D.GeometryComplexityLE p) (hE : E.GeometryComplexityLE p)
    (hφ : ∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p)
    (u v : D.RealGroup) :
    letI := D.metricSpace
    letI := E.metricSpace
    dist (QuotientGroup.mk (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ u) : E.Space)
      (QuotientGroup.mk (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ v)) ≤
          Real.exp ((p + 3) ^ 2) * dist (QuotientGroup.mk u : D.Space) (QuotientGroup.mk v) := by
  let := D.metricSpace
  let := E.metricSpace
  let := realificationQuotientMetricSpace D.basis D.lattice D.grid D.grid_pos D.outer_grid
  let := realificationQuotientMetricSpace E.basis E.lattice E.grid E.grid_pos E.outer_grid
  obtain ⟨K, _, hK, hLip⟩ := exists_realificationMap_quotient_lipschitz_exp_bound
    D.basis E.basis φ D.lattice E.lattice hlattice
    D.grid E.grid D.grid_pos E.grid_pos D.outer_grid E.outer_grid ⌈Real.exp p⌉₊
    (by linarith : 0 ≤ p + 1)
    (by simpa only [Fintype.card_fin] using hD.1.trans (by linarith : p ≤ p + 1))
    (by simpa only [Fintype.card_fin] using hE.1.trans (by linarith : p ≤ p + 1))
    (ceil_exp_le_exp_add_one hp) (fun i j => rationalHeightLE_ceil_exp (hφ i j))
  have hd := hLip.dist_le_mul (QuotientGroup.mk u) (QuotientGroup.mk v)
  change dist (QuotientGroup.mk (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ u) : E.Space)
    (QuotientGroup.mk (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := E.filtration.lowerCentralSeries_eq_bot) φ v)) ≤
        (K : ℝ) * dist (QuotientGroup.mk u : D.Space) (QuotientGroup.mk v) at hd
  apply hd.trans
  apply mul_le_mul_of_nonneg_right _ dist_nonneg
  simpa only [show p + 1 + 2 = p + 3 by ring] using hK

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem squarefreeFinBasis_permute (p : ℝ) (e : ReplicatedPermutation bound)
    (j : Fin (Fintype.card M.SquarefreeBasisIndex)) :
    ∃ k, M.filtration.replicatedLiePermute e (M.squarefreeFinBasis p j) = M.squarefreeFinBasis p k := by
  obtain ⟨k, hk⟩ := M.squarefreeBasis_permute p (replicatedPermutation bound e)
    (replicatedPermutation_block bound e) ((Fintype.equivFin M.SquarefreeBasisIndex).symm j)
  refine ⟨Fintype.equivFin M.SquarefreeBasisIndex k, ?_⟩
  simpa only [squarefreeFinBasis, Basis.reindex_apply, Equiv.symm_apply_apply,
    MultidegreeLieFiltration.replicatedLiePermute] using hk

theorem squarefreePermute_coordinate_height (p : ℝ) (e : ReplicatedPermutation bound)
    {q : ℝ} (hq : 0 ≤ q) (i j : Fin (Fintype.card M.SquarefreeBasisIndex)) :
    rationalLogHeight ((M.squarefreeFinBasis p).repr
      (M.filtration.replicatedLiePermute e (M.squarefreeFinBasis p j)) i) ≤ q := by
  obtain ⟨k, hk⟩ := M.squarefreeFinBasis_permute p e j
  rw [hk]
  simp only [Basis.repr_self, Finsupp.single_apply]
  split_ifs <;> simpa [rationalLogHeight] using hq

variable (p : ℝ) (B : ℕ) (hB : 0 < B) (hstable : M.SquarefreeGridStable p B)
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1))]

theorem squarefreeSpacePermute_lipschitz {q : ℝ} (hq : 0 ≤ q)
    (hE : (M.squarefreeModel p B hB hstable).GeometryComplexityLE q)
    (e : ReplicatedPermutation bound) :
    letI := (M.squarefreeModel p B hB hstable).metricSpace
    LipschitzWith ⟨Real.exp ((q + 3) ^ 2), (Real.exp_pos _).le⟩
      (M.squarefreeSpacePermute p B hB hstable e) := by
  let := (M.squarefreeModel p B hB hstable).metricSpace
  apply LipschitzWith.of_dist_le_mul
  intro x y
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      exact nativeMap_dist_le (M.squarefreeModel p B hB hstable) (M.squarefreeModel p B hB hstable)
        (M.filtration.replicatedLiePermute e).toLieHom
        (fun g hg => (M.squarefreeLattice_permute p B hstable (replicatedPermutation bound e)
          (replicatedPermutation_block bound e) g).mpr hg)
        hq hE hE (M.squarefreePermute_coordinate_height p e hq) x y

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
