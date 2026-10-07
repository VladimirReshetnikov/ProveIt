import OAI.Combinatorics.Progressions.Lattices.ComparisonLattice

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ : Type} {L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d r : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound) (p : ℝ) (B : ℕ) (hB : 0 < B)
  (hstable : M.SquarefreeGridStable p B)
  (E : RationalFilteredNilmanifold
    (M.filtration.comparisonSubalgebra (fun i : ReplicatedIndex bound => i.1))
    (max s (Fintype.card (ReplicatedIndex bound))) r)
  (hEL : E.lattice = M.comparisonLattice p B hB hstable)

noncomputable def comparisonFirstSpace : E.Space → D.Space :=
  cosetMap E.realLattice D.realLattice
    (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot)
      (M.filtration.comparisonFirst (fun i : ReplicatedIndex bound => i.1)))
    (realificationMap_subgroup _ _ _ (by rw [hEL]; exact M.comparisonLattice_first p B hB hstable))

noncomputable def comparisonSecondSpace : E.Space → (M.squarefreeModel p B hB hstable).Space :=
  cosetMap E.realLattice (M.squarefreeModel p B hB hstable).realLattice
    (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
      (hM := (M.squarefreeModel p B hB hstable).filtration.lowerCentralSeries_eq_bot)
      (M.filtration.comparisonSecond (fun i : ReplicatedIndex bound => i.1)))
    (realificationMap_subgroup _ _ _ (by rw [hEL]; exact M.comparisonLattice_second p B hB hstable))

theorem comparisonFirstSpace_mk (g : E.RealGroup) :
    M.comparisonFirstSpace p B hB hstable E hEL (QuotientGroup.mk g) =
      QuotientGroup.mk (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot)
        (M.filtration.comparisonFirst (fun i : ReplicatedIndex bound => i.1)) g) := rfl

theorem comparisonSecondSpace_mk (g : E.RealGroup) :
    M.comparisonSecondSpace p B hB hstable E hEL (QuotientGroup.mk g) =
      QuotientGroup.mk (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := (M.squarefreeModel p B hB hstable).filtration.lowerCentralSeries_eq_bot)
        (M.filtration.comparisonSecond (fun i : ReplicatedIndex bound => i.1)) g) := rfl

theorem comparisonFirstSpace_smul (g : E.RealGroup) (x : E.Space) :
    M.comparisonFirstSpace p B hB hstable E hEL (g • x) =
      realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot)
        (M.filtration.comparisonFirst (fun i : ReplicatedIndex bound => i.1)) g •
        M.comparisonFirstSpace p B hB hstable E hEL x := cosetMap_smul _ _ _ _ _ _

theorem comparisonSecondSpace_smul (g : E.RealGroup) (x : E.Space) :
    M.comparisonSecondSpace p B hB hstable E hEL (g • x) =
      realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := (M.squarefreeModel p B hB hstable).filtration.lowerCentralSeries_eq_bot)
        (M.filtration.comparisonSecond (fun i : ReplicatedIndex bound => i.1)) g •
        M.comparisonSecondSpace p B hB hstable E hEL x := cosetMap_smul _ _ _ _ _ _

variable
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.comparisonSubalgebra (fun i : ReplicatedIndex bound => i.1))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.comparisonSubalgebra (fun i : ReplicatedIndex bound => i.1))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.comparisonSubalgebra (fun i : ReplicatedIndex bound => i.1))]
  [T2Space (ℝ ⊗[ℚ] M.filtration.comparisonSubalgebra (fun i : ReplicatedIndex bound => i.1))]

theorem comparisonFirstSpace_lipschitz
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {q : ℝ} (hq : 0 ≤ q) (hD : D.GeometryComplexityLE q) (hE : E.GeometryComplexityLE q)
    (hheight : ∀ j k, rationalLogHeight (D.basis.repr (E.basis j).val.1 k) ≤ q) :
    letI := E.metricSpace
    letI := D.metricSpace
    LipschitzWith ⟨Real.exp ((q + 3) ^ 2), (Real.exp_pos _).le⟩
      (M.comparisonFirstSpace p B hB hstable E hEL) := by
  let := E.metricSpace
  let := D.metricSpace
  apply LipschitzWith.of_dist_le_mul
  intro x y
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      exact nativeMap_dist_le E D
        (M.filtration.comparisonFirst (fun i : ReplicatedIndex bound => i.1))
        (by rw [hEL]; exact M.comparisonLattice_first p B hB hstable)
        hq hE hD (fun k j => hheight j k) x y

theorem comparisonSecondSpace_lipschitz
    [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun i : ReplicatedIndex bound => i.1))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun i : ReplicatedIndex bound => i.1))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun i : ReplicatedIndex bound => i.1))]
    [T2Space (ℝ ⊗[ℚ] M.filtration.SquarefreeAlgebra (fun i : ReplicatedIndex bound => i.1))]
    {q : ℝ} (hq : 0 ≤ q)
    (hA : (M.squarefreeModel p B hB hstable).GeometryComplexityLE q)
    (hE : E.GeometryComplexityLE q)
    (hheight : ∀ j k, rationalLogHeight ((M.squarefreeFinBasis p).repr (E.basis j).val.2 k) ≤ q) :
    letI := E.metricSpace
    letI := (M.squarefreeModel p B hB hstable).metricSpace
    LipschitzWith ⟨Real.exp ((q + 3) ^ 2), (Real.exp_pos _).le⟩
      (M.comparisonSecondSpace p B hB hstable E hEL) := by
  let := E.metricSpace
  let := (M.squarefreeModel p B hB hstable).metricSpace
  apply LipschitzWith.of_dist_le_mul
  intro x y
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      exact nativeMap_dist_le E (M.squarefreeModel p B hB hstable)
        (M.filtration.comparisonSecond (fun i : ReplicatedIndex bound => i.1))
        (by rw [hEL]; exact M.comparisonLattice_second p B hB hstable)
        hq hE hA (fun k j => hheight j k) x y

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
