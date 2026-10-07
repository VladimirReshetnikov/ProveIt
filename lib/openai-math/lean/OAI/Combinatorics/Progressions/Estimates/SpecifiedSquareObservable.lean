import OAI.Combinatorics.Progressions.Dynamics.ComparisonEquivalenceBudget
import OAI.Combinatorics.Progressions.Geometry.RealifiedSquareMetric
import OAI.Combinatorics.Progressions.Linear.NativeRankQuotientOrbit

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_specified_square_observable_lipschitz (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d m : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L (s + 1) d)
      [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      (b : Basis (Fin m) ℚ L) (v : Fin m → ℕ)
      (h2 : D.filtration.layer 2 = Submodule.span ℚ (b '' {i | 2 ≤ v i}))
      (N : ℕ) (hN : 0 < N)
      (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis b v h2)
        (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N)
      {ω : σ → ℕ} (T : D.Niltest ω) {p : ℝ},
      0 ≤ p → T.ComplexityLE p →
      (Fintype.card (Fin m ⊕ {i // 2 ≤ v i}) : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ p) →
      ∀ η : D.RealGroup,
        (∀ i, |(D.basis.baseChange ℝ).repr η.coord i| ≤ Real.exp p) →
        ∃ ℓ : ℝ≥0, (ℓ : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          letI := realificationQuotientMetricSpace (D.filtration.squareFinBasis b v h2)
            (D.filtration.squareLattice D.lattice) N hN hout
          LipschitzWith ℓ (D.filtration.realSquareObservable D.lattice η T.observable) := by
  obtain ⟨B, _, hleft⟩ := exists_bounded_normalization_left_lipschitz (s + 1) 1
  let X : Polynomial ℕ := Polynomial.X
  let P := 2 * X + (X + 3) ^ 2 + (X + 3 + Polynomial.C B) ^ B + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ d m _ _ _ _ D _ _ _ _ b v h2 N hN hout ω T p hp hT hdim hb η hη
  obtain ⟨A, _, hA, hALip⟩ := hleft D p hp hT.1
  have hηLip := hALip η (fun i => (hη i).trans (Real.exp_le_exp.mpr (by norm_num; linarith)))
  let H := ⌈Real.exp p⌉₊
  let n := Fintype.card (Fin m ⊕ {i // 2 ≤ v i})
  let J := coordinateLipschitzBound (Fintype.card (Fin d)) (Fintype.card (Fin n)) H
  have hJ : (J : ℝ) ≤ Real.exp ((p + 3) ^ 2) := by
    change (coordinateLipschitzBound (Fintype.card (Fin d)) (Fintype.card (Fin n)) H : ℝ) ≤ _
    have h := coordinateLipschitzBound_le_exp (Fintype.card (Fin d)) (Fintype.card (Fin n)) H
      (show 0 ≤ p + 1 by linarith)
      (by simpa only [Fintype.card_fin] using hT.1.1.trans (by linarith : p ≤ p + 1))
      (by simpa only [Fintype.card_fin] using hdim.trans (by linarith : p ≤ p + 1))
      (ceil_exp_le_exp_add_one hp)
    simpa only [show p + 1 + 2 = p + 3 by ring] using h
  have hproj := D.filtration.squareFinBasis_projection_height D.basis b v h2
    (one_le_ceil_exp p) (fun i j => rationalHeightLE_ceil_exp (hb j i))
  let ℓ := T.normBound * (T.lipBound * J) + T.normBound * (T.lipBound * (A * J))
  have hnorm : (T.normBound : ℝ) ≤ Real.exp p := by
    have h := T.observable_budget hT
    linarith [T.lipBound.coe_nonneg]
  have hlip : (T.lipBound : ℝ) ≤ Real.exp p := by
    have h := T.observable_budget hT
    linarith [T.normBound.coe_nonneg]
  have hℓ := squareObservableLipschitz_le_exp A T.normBound T.lipBound J
    (normalizedSquareLeftBudget_nonneg 1 B hp) hA hnorm hlip hJ
  have hcost : 2 * p + (p + 3) ^ 2 + normalizedSquareLeftBudget 1 B p + 1 ≤ (p + C) ^ C := by
    have hleft : normalizedSquareLeftBudget 1 B p = (p + 3 + B) ^ B := by
      unfold normalizedSquareLeftBudget
      congr 1
      ring
    rw [hleft]
    simpa [P, X, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨ℓ, hℓ.trans (Real.exp_le_exp.mpr hcost), ?_⟩
  exact D.filtration.realSquareObservable_lipschitz D.basis
    (D.filtration.squareFinBasis b v h2) D.lattice D.grid N H D.grid_pos hN D.outer_grid hout
    (fun k i => (hproj i k).1) (fun k i => (hproj i k).2)
    η T.observable A T.lipBound T.normBound hηLip T.lipschitz T.norm_le

end Erdos3.RationalFilteredNilmanifold

end

end OAI
