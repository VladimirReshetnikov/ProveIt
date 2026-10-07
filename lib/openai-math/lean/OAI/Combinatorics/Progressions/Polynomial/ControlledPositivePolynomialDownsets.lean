import OAI.Combinatorics.Progressions.Dynamics.SquarefreeModelBudget
import OAI.Combinatorics.Progressions.Estimates.NativePositiveCoefficientBases

namespace OAI

section

namespace Erdos3

noncomputable def positivePolynomialInputBudget (t : ℕ) (p : ℝ) : ℝ :=
  p + 1 + squarefreeInputBudget t p

noncomputable def positivePolynomialDenominatorBudget (t : ℕ) (p : ℝ) : ℝ :=
  positivePolynomialInputBudget t p + (positivePolynomialInputBudget t p + 2) ^ 4

noncomputable def positivePolynomialModelBudget (t : ℕ) (p : ℝ) : ℝ :=
  positivePolynomialDenominatorBudget t p +
    (positivePolynomialDenominatorBudget t p + (bchIntegralDenominatorBound t + 5 : ℕ)) ^
      (bchIntegralDenominatorBound t + 5)

theorem positivePolynomialInputBudget_nonneg (t : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ positivePolynomialInputBudget t p :=
  add_nonneg (by linarith) (squarefreeInputBudget_nonneg t hp)

theorem squarefreeInputBudget_le_positive (t : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    squarefreeInputBudget t p ≤ positivePolynomialInputBudget t p :=
  le_add_of_nonneg_left (by linarith)

theorem positivePolynomialInputBudget_le_denominator (t : ℕ) (p : ℝ) :
    positivePolynomialInputBudget t p ≤ positivePolynomialDenominatorBudget t p :=
  le_add_of_nonneg_right (by positivity)

theorem positivePolynomialDenominatorBudget_le_model (t : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    positivePolynomialDenominatorBudget t p ≤ positivePolynomialModelBudget t p := by
  have h := (positivePolynomialInputBudget_nonneg t hp).trans
    (positivePolynomialInputBudget_le_denominator t p)
  exact le_add_of_nonneg_right (pow_nonneg (add_nonneg h (Nat.cast_nonneg _)) _)

theorem exists_positivePolynomialModel_budget (t : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      positivePolynomialModelBudget t p ≤ (p + C) ^ C := by
  let Q : Polynomial ℕ := Polynomial.X + 1 +
    (Polynomial.C (2 ^ t) * Polynomial.X + (Polynomial.X + 3) ^ 8)
  let R : Polynomial ℕ := Q + (Q + 2) ^ 4
  let K := bchIntegralDenominatorBound t + 5
  obtain ⟨C, hC, h⟩ := exists_natPolynomial_eval_budget (R + (R + Polynomial.C K) ^ K)
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa only [positivePolynomialModelBudget, positivePolynomialDenominatorBudget,
    positivePolynomialInputBudget, squarefreeInputBudget, R, Q, K,
    Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_one,
    Polynomial.eval₂_ofNat, map_pow, map_ofNat, Nat.coe_castRingHom] using h p hp

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module MultidegreeLieFiltration
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

abbrev PositivePolynomialBasisIndex := Σ a : BoxedDegreeIndex bound,
  Fin (finrank ℚ (M.filtration.positiveCoefficientLayer a))

noncomputable def positivePolynomialBasis (p : ℝ) :
    Basis M.PositivePolynomialBasisIndex ℚ M.filtration.positivePolynomialAlgebra :=
  M.filtration.positivePolynomialBasis (M.positiveCoefficientBasis p)

theorem positivePolynomialBasisIndex_card_le (p : ℝ) :
    Fintype.card M.PositivePolynomialBasisIndex ≤ 2 ^ (∑ i, bound i) * d := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  rw [← finrank_eq_card_basis (M.positivePolynomialBasis p)]
  simpa only [finrank_eq_card_basis D.basis, Fintype.card_fin] using
    M.filtration.positivePolynomial_finrank_le_total

omit [DecidableEq σ] in
theorem positiveCoefficientBasis_card_le (a : BoxedDegreeIndex bound) :
    finrank ℚ (M.filtration.positiveCoefficientLayer a) ≤ d := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  simpa only [finrank_eq_card_basis D.basis, Fintype.card_fin] using
    (M.filtration.positiveCoefficientLayer a).finrank_le

omit [DecidableEq σ] in
theorem positivePolynomialBasis_structure_height {p : ℝ} (hM : M.ComplexityLE p)
    (i j k : M.PositivePolynomialBasisIndex) :
    RationalHeightLE (lieStructureConstants (M.positivePolynomialBasis p) i j k)
      (squarefreeStructureHeight d ⌈Real.exp p⌉₊) := by
  have h := M.filtration.positivePolynomialBasis_structure_height
    (M.positiveCoefficientBasis p) D.basis (one_le_ceil_exp p)
    (M.positiveCoefficientBasis_height hM)
    (fun i j k => rationalHeightLE_ceil_exp (hM.1.2.2.1 i j k))
    (fun a => by simpa only [Fintype.card_fin] using M.positiveCoefficientBasis_card_le a) i j k
  simpa only [positivePolynomialBasis, Fintype.card_fin] using h

omit [DecidableEq σ] in
theorem positivePolynomialBasis_evaluation_height {p : ℝ} (hM : M.ComplexityLE p)
    (i : M.PositivePolynomialBasisIndex) (k : Fin d) :
    RationalHeightLE (D.basis.repr
      (M.filtration.positivePolynomialEvaluation (M.positivePolynomialBasis p i)) k) ⌈Real.exp p⌉₊ := by
  change RationalHeightLE (D.basis.repr
    (M.filtration.positivePolynomialEvaluation
      (M.filtration.positivePolynomialBasis (M.positiveCoefficientBasis p) i)) k) _
  rw [M.filtration.positivePolynomialBasis_evaluation]
  exact M.positiveCoefficientBasis_height hM i.1 i.2 k

noncomputable def positivePolynomialFinBasis (p : ℝ) :
    Basis (Fin (Fintype.card M.PositivePolynomialBasisIndex)) ℚ M.filtration.positivePolynomialAlgebra :=
  (M.positivePolynomialBasis p).reindex (Fintype.equivFin M.PositivePolynomialBasisIndex)

theorem positivePolynomialFinBasis_structure_height {p : ℝ} (hM : M.ComplexityLE p) (i j k) :
    RationalHeightLE (lieStructureConstants (M.positivePolynomialFinBasis p) i j k)
      (squarefreeStructureHeight d ⌈Real.exp p⌉₊) := by
  rw [positivePolynomialFinBasis, lieStructureConstants_reindex]
  exact M.positivePolynomialBasis_structure_height hM _ _ _

theorem positivePolynomialFinBasis_evaluation_height {p : ℝ} (hM : M.ComplexityLE p) (i k) :
    RationalHeightLE (D.basis.repr
      (M.filtration.positivePolynomialEvaluation (M.positivePolynomialFinBasis p i)) k) ⌈Real.exp p⌉₊ := by
  rw [positivePolynomialFinBasis, Basis.reindex_apply]
  exact M.positivePolynomialBasis_evaluation_height hM _ _

theorem positivePolynomialFinBasis_multidegree_height (p : ℝ) (a : σ → ℕ) (j k) :
    RationalHeightLE ((M.positivePolynomialFinBasis p).repr
      (M.filtration.positivePolynomialMultidegreeBasis (M.positiveCoefficientBasis p) a j).val k) 1 := by
  rw [positivePolynomialFinBasis, Basis.repr_reindex_apply]
  exact M.filtration.positivePolynomialMultidegreeBasis_height (M.positiveCoefficientBasis p) a j _

theorem positivePolynomialFinBasis_degree_height (p : ℝ) (n : ℕ) (j k) :
    RationalHeightLE ((M.positivePolynomialFinBasis p).repr
      (M.filtration.positivePolynomialDegreeBasis (M.positiveCoefficientBasis p) n j).val k) 1 := by
  rw [positivePolynomialFinBasis, Basis.repr_reindex_apply]
  exact M.filtration.positivePolynomialDegreeBasis_height (M.positiveCoefficientBasis p) n j _

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module MultidegreeLieFiltration VectorPolynomial

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound) (J : Set (σ →₀ ℕ)) [DecidablePred (· ∈ J)]
  (hJ : IsLowerSet J)

abbrev PositivePolynomialDownsetIndex :=
  {j : M.PositivePolynomialBasisIndex // j ∉ {k | boxedDegreeMonomial k.1 ∉ J}}

noncomputable def positivePolynomialDownsetBasis (p : ℝ) :
    Basis (M.PositivePolynomialDownsetIndex J) ℚ
      (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra J hJ) :=
  M.filtration.positivePolynomialDownsetBasis (M.positiveCoefficientBasis p) J hJ

noncomputable def positivePolynomialDownsetFinBasis (p : ℝ) :
    Basis (Fin (Fintype.card (M.PositivePolynomialDownsetIndex J))) ℚ
      (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra J hJ) :=
  (M.positivePolynomialDownsetBasis J hJ p).reindex (Fintype.equivFin _)

theorem positivePolynomialDownsetIndex_card_le :
    Fintype.card (M.PositivePolynomialDownsetIndex J) ≤
      Fintype.card M.PositivePolynomialBasisIndex := Fintype.card_subtype_le _

omit [DecidableEq σ] [DecidablePred (· ∈ J)] in
theorem positivePolynomialDownsetBasis_structure (p : ℝ) (i j k) :
    lieStructureConstants (M.positivePolynomialDownsetBasis J hJ p) i j k =
      lieStructureConstants (M.positivePolynomialBasis p) i.val j.val k.val := by
  exact supportedQuotientBasis_lieStructure _ _ _
    (M.filtration.positivePolynomialDownsetIdeal_eq_span (M.positiveCoefficientBasis p) J hJ) i j k

theorem positivePolynomialDownsetFinBasis_multidegree_height (p : ℝ) (a : σ → ℕ) (j k) :
    RationalHeightLE ((M.positivePolynomialDownsetFinBasis J hJ p).repr
      (M.filtration.positivePolynomialDownsetMultidegreeBasis (M.positiveCoefficientBasis p) J hJ a j).val k) 1 := by
  rw [positivePolynomialDownsetFinBasis, Basis.repr_reindex_apply]
  exact M.filtration.positivePolynomialDownsetMultidegreeBasis_height
    (M.positiveCoefficientBasis p) J hJ a j _

theorem positivePolynomialDownsetFinBasis_degree_height (p : ℝ) (n : ℕ) (j k) :
    RationalHeightLE ((M.positivePolynomialDownsetFinBasis J hJ p).repr
      (M.filtration.positivePolynomialDownsetDegreeBasis (M.positiveCoefficientBasis p) J hJ n j).val k) 1 := by
  rw [positivePolynomialDownsetFinBasis, Basis.repr_reindex_apply]
  exact M.filtration.positivePolynomialDownsetDegreeBasis_height
    (M.positiveCoefficientBasis p) J hJ n j _

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module NilpotentLieBCHGroup
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

def PositivePolynomialGridStable (p : ℝ) (B : ℕ) : Prop :=
  ∀ x ∈ coordinateGridModule (M.positivePolynomialBasis p) B,
    ∀ y ∈ coordinateGridModule (M.positivePolynomialBasis p) B,
      lieBCH (∑ i, bound i) x y ∈ coordinateGridModule (M.positivePolynomialBasis p) B

noncomputable def positivePolynomialLattice (p : ℝ) (B : ℕ)
    (hstable : M.PositivePolynomialGridStable p B) :
    Subgroup M.filtration.positivePolynomialMultidegree.ordinary.Group :=
  coordinateGridBCHSubgroup (M.positivePolynomialBasis p) B
    M.filtration.positivePolynomialMultidegree.ordinary.lowerCentralSeries_eq_bot hstable

theorem positivePolynomialLattice_coordinates (p : ℝ) (B : ℕ)
    (hstable : M.PositivePolynomialGridStable p B) :
    bchSubgroupCoordinates (M.positivePolynomialBasis p) (M.positivePolynomialLattice p B hstable) =
      scaledIntegerGrid B := coordinateGridBCHSubgroup_coordinates _ _ _ hstable

noncomputable def positivePolynomialEvaluationDenominator (p : ℝ) : ℕ :=
  D.grid * matrixDenominator (LinearMap.toMatrix (M.positivePolynomialBasis p) D.basis
    M.filtration.positivePolynomialEvaluation.toLinearMap)

theorem positivePolynomialEvaluationDenominator_pos (p : ℝ) :
    0 < M.positivePolynomialEvaluationDenominator p :=
  Nat.mul_pos D.grid_pos (matrixDenominator_pos _)

theorem positivePolynomialLattice_maps (p : ℝ) (B : ℕ)
    (hstable : M.PositivePolynomialGridStable p B)
    (hdiv : M.positivePolynomialEvaluationDenominator p ∣ B) :
    M.positivePolynomialLattice p B hstable ≤
      D.lattice.comap (mapOfSteps M.filtration.positivePolynomialEvaluation) := by
  classical
  intro g hg
  apply (bchSubgroupCoordinates_repr (M.positivePolynomialBasis p)
    (D.lattice.comap (mapOfSteps M.filtration.positivePolynomialEvaluation)) g).mp
  rw [bchSubgroupCoordinates_comap_of_steps (M.positivePolynomialBasis p) D.basis]
  apply D.inner_grid
  apply matrix_mulVec_fine_grid
  apply scaledIntegerGrid_subset_of_dvd hdiv
  rw [← M.positivePolynomialLattice_coordinates p B hstable]
  exact (bchSubgroupCoordinates_repr (M.positivePolynomialBasis p)
    (M.positivePolynomialLattice p B hstable) g).mpr hg

theorem exists_positivePolynomial_stable_grid {p : ℝ} (hM : M.ComplexityLE p) :
    ∃ B : ℕ, 0 < B ∧ M.positivePolynomialEvaluationDenominator p ∣ B ∧
      B ≤ bchIntegralDenominatorBound (∑ i, bound i) *
        squarefreeStructureHeight d ⌈Real.exp p⌉₊ ^ (Fintype.card M.PositivePolynomialBasisIndex ^ 3) *
        M.positivePolynomialEvaluationDenominator p ∧ M.PositivePolynomialGridStable p B :=
  exists_bch_stable_integral_grid (M.positivePolynomialBasis p)
    M.filtration.positivePolynomialMultidegree.ordinary.lowerCentralSeries_eq_bot
    (M.positivePolynomialEvaluationDenominator p) (M.positivePolynomialEvaluationDenominator_pos p)
    (M.positivePolynomialBasis_structure_height hM)

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

noncomputable def positivePolynomialModel (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.PositivePolynomialGridStable p B) :
    RationalFilteredNilmanifold M.filtration.positivePolynomialAlgebra
      (∑ i, bound i) (Fintype.card M.PositivePolynomialBasisIndex) where
  filtration := M.filtration.positivePolynomialMultidegree.ordinary
  basis := M.positivePolynomialFinBasis p
  layerBasis i := M.filtration.positivePolynomialDegreeBasis (M.positiveCoefficientBasis p) (i.val + 1)
  lattice := M.positivePolynomialLattice p B hstable
  grid := B
  grid_pos := hB
  inner_grid := by
    apply bchSubgroup_inner_grid_reindex
    rw [M.positivePolynomialLattice_coordinates]
  outer_grid := by
    apply bchSubgroup_outer_grid_reindex
    rw [M.positivePolynomialLattice_coordinates]
    exact fun _ hx => scaledIntegerGrid_mem_denominatorGrid B B hx

noncomputable def positivePolynomialModelMultidegree (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.PositivePolynomialGridStable p B) :
    (M.positivePolynomialModel p B hB hstable).MultidegreeStructure bound where
  filtration := M.filtration.positivePolynomialMultidegree
  ordinary := rfl
  basis a := M.filtration.positivePolynomialMultidegreeBasis (M.positiveCoefficientBasis p)
    (fun i => (a i).val)

theorem positivePolynomialModel_complexity {p q : ℝ} (hM : M.ComplexityLE p)
    (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable p B)
    (hq : 0 ≤ q) (hd : (Fintype.card M.PositivePolynomialBasisIndex : ℝ) ≤ q)
    (hBq : (B : ℝ) ≤ Real.exp q)
    (hHq : (squarefreeStructureHeight d ⌈Real.exp p⌉₊ : ℝ) ≤ Real.exp q) :
    (M.positivePolynomialModelMultidegree p B hB hstable).ComplexityLE q := by
  have hone : ((1 : ℕ) : ℝ) ≤ Real.exp q := by
    rw [Nat.cast_one]
    exact Real.one_le_exp hq
  refine ⟨⟨hd, hBq, ?_, ?_⟩, ?_⟩
  · intro i j k
    exact rationalLogHeight_le_of_height (M.positivePolynomialFinBasis_structure_height hM i j k) hHq
  · intro i j k
    exact rationalLogHeight_le_of_height (M.positivePolynomialFinBasis_degree_height p (i.val + 1) j k) hone
  · intro a j k
    exact rationalLogHeight_le_of_height
      (M.positivePolynomialFinBasis_multidegree_height p (fun i => (a i).val) j k) hone

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open scoped BigOperators
open NilpotentLieBCHGroup

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem positivePolynomialEvaluationDenominator_le_exp {p : ℝ} (hM : M.ComplexityLE p) :
    (M.positivePolynomialEvaluationDenominator p : ℝ) ≤
      Real.exp (positivePolynomialDenominatorBudget (∑ i, bound i) p) := by
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  let t := ∑ i, bound i
  have hSQ := squarefreeInputBudget_le_positive t hp
  have hpQ : p ≤ positivePolynomialInputBudget t p :=
    (le_squarefreeInputBudget t hp).trans hSQ
  have hp1Q : p + 1 ≤ positivePolynomialInputBudget t p :=
    le_add_of_nonneg_right (squarefreeInputBudget_nonneg t hp)
  have hQ := positivePolynomialInputBudget_nonneg t hp
  have hNQ : (Fintype.card M.PositivePolynomialBasisIndex : ℝ) ≤
      positivePolynomialInputBudget t p := by
    apply le_trans _ hSQ
    calc
      _ ≤ (2 : ℝ) ^ t * d := by exact_mod_cast M.positivePolynomialBasisIndex_card_le p
      _ ≤ (2 : ℝ) ^ t * p := mul_le_mul_of_nonneg_left hM.1.1 (by positivity)
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  have hA : ∀ i j, RationalHeightLE
      (LinearMap.toMatrix (M.positivePolynomialBasis p) D.basis
        M.filtration.positivePolynomialEvaluation.toLinearMap i j) ⌈Real.exp p⌉₊ := by
    intro i j
    rw [LinearMap.toMatrix_apply]
    exact M.positivePolynomialBasis_evaluation_height hM j i
  have hden := matrixDenominator_allowance_le_exp _ D.grid ⌈Real.exp p⌉₊ hA hQ
    (by simpa only [Fintype.card_fin] using hM.1.1.trans hpQ) hNQ
    ((ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr hp1Q))
    (hM.1.2.1.trans (Real.exp_le_exp.mpr hpQ))
  exact hden.trans (Real.exp_le_exp.mpr (le_add_of_nonneg_left hQ))

theorem exists_controlled_positivePolynomial_model {p : ℝ} (hM : M.ComplexityLE p) :
    ∃ (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable p B),
      (M.positivePolynomialModelMultidegree p B hB hstable).ComplexityLE
        (positivePolynomialModelBudget (∑ i, bound i) p) ∧
      M.positivePolynomialLattice p B hstable ≤
        D.lattice.comap (mapOfSteps M.filtration.positivePolynomialEvaluation) := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  let t := ∑ i, bound i
  have hSR := (squarefreeInputBudget_le_positive t hp).trans
    (positivePolynomialInputBudget_le_denominator t p)
  have hR := (positivePolynomialInputBudget_nonneg t hp).trans
    (positivePolynomialInputBudget_le_denominator t p)
  have hRT := positivePolynomialDenominatorBudget_le_model t hp
  have hNR : (Fintype.card M.PositivePolynomialBasisIndex : ℝ) ≤
      positivePolynomialDenominatorBudget t p := by
    apply le_trans _ hSR
    calc
      _ ≤ (2 : ℝ) ^ t * d := by exact_mod_cast M.positivePolynomialBasisIndex_card_le p
      _ ≤ (2 : ℝ) ^ t * p := mul_le_mul_of_nonneg_left hM.1.1 (by positivity)
      _ ≤ _ := le_add_of_nonneg_right (by positivity)
  have hHR : (squarefreeStructureHeight d ⌈Real.exp p⌉₊ : ℝ) ≤
      Real.exp (positivePolynomialDenominatorBudget t p) :=
    (squarefreeStructureHeight_ceil_exp d hp hM.1.1).trans
      (Real.exp_le_exp.mpr ((le_add_of_nonneg_left (mul_nonneg (by positivity) hp)).trans hSR))
  obtain ⟨B, hB, hdiv, hraw, hstable⟩ := M.exists_positivePolynomial_stable_grid hM
  refine ⟨B, hB, hstable, ?_, M.positivePolynomialLattice_maps p B hstable hdiv⟩
  apply M.positivePolynomialModel_complexity hM B hB hstable (hR.trans hRT) (hNR.trans hRT)
  · apply (Nat.cast_le.mpr hraw).trans
    exact (integral_grid_allowance_le_exp (bchIntegralDenominatorBound t)
      (Fintype.card M.PositivePolynomialBasisIndex) _ _ hR hNR hHR
      (M.positivePolynomialEvaluationDenominator_le_exp hM)).trans
        (Real.exp_le_exp.mpr (le_add_of_nonneg_left hR))
  · exact hHR.trans (Real.exp_le_exp.mpr hRT)

theorem exists_positivePolynomial_model_uniform (t : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
      {bound : σ → ℕ} (M : D.MultidegreeStructure bound) {p : ℝ},
      (∑ i, bound i) = t → M.ComplexityLE p →
      ∃ (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable p B),
        (M.positivePolynomialModelMultidegree p B hB hstable).ComplexityLE ((p + C) ^ C) ∧
        M.positivePolynomialLattice p B hstable ≤
          D.lattice.comap (mapOfSteps M.filtration.positivePolynomialEvaluation) := by
  obtain ⟨C, hC, hbudget⟩ := exists_positivePolynomialModel_budget t
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ s d D bound M p ht hM
  obtain ⟨B, hB, hstable, hmodel, hmap⟩ := M.exists_controlled_positivePolynomial_model hM
  refine ⟨B, hB, hstable, hmodel.mono _ ?_, hmap⟩
  rw [ht]
  exact hbudget p ((Nat.cast_nonneg d).trans hM.1.1)

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module MultidegreeLieFiltration VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound) (J : Set (σ →₀ ℕ)) [DecidablePred (· ∈ J)]
  (hJ : IsLowerSet J)

noncomputable def positivePolynomialDownsetLattice (p : ℝ) (B : ℕ)
    (hstable : M.PositivePolynomialGridStable p B) :
    Subgroup (M.filtration.positivePolynomialDownsetQuotient J hJ).ordinary.Group :=
  (M.positivePolynomialLattice p B hstable).map
    (M.filtration.positivePolynomialMultidegree.ordinary.quotientStepHom
      (restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra J hJ)
      (by rw [M.filtration.positivePolynomialMultidegree.ordinary.terminal]; exact bot_le))

theorem positivePolynomialDownsetLattice_coordinates (p : ℝ) (B : ℕ)
    (hstable : M.PositivePolynomialGridStable p B) :
    bchSubgroupCoordinates (M.positivePolynomialDownsetBasis J hJ p)
      (M.positivePolynomialDownsetLattice J hJ p B hstable) = scaledIntegerGrid B := by
  exact M.filtration.positivePolynomialMultidegree.ordinary.quotientStep_exact_grid_supported
    (M.positivePolynomialBasis p)
    (restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra J hJ) _
    {j | boxedDegreeMonomial j.1 ∉ J}
    (M.filtration.positivePolynomialDownsetIdeal_eq_span (M.positiveCoefficientBasis p) J hJ)
    (M.positivePolynomialLattice p B hstable) B (M.positivePolynomialLattice_coordinates p B hstable)

noncomputable def positivePolynomialDownsetModel (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.PositivePolynomialGridStable p B) :
    RationalFilteredNilmanifold
      (M.filtration.positivePolynomialAlgebra ⧸
        restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra J hJ)
      (∑ i, bound i) (Fintype.card (M.PositivePolynomialDownsetIndex J)) where
  filtration := (M.filtration.positivePolynomialDownsetQuotient J hJ).ordinary
  basis := M.positivePolynomialDownsetFinBasis J hJ p
  layerBasis i := M.filtration.positivePolynomialDownsetDegreeBasis
    (M.positiveCoefficientBasis p) J hJ (i.val + 1)
  lattice := M.positivePolynomialDownsetLattice J hJ p B hstable
  grid := B
  grid_pos := hB
  inner_grid := by
    apply bchSubgroup_inner_grid_reindex
    rw [M.positivePolynomialDownsetLattice_coordinates]
  outer_grid := by
    apply bchSubgroup_outer_grid_reindex
    rw [M.positivePolynomialDownsetLattice_coordinates]
    exact fun _ hx => scaledIntegerGrid_mem_denominatorGrid B B hx

noncomputable def positivePolynomialDownsetModelMultidegree (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.PositivePolynomialGridStable p B) :
    (M.positivePolynomialDownsetModel J hJ p B hB hstable).MultidegreeStructure bound where
  filtration := M.filtration.positivePolynomialDownsetQuotient J hJ
  ordinary := rfl
  basis a := M.filtration.positivePolynomialDownsetMultidegreeBasis
    (M.positiveCoefficientBasis p) J hJ (fun i => (a i).val)

theorem positivePolynomialDownsetModel_complexity (p q : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.PositivePolynomialGridStable p B)
    (hE : (M.positivePolynomialModel p B hB hstable).GeometryComplexityLE q) :
    (M.positivePolynomialDownsetModelMultidegree J hJ p B hB hstable).ComplexityLE q := by
  have hq : 0 ≤ q := (Nat.cast_nonneg _).trans hE.1
  have hone : ((1 : ℕ) : ℝ) ≤ Real.exp q := by simpa only [Nat.cast_one] using Real.one_le_exp hq
  have hc (i j k : M.PositivePolynomialBasisIndex) :
      rationalLogHeight (lieStructureConstants (M.positivePolynomialBasis p) i j k) ≤ q := by
    have h := hE.2.2.1 ((Fintype.equivFin _) i) ((Fintype.equivFin _) j) ((Fintype.equivFin _) k)
    simpa only [positivePolynomialModel, positivePolynomialFinBasis, lieStructureConstants_reindex,
      Equiv.symm_apply_apply] using h
  refine ⟨⟨(Nat.cast_le.mpr (M.positivePolynomialDownsetIndex_card_le J)).trans hE.1,
    hE.2.1, ?_, ?_⟩, ?_⟩
  · intro i j k
    change rationalLogHeight (lieStructureConstants (M.positivePolynomialDownsetFinBasis J hJ p) i j k) ≤ q
    rw [positivePolynomialDownsetFinBasis, lieStructureConstants_reindex,
      M.positivePolynomialDownsetBasis_structure]
    exact hc _ _ _
  · intro i j k
    exact rationalLogHeight_le_of_height
      (M.positivePolynomialDownsetFinBasis_degree_height J hJ p (i.val + 1) j k) hone
  · intro a j k
    exact rationalLogHeight_le_of_height
      (M.positivePolynomialDownsetFinBasis_multidegree_height J hJ p (fun i => (a i).val) j k) hone

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem positivePolynomialEvaluation_metric_bound {p q : ℝ} (hM : M.ComplexityLE p)
    (hpq : p ≤ q) (hdim : (Fintype.card M.PositivePolynomialBasisIndex : ℝ) ≤ q) :
    (coordinateLipschitzBound d (Fintype.card M.PositivePolynomialBasisIndex) ⌈Real.exp p⌉₊ : ℝ) ≤
      Real.exp ((q + 3) ^ 2) := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  have hq : 0 ≤ q := hp.trans hpq
  have hH : (⌈Real.exp p⌉₊ : ℝ) ≤ Real.exp (q + 1) :=
    (ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr (by linarith))
  have h := coordinateLipschitzBound_le_exp d (Fintype.card M.PositivePolynomialBasisIndex)
    ⌈Real.exp p⌉₊ (p := q + 1) (by linarith) (by linarith [hM.1.1]) (by linarith) hH
  have heq : q + 1 + 2 = q + 3 := by ring
  simpa only [heq] using h

noncomputable def positivePolynomialEvaluationCosetMap (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.PositivePolynomialGridStable p B)
    (hmap : M.positivePolynomialLattice p B hstable ≤
      D.lattice.comap (mapOfSteps M.filtration.positivePolynomialEvaluation)) :
    (M.positivePolynomialModel p B hB hstable).Space → D.Space :=
  cosetMap _ _
    (realificationMap (hnil := M.filtration.positivePolynomialMultidegree.ordinary.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot) M.filtration.positivePolynomialEvaluation)
    (realificationMap_subgroup M.filtration.positivePolynomialEvaluation _ _ hmap)

theorem positivePolynomialEvaluationCosetMap_mk (p : ℝ) (B : ℕ) (hB : 0 < B)
    (hstable : M.PositivePolynomialGridStable p B)
    (hmap : M.positivePolynomialLattice p B hstable ≤
      D.lattice.comap (mapOfSteps M.filtration.positivePolynomialEvaluation)) (g) :
    M.positivePolynomialEvaluationCosetMap p B hB hstable hmap (QuotientGroup.mk g) =
      QuotientGroup.mk (realificationMap
        (hnil := M.filtration.positivePolynomialMultidegree.ordinary.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot) M.filtration.positivePolynomialEvaluation g) := rfl

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]
  [T2Space (ℝ ⊗[ℚ] M.filtration.positivePolynomialAlgebra)]

theorem positivePolynomialEvaluationCosetMap_lipschitz {p : ℝ} (hM : M.ComplexityLE p)
    (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable p B)
    (hmap : M.positivePolynomialLattice p B hstable ≤
      D.lattice.comap (mapOfSteps M.filtration.positivePolynomialEvaluation)) :
    letI := (M.positivePolynomialModel p B hB hstable).metricSpace
    letI := D.metricSpace
    LipschitzWith (coordinateLipschitzBound d (Fintype.card M.PositivePolynomialBasisIndex) ⌈Real.exp p⌉₊)
      (M.positivePolynomialEvaluationCosetMap p B hB hstable hmap) := by
  let := (M.positivePolynomialModel p B hB hstable).metricSpace
  let := D.metricSpace
  have h := lipschitz_realificationMap_quotient
    (M.positivePolynomialModel p B hB hstable).basis D.basis
    M.filtration.positivePolynomialEvaluation
    (M.positivePolynomialLattice p B hstable) D.lattice hmap B D.grid hB D.grid_pos
    (M.positivePolynomialModel p B hB hstable).outer_grid D.outer_grid ⌈Real.exp p⌉₊
    (fun k i => M.positivePolynomialFinBasis_evaluation_height hM i k)
  simp only [Fintype.card_fin] at h
  convert h using 1
  rfl

theorem exists_positivePolynomial_observable_pullback {p q : ℝ} (hM : M.ComplexityLE p)
    (hpq : p ≤ q) (hdim : (Fintype.card M.PositivePolynomialBasisIndex : ℝ) ≤ q)
    (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable p B)
    (hmap : M.positivePolynomialLattice p B hstable ≤
      D.lattice.comap (mapOfSteps M.filtration.positivePolynomialEvaluation))
    (u : D.Space → ℂ) (ℓ : ℝ≥0) (hℓ : (ℓ : ℝ) ≤ Real.exp q)
    (hu : letI := D.metricSpace; LipschitzWith ℓ u) :
    ∃ K : ℝ≥0, (K : ℝ) ≤ Real.exp (q + (q + 3) ^ 2) ∧
      (letI := (M.positivePolynomialModel p B hB hstable).metricSpace
       LipschitzWith K (u ∘ M.positivePolynomialEvaluationCosetMap p B hB hstable hmap)) := by
  let := D.metricSpace
  let := (M.positivePolynomialModel p B hB hstable).metricSpace
  let C := coordinateLipschitzBound d (Fintype.card M.PositivePolynomialBasisIndex) ⌈Real.exp p⌉₊
  refine ⟨ℓ * C, ?_, hu.comp (M.positivePolynomialEvaluationCosetMap_lipschitz hM B hB hstable hmap)⟩
  calc
    (ℓ * C : ℝ≥0) ≤ Real.exp q * Real.exp ((q + 3) ^ 2) :=
      mul_le_mul hℓ (M.positivePolynomialEvaluation_metric_bound hM hpq hdim)
        C.coe_nonneg (Real.exp_nonneg _)
    _ = _ := (Real.exp_add _ _).symm

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped BigOperators

theorem exists_positivePolynomial_downset_models_uniform (t : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] {s d : ℕ} {D : RationalFilteredNilmanifold L s d}
      {bound : σ → ℕ} (M : D.MultidegreeStructure bound) {p : ℝ},
      (∑ i, bound i) = t → M.ComplexityLE p →
      ∀ (J K : Set (σ →₀ ℕ)) [DecidablePred (· ∈ J)] [DecidablePred (· ∈ K)]
        (hJ : IsLowerSet J) (hK : IsLowerSet K),
      (∀ a, a ≠ 0 → a ∉ J ∪ K → M.filtration.layer (fun i => a i) = ⊥) →
      ∃ (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable p B),
        (M.positivePolynomialModelMultidegree p B hB hstable).ComplexityLE ((p + C) ^ C) ∧
        (M.positivePolynomialDownsetModelMultidegree J hJ p B hB hstable).ComplexityLE ((p + C) ^ C) ∧
        (M.positivePolynomialDownsetModelMultidegree K hK p B hB hstable).ComplexityLE ((p + C) ^ C) ∧
        M.positivePolynomialLattice p B hstable ≤
          D.lattice.comap (mapOfSteps M.filtration.positivePolynomialEvaluation) ∧
        Function.Injective (fun x =>
          (M.filtration.positivePolynomialDownsetCosetMap J hJ (M.positivePolynomialLattice p B hstable) x,
            M.filtration.positivePolynomialDownsetCosetMap K hK (M.positivePolynomialLattice p B hstable) x)) := by
  obtain ⟨C, hC, hmodels⟩ := exists_positivePolynomial_model_uniform t
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ s d D bound M p ht hM J K _ _ hJ hK hcover
  obtain ⟨B, hB, hstable, hmodel, heval⟩ := hmodels M ht hM
  refine ⟨B, hB, hstable, hmodel,
    M.positivePolynomialDownsetModel_complexity J hJ p _ B hB hstable hmodel.1,
    M.positivePolynomialDownsetModel_complexity K hK p _ B hB hstable hmodel.1, heval, ?_⟩
  exact M.filtration.positivePolynomial_downset_coset_pair_injective
    (M.positiveCoefficientBasis p) J K hJ hK hcover (M.positivePolynomialLattice p B hstable) B
    (M.positivePolynomialLattice_coordinates p B hstable)

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
