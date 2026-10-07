import OAI.Combinatorics.Progressions.Polynomial.AntisymmetricBoxPolynomial

namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

structure NativeAntisymmetricOrbitFactors {p : ℝ}
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (N : ℕ) (q : ℝ) where
  leftIndex : Fin W.outputDim
  rightIndex : Fin W.outputDim
  basis : Basis (Fin (finrank ℚ (Fin 8 → W.L))) ℚ (Fin 8 → W.L)
  weight : Fin (finrank ℚ (Fin 8 → W.L)) → ℕ
  adapted : ∀ k, (pi (fun _ : Fin 8 => W.model)).filtration.layer k =
    Submodule.span ℚ (basis '' {i | k ≤ weight i})
  basis_height : ∀ i j,
    rationalLogHeight ((pi (fun _ : Fin 8 => W.model)).basis.repr (basis i) j) ≤ q
  subalgebra : LieSubalgebra ℚ (pi (fun _ : Fin 8 => W.model)).filtration.AssociatedGraded
  generator : Fin (finrank ℚ (Fin 8 → W.L)) →
    (pi (fun _ : Fin 8 => W.model)).filtration.AssociatedGraded
  spanning : Submodule.span ℚ (Set.range generator) = subalgebra.toSubmodule
  graded : BasisGradedSubmodule
    ((pi (fun _ : Fin 8 => W.model)).filtration.associatedGradedBasis basis weight adapted)
    weight subalgebra.toSubmodule
  generator_height : ∀ i j, rationalLogHeight
    (((pi (fun _ : Fin 8 => W.model)).filtration.associatedGradedBasis basis weight adapted).repr
      (generator i) j) ≤ q
  kills_top : ∀ z ∈ (pi (fun _ : Fin 8 => W.model)).filtration.realGradedRefiltrationLayer
      subalgebra (∑ k, mixedCorrelationDegree 1 k),
    realifyFunctional (piFrequency W.antisymmetricBoxFrequencies) z = 0
  denominator : ℕ
  denominator_pos : 0 < denominator
  denominator_bound : (denominator : ℝ) ≤ Real.exp q
  latticeConstant : (pi (fun _ : Fin 8 => W.model)).RealGroup
  latticeConstant_mem : latticeConstant ∈ (pi (fun _ : Fin 8 => W.model)).realLattice
  slow :
    ((pi (fun _ : Fin 8 => W.model)).filtration.realification.adaptedPolynomialFiltration
      (fun _ : Fin 4 => 1)).Group
  middle :
    ((pi (fun _ : Fin 8 => W.model)).filtration.realification.adaptedPolynomialFiltration
      (fun _ : Fin 4 => 1)).Group
  rational :
    ((pi (fun _ : Fin 8 => W.model)).filtration.realification.adaptedPolynomialFiltration
      (fun _ : Fin 4 => 1)).Group
  product : slow * middle * rational *
    (pi (fun _ : Fin 8 => W.model)).filtration.realification.adaptedConstantGroupHom
      (fun _ : Fin 4 => 1) latticeConstant = W.antisymmetricBoxPolynomial leftIndex rightIndex
  slow_bound : ∀ α i, |(basis.baseChange ℝ).repr
    (coefficients (slow.coord : VectorPolynomial (Fin 4) ℚ (ℝ ⊗[ℚ] (Fin 8 → W.L))) α) i| ≤
      Real.exp q / monomialScale (fun _ : Fin 4 => (N : ℝ)) α
  rational_grid : (fun z : ((Fin 4) →₀ ℕ) × Fin (finrank ℚ (Fin 8 → W.L)) =>
    (basis.baseChange ℝ).repr
      (coefficients (rational.coord : VectorPolynomial (Fin 4) ℚ (ℝ ⊗[ℚ] (Fin 8 → W.L))) z.1) z.2) ∈
        realDenominatorGrid denominator
  middle_zero : coefficients
    (middle.coord : VectorPolynomial (Fin 4) ℚ (ℝ ⊗[ℚ] (Fin 8 → W.L))) 0 = 0
  rational_zero : coefficients
    (rational.coord : VectorPolynomial (Fin 4) ℚ (ℝ ⊗[ℚ] (Fin 8 → W.L))) 0 = 0
  middle_coefficients : ∀ α, coefficients
    (middle.coord : VectorPolynomial (Fin 4) ℚ (ℝ ⊗[ℚ] (Fin 8 → W.L))) α ∈
      (pi (fun _ : Fin 8 => W.model)).filtration.realGradedRefiltrationLayer subalgebra
        (Finsupp.weight (fun _ => 1) α)

namespace NativeAntisymmetricOrbitFactors

variable {p q : ℝ} {N : ℕ}
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
  (V : NativeAntisymmetricOrbitFactors W N q)

theorem middle_values (t : Fin 4 → ℝ) :
    eval₂ t (V.middle.coord : VectorPolynomial (Fin 4) ℚ (ℝ ⊗[ℚ] (Fin 8 → W.L))) ∈
      realificationLieSubalgebra
        ((pi (fun _ : Fin 8 => W.model)).filtration.gradedRefiltrationSubalgebra V.subalgebra) := by
  apply (eval₂_mem_iff_coefficients
    (realificationLieSubalgebra
      ((pi (fun _ : Fin 8 => W.model)).filtration.gradedRefiltrationSubalgebra V.subalgebra)).toSubmodule
    (V.middle.coord : VectorPolynomial (Fin 4) ℚ (ℝ ⊗[ℚ] (Fin 8 → W.L)))).mpr
  exact (pi (fun _ : Fin 8 => W.model)).filtration.normalized_refiltration_coefficients_mem_first
    (fun _ : Fin 4 => 1) V.subalgebra (fun _ => Nat.zero_lt_one) V.middle.coord
    V.middle_coefficients V.middle_zero

theorem middle_top_frequency (α : (Fin 4) →₀ ℕ)
    (hα : Finsupp.weight (fun _ => 1) α = ∑ k, mixedCorrelationDegree 1 k) :
    realifyFunctional (piFrequency W.antisymmetricBoxFrequencies)
      (coefficients (V.middle.coord : VectorPolynomial (Fin 4) ℚ (ℝ ⊗[ℚ] (Fin 8 → W.L))) α) = 0 := by
  apply V.kills_top
  simpa only [hα] using V.middle_coefficients α

theorem middle_bracket_frequency (α β : (Fin 4) →₀ ℕ)
    (hαβ : Finsupp.weight (fun _ => 1) α + Finsupp.weight (fun _ => 1) β =
      ∑ k, mixedCorrelationDegree 1 k) :
    realifyFunctional (piFrequency W.antisymmetricBoxFrequencies)
      ⁅coefficients (V.middle.coord : VectorPolynomial (Fin 4) ℚ (ℝ ⊗[ℚ] (Fin 8 → W.L))) α,
        coefficients (V.middle.coord : VectorPolynomial (Fin 4) ℚ (ℝ ⊗[ℚ] (Fin 8 → W.L))) β⁆ = 0 := by
  apply V.kills_top
  simpa only [hαβ] using
    (pi (fun _ : Fin 8 => W.model)).filtration.realGradedRefiltrationLayer_lie_mem V.subalgebra
      (V.middle_coefficients α) (V.middle_coefficients β)

end NativeAntisymmetricOrbitFactors

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra

theorem exists_antisymmetric_coefficient_control :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
      {N : ℕ} [NeZero N] (V : NativeAntisymmetricOrbitFactors W N p), 0 ≤ p →
      let D := pi (fun _ : Fin 8 => W.model)
      D.GeometryComplexityLE ((p + C) ^ C) ∧
        ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          D.filtration.PolynomialRationalGrid D.basis (fun _ : Fin 4 => 1) m V.rational ∧
          D.filtration.PolynomialSlowBound D.basis (fun _ : Fin 4 => 1)
            (fun _ => (N : ℝ)) (Real.exp ((p + C) ^ C)) V.slow := by
  let X : Polynomial ℕ := Polynomial.X
  let R := (X + 10) ^ 2 + X + 10
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((R + 2) ^ 3 + R + (R + 3) ^ 2)
  refine ⟨C, hC, ?_⟩
  intro p W N _ V hp
  let D := pi (fun _ : Fin 8 => W.model)
  let r := (p + 10) ^ 2 + p + 10
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hpr : p ≤ r := by dsimp [r]; nlinarith [sq_nonneg (p + 10)]
  have hD : D.GeometryComplexityLE r := by
    have h := pi_geometry (fun _ : Fin 8 => W.model) (by linarith : 0 ≤ p + 8)
      (by norm_num; linarith)
      (fun _ => W.complexity.1.mono W.model (by linarith : p ≤ p + 8))
    exact h.mono D (by dsimp [r]; nlinarith)
  have hdim : (Fintype.card (Fin (finrank ℚ (Fin 8 → W.L))) : ℝ) ≤ r := by
    rw [Fintype.card_fin, finrank_eq_card_basis D.basis, Fintype.card_fin]
    exact hD.1
  have hdimD : (Fintype.card (Fin (Fintype.card ((_ : Fin 8) × Fin W.dim))) : ℝ) ≤ r := by
    simpa only [Fintype.card_fin] using hD.1
  let m := matrixDenominator (fun i j => D.basis.repr (V.basis j) i) * V.denominator
  have hmb : (m : ℝ) ≤ Real.exp ((r + 2) ^ 3 + r) :=
    NilpotentLieFiltration.original_coordinate_denominator_bound V.basis D.basis hr hdim hdimD
      (fun i j => (V.basis_height i j).trans hpr) V.denominator
      (V.denominator_bound.trans (Real.exp_le_exp.mpr hpr))
  have hsum : (r + 2) ^ 3 + r + (r + 3) ^ 2 ≤ (p + C) ^ C := by
    simpa [R, X, r, Polynomial.eval₂_pow] using hbudget p hp
  have hdenC : (r + 2) ^ 3 + r ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (sq_nonneg _)).trans hsum
  have hrC : r ≤ (p + C) ^ C := (le_add_of_nonneg_left (by positivity)).trans hdenC
  have hslowC : (r + 3) ^ 2 ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (by positivity)).trans hsum
  have hN : ∀ _i : Fin 4, (0 : ℝ) < N := fun _ => Nat.cast_pos.mpr (NeZero.pos N)
  have hs := D.filtration.polynomialSlowBound_change_basis_exp V.basis D.basis
    (fun _ : Fin 4 => 1) (fun _ => (N : ℝ)) hN hr hdim
    (fun i j => (V.basis_height i j).trans hpr) V.slow
    (D.filtration.polynomialSlowBound_mono V.basis (fun _ => 1) (fun _ => (N : ℝ)) hN
      (Real.exp_le_exp.mpr hpr) V.slow V.slow_bound)
  refine ⟨hD.mono D hrC, m, Nat.mul_pos (matrixDenominator_pos _) V.denominator_pos,
    hmb.trans (Real.exp_le_exp.mpr hdenC), ?_, ?_⟩
  · exact D.filtration.polynomialRationalGrid_change_basis V.basis D.basis
      (fun _ : Fin 4 => 1) V.denominator V.rational V.rational_grid
  · exact D.filtration.polynomialSlowBound_mono D.basis (fun _ : Fin 4 => 1)
      (fun _ => (N : ℝ)) hN (Real.exp_le_exp.mpr hslowC) V.slow hs

end Erdos3

end

section

namespace Erdos3.NativeAntisymmetricOrbitFactors

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

variable {p q : ℝ} {N : ℕ}
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
  (V : NativeAntisymmetricOrbitFactors W N q)
  [TopologicalSpace (ℝ ⊗[ℚ] (Fin 8 → W.L))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 8 → W.L))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fin 8 → W.L))] [T2Space (ℝ ⊗[ℚ] (Fin 8 → W.L))]

theorem eval_factors (hp : 0 ≤ p) (n : Fin 4 → ℤ) :
    W.antisymmetricBoxValue V.leftIndex V.rightIndex n =
      (W.antisymmetricBoxNiltest hp V.leftIndex V.rightIndex).observable (QuotientGroup.mk
        ((pi (fun _ : Fin 8 => W.model)).filtration.adaptedPolynomialRealValueHom
            (fun _ : Fin 4 => 1) (fun i => (n i : ℝ)) V.slow *
          (pi (fun _ : Fin 8 => W.model)).filtration.adaptedPolynomialRealValueHom
            (fun _ : Fin 4 => 1) (fun i => (n i : ℝ)) V.middle *
          (pi (fun _ : Fin 8 => W.model)).filtration.adaptedPolynomialRealValueHom
            (fun _ : Fin 4 => 1) (fun i => (n i : ℝ)) V.rational)) := by
  rw [← W.antisymmetricBoxNiltest_eval hp]
  exact Niltest.eval_of_lattice_factorization (pi (fun _ : Fin 8 => W.model)) (fun _ : Fin 4 => 1)
    (W.antisymmetricBoxNiltest hp V.leftIndex V.rightIndex) V.slow V.middle V.rational
    V.latticeConstant V.latticeConstant_mem
    (V.product.trans (W.antisymmetricBoxPolynomial_eq_test hp V.leftIndex V.rightIndex)) n

theorem top_layer_invariant (hp : 0 ≤ p)
    (z : (pi (fun _ : Fin 8 => W.model)).RealGroup)
    (hz : z.coord ∈ (pi (fun _ : Fin 8 => W.model)).filtration.realGradedRefiltrationLayer
      V.subalgebra (∑ k, mixedCorrelationDegree 1 k))
    (x : (pi (fun _ : Fin 8 => W.model)).Space) :
    (W.antisymmetricBoxNiltest hp V.leftIndex V.rightIndex).observable (z • x) =
      (W.antisymmetricBoxNiltest hp V.leftIndex V.rightIndex).observable x := by
  have htop : z ∈ (pi (fun _ : Fin 8 => W.model)).filtration.realification.subgroup
      (∑ k, mixedCorrelationDegree 1 k) :=
    (pi (fun _ : Fin 8 => W.model)).filtration.realGradedRefiltrationLayer_le V.subalgebra _ hz
  rw [W.antisymmetricBoxNiltest_vertical hp V.leftIndex V.rightIndex z htop,
    V.kills_top z.coord hz]
  simp only [AddCircle.coe_zero, CircleFourier.character_zero, one_mul]

end Erdos3.NativeAntisymmetricOrbitFactors

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

noncomputable def NativeAntisymmetricOrbitFactors.mono {p p' q q' : ℝ} {N : ℕ} [NeZero N]
    {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
    (V : NativeAntisymmetricOrbitFactors W N q) (hp : p ≤ p') (hq : q ≤ q') :
    NativeAntisymmetricOrbitFactors (W.mono hp) N q' := by
  have hproduct := V.product.trans
    (W.antisymmetricBoxPolynomial_mono hp V.leftIndex V.rightIndex).symm
  exact {
    leftIndex := V.leftIndex
    rightIndex := V.rightIndex
    basis := V.basis
    weight := V.weight
    adapted := V.adapted
    basis_height := fun i j => (V.basis_height i j).trans hq
    subalgebra := V.subalgebra
    generator := V.generator
    spanning := V.spanning
    graded := V.graded
    generator_height := fun i j => (V.generator_height i j).trans hq
    kills_top := V.kills_top
    denominator := V.denominator
    denominator_pos := V.denominator_pos
    denominator_bound := V.denominator_bound.trans (Real.exp_le_exp.mpr hq)
    latticeConstant := V.latticeConstant
    latticeConstant_mem := V.latticeConstant_mem
    slow := V.slow
    middle := V.middle
    rational := V.rational
    product := hproduct
    slow_bound := fun α i => (V.slow_bound α i).trans (div_le_div_of_nonneg_right
      (Real.exp_le_exp.mpr hq)
      (monomialScale_pos (fun _ : Fin 4 => (N : ℝ))
        (fun _ => by exact_mod_cast NeZero.pos N) α).le)
    rational_grid := V.rational_grid
    middle_zero := V.middle_zero
    rational_zero := V.rational_zero
    middle_coefficients := V.middle_coefficients }

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra

theorem exists_antisymmetric_outer_bounds :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
      {N : ℕ} [NeZero N] (V : NativeAntisymmetricOrbitFactors W N p), 0 ≤ p →
      let D := pi (fun _ : Fin 8 => W.model)
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        (∀ x : Fin 4 → ℤ, (D.basis.baseChange ℝ).equivFun
          (D.filtration.adaptedPolynomialRealValueHom (fun _ : Fin 4 => 1)
            (fun i => (x i : ℝ)) V.rational).coord ∈ realDenominatorGrid m) ∧
        ∀ x : Fin 4 → ℤ, (∀ i, |(x i : ℝ)| ≤ (N : ℝ)) → ∀ i,
          |(D.basis.baseChange ℝ).repr
            (D.filtration.adaptedPolynomialRealValueHom (fun _ : Fin 4 => 1)
              (fun j => (x j : ℝ)) V.slow).coord i| ≤ Real.exp ((p + C) ^ C) := by
  let X : Polynomial ℕ := Polynomial.X
  let R := (X + 10) ^ 2 + X + 10
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((R + 2) ^ 3 + R + (R + 82) ^ 2)
  refine ⟨C, hC, ?_⟩
  intro p W N _ V hp
  let D := pi (fun _ : Fin 8 => W.model)
  let r := (p + 10) ^ 2 + p + 10
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hpr : p ≤ r := by dsimp [r]; nlinarith [sq_nonneg (p + 10)]
  have hD : D.GeometryComplexityLE r := by
    have h := pi_geometry (fun _ : Fin 8 => W.model) (by linarith : 0 ≤ p + 8)
      (by norm_num; linarith)
      (fun _ => W.complexity.1.mono W.model (by linarith : p ≤ p + 8))
    exact h.mono D (by dsimp [r]; nlinarith)
  have hdim : (Fintype.card (Fin (finrank ℚ (Fin 8 → W.L))) : ℝ) ≤ r := by
    rw [Fintype.card_fin, finrank_eq_card_basis D.basis, Fintype.card_fin]
    exact hD.1
  have hdimD : (Fintype.card (Fin (Fintype.card ((_ : Fin 8) × Fin W.dim))) : ℝ) ≤ r := by
    simpa only [Fintype.card_fin] using hD.1
  let m := matrixDenominator (fun i j => D.basis.repr (V.basis j) i) * V.denominator
  have hm : 0 < m := Nat.mul_pos (matrixDenominator_pos _) V.denominator_pos
  have hmb : (m : ℝ) ≤ Real.exp ((r + 2) ^ 3 + r) :=
    NilpotentLieFiltration.original_coordinate_denominator_bound V.basis D.basis hr hdim hdimD
      (fun i j => (V.basis_height i j).trans hpr) V.denominator
      (V.denominator_bound.trans (Real.exp_le_exp.mpr hpr))
  have hsum : (r + 2) ^ 3 + r + (r + 82) ^ 2 ≤ (p + C) ^ C := by
    simpa [R, X, r, Polynomial.eval₂_pow] using hbudget p hp
  have hdenC : (r + 2) ^ 3 + r ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (sq_nonneg _)).trans hsum
  have hslowC : (r + 82) ^ 2 ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (by positivity)).trans hsum
  refine ⟨m, hm, hmb.trans (Real.exp_le_exp.mpr hdenC), ?_, ?_⟩
  · intro x
    exact real_basis_coordinates_grid V.basis D.basis V.denominator _
      (D.filtration.polynomialRationalGrid_value V.basis (fun _ : Fin 4 => 1)
        V.denominator V.rational V.rational_grid x)
  · intro x hx i
    have hs (j) : |(V.basis.baseChange ℝ).repr
        (D.filtration.adaptedPolynomialRealValueHom (fun _ : Fin 4 => 1)
          (fun k => (x k : ℝ)) V.slow).coord j| ≤ 75 * Real.exp p := by
      have h := D.filtration.polynomialSlowBound_value V.basis (fun _ : Fin 4 => 1)
        (fun _ => Nat.zero_lt_one) (fun _ => (N : ℝ))
        (fun _ => by exact_mod_cast NeZero.pos N) (Real.exp_nonneg p)
        V.slow V.slow_bound (fun k => (x k : ℝ)) hx j
      convert h using 1
      norm_num [show (∑ k, mixedCorrelationDegree 1 k) = 2 by decide]
    have h75 : (75 : ℝ) ≤ Real.exp 75 := by linarith [Real.add_one_le_exp (75 : ℝ)]
    have hs' (j) : |(V.basis.baseChange ℝ).repr
        (D.filtration.adaptedPolynomialRealValueHom (fun _ : Fin 4 => 1)
          (fun k => (x k : ℝ)) V.slow).coord j| ≤ Real.exp (r + 80) := by
      apply (hs j).trans
      calc
        _ ≤ Real.exp 75 * Real.exp p := mul_le_mul_of_nonneg_right h75 (Real.exp_nonneg p)
        _ = Real.exp (75 + p) := (Real.exp_add _ _).symm
        _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
    have hH : (⌈Real.exp p⌉₊ : ℝ) ≤ Real.exp (r + 80) :=
      (ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr (by linarith))
    have hbound := real_basis_coordinates_exp_bound V.basis D.basis
      (by linarith : 0 ≤ r + 80) (hdim.trans (by linarith)) hH
      (fun i j => rationalHeightLE_ceil_exp (V.basis_height j i)) _ hs' i
    apply hbound.trans
    apply Real.exp_le_exp.mpr
    simpa only [show r + 80 + 2 = r + 82 by ring] using hslowC

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra

theorem exists_antisymmetric_local_control :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
      {N : ℕ} [NeZero N] (V : NativeAntisymmetricOrbitFactors W N p)
      [TopologicalSpace (ℝ ⊗[ℚ] (Fin 8 → W.L))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 8 → W.L))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fin 8 → W.L))] [T2Space (ℝ ⊗[ℚ] (Fin 8 → W.L))],
      0 ≤ p →
      let D := pi (fun _ : Fin 8 => W.model)
      let a := fun x : Fin 4 → ℤ => D.filtration.adaptedPolynomialRealValueHom
        (fun _ : Fin 4 => 1) (fun i => (x i : ℝ)) V.slow
      let r := fun x : Fin 4 → ℤ => D.filtration.adaptedPolynomialRealValueHom
        (fun _ : Fin 4 => 1) (fun i => (x i : ℝ)) V.rational
      ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        (∀ x y : Fin 4 → ℤ, (∀ i, (P : ℤ) ∣ x i - y i) →
          ((QuotientGroup.mk (r x) : D.Space) = QuotientGroup.mk (r y)) ∧
          ((QuotientGroup.mk (r x)⁻¹ : D.Space) = QuotientGroup.mk (r y)⁻¹)) ∧
        (letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
          (D.basis.baseChange ℝ)
         ∀ (x y : Fin 4 → ℤ) (δ : ℝ), 0 ≤ δ →
           (∀ i, |(x i : ℝ)| ≤ (N : ℝ)) → (∀ i, |(y i : ℝ)| ≤ (N : ℝ)) →
           (∀ i, |(x i : ℝ) - (y i : ℝ)| ≤ (N : ℝ) * δ) →
           dist (a x) (a y) ≤ Real.exp ((p + C) ^ C) * δ) := by
  obtain ⟨A, _, hcoeff⟩ := exists_antisymmetric_coefficient_control
  obtain ⟨B, _, hperiod⟩ := exists_native_rational_period 2
  obtain ⟨K, _, hmetric⟩ := exists_polynomialSlowBound_dist_exp 2 1
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C A) ^ A + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Q + Polynomial.C B) ^ B + (Q + Polynomial.C K) ^ K)
  refine ⟨C, hC, ?_⟩
  intro p W N _ V _ _ _ _ hp
  let D := pi (fun _ : Fin 8 => W.model)
  obtain ⟨hD, m, hm, hmb, hgrid, hslow⟩ := hcoeff W V hp
  let q := (p + A) ^ A + 4
  have hq0 : 0 ≤ (p + A) ^ A := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hAq : (p + A) ^ A ≤ q := by dsimp [q]; linarith
  have h4q : (Fintype.card (Fin 4) : ℝ) ≤ q := by norm_num; dsimp [q]; linarith
  have hsum : (q + B) ^ B + (q + K) ^ K ≤ (p + C) ^ C := by
    simpa [Q, X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hBC : (q + B) ^ B ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hsum
  have hKC : (q + K) ^ K ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (by positivity)).trans hsum
  obtain ⟨P, hP, hPb, hcosets⟩ := hperiod D (fun _ : Fin 4 => 1) (fun _ => Nat.zero_lt_one)
    q hq (hD.mono D hAq) h4q m hm (hmb.trans (Real.exp_le_exp.mpr hAq))
  refine ⟨P, hP, hPb.trans (Real.exp_le_exp.mpr hBC), ?_, ?_⟩
  · exact hcosets V.rational hgrid
  · let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
      (D.basis.baseChange ℝ)
    intro x y δ hδ hx hy hxy
    have hN : ∀ _i : Fin 4, (0 : ℝ) < N := fun _ => Nat.cast_pos.mpr (NeZero.pos N)
    have hs := D.filtration.polynomialSlowBound_mono D.basis (fun _ : Fin 4 => 1)
      (fun _ => (N : ℝ)) hN
      (Real.exp_le_exp.mpr (by simp only [pow_one]; linarith : (p + A) ^ A ≤ (q + 2) ^ 1))
      V.slow hslow
    have hd := hmetric D (fun _ : Fin 4 => 1) (fun _ => Nat.zero_lt_one)
      q hq (hD.mono D hAq) h4q (fun _ => (N : ℝ)) hN V.slow hs
      (fun i => (x i : ℝ)) (fun i => (y i : ℝ)) δ hδ hx hy hxy
    exact hd.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hKC) hδ)

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

structure NativeAntisymmetricFrozenDescent {p : ℝ}
    {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {N : ℕ}
    (V : NativeAntisymmetricOrbitFactors W N p) (q : ℝ) where
  nonnegative : 0 ≤ p
  [productTopology : TopologicalSpace (ℝ ⊗[ℚ] (Fin 8 → W.L))]
  [productTopologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 8 → W.L))]
  [productContinuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fin 8 → W.L))]
  [productHausdorff : T2Space (ℝ ⊗[ℚ] (Fin 8 → W.L))]
  outerBudget : ℝ
  outer_nonnegative : 0 ≤ outerBudget
  outer_bound : outerBudget ≤ q
  denominator : ℕ
  denominator_pos : 0 < denominator
  denominator_bound : (denominator : ℝ) ≤ Real.exp outerBudget
  rational_values : ∀ x : Fin 4 → ℤ,
    ((pi (fun _ : Fin 8 => W.model)).basis.baseChange ℝ).equivFun
      ((pi (fun _ : Fin 8 => W.model)).filtration.adaptedPolynomialRealValueHom
        (fun _ : Fin 4 => 1) (fun i => (x i : ℝ)) V.rational).coord ∈
      realDenominatorGrid denominator
  slow_values : ∀ x : Fin 4 → ℤ, (∀ i, |(x i : ℝ)| ≤ (N : ℝ)) → ∀ i,
    |((pi (fun _ : Fin 8 => W.model)).basis.baseChange ℝ).repr
      ((pi (fun _ : Fin 8 => W.model)).filtration.adaptedPolynomialRealValueHom
        (fun _ : Fin 4 => 1) (fun j => (x j : ℝ)) V.slow).coord i| ≤ Real.exp outerBudget
  L : Type
  [lie : LieRing L]
  [algebra : LieAlgebra ℚ L]
  dim : ℕ
  [topology : TopologicalSpace (ℝ ⊗[ℚ] L)]
  [topologicalAdd : IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [continuousSMul : ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
  [hausdorff : T2Space (ℝ ⊗[ℚ] L)]
  model : RationalFilteredNilmanifold L 1 dim
  model_complexity : model.GeometryComplexityLE q
  orbit : model.filtration.realification.PolynomialOrbit (fun _ : Fin 4 => 1)
  descend : ∀ a r : (pi (fun _ : Fin 8 => W.model)).RealGroup,
    (∀ i, |((pi (fun _ : Fin 8 => W.model)).basis.baseChange ℝ).repr a.coord i| ≤
      Real.exp outerBudget) →
    ((pi (fun _ : Fin 8 => W.model)).basis.baseChange ℝ).equivFun r.coord ∈
      realDenominatorGrid denominator →
    ∃ S : model.Niltest (fun _ : Fin 4 => 1), S.orbit = orbit ∧
      S.normBound = (W.antisymmetricBoxNiltest nonnegative V.leftIndex V.rightIndex).normBound ∧
      S.ComplexityLE q ∧ ∀ x : Fin 4 → ℤ,
        S.eval x = (W.antisymmetricBoxNiltest nonnegative V.leftIndex V.rightIndex).observable
          (QuotientGroup.mk (a *
            (pi (fun _ : Fin 8 => W.model)).filtration.adaptedPolynomialRealValueHom
              (fun _ : Fin 4 => 1) (fun i => (x i : ℝ)) V.middle * r))

attribute [local instance] NativeAntisymmetricFrozenDescent.lie NativeAntisymmetricFrozenDescent.algebra
  NativeAntisymmetricFrozenDescent.topology NativeAntisymmetricFrozenDescent.topologicalAdd
  NativeAntisymmetricFrozenDescent.continuousSMul NativeAntisymmetricFrozenDescent.hausdorff

noncomputable def NativeAntisymmetricFrozenDescent.mono {p q q' : ℝ}
    {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {N : ℕ}
    {V : NativeAntisymmetricOrbitFactors W N p} (R : NativeAntisymmetricFrozenDescent V q)
    (hqq' : q ≤ q') : NativeAntisymmetricFrozenDescent V q' :=
  { R with
    outer_bound := R.outer_bound.trans hqq'
    model_complexity := R.model_complexity.mono R.model hqq'
    descend := by
      intro a r ha hr
      obtain ⟨S, hSo, hSn, hSc, hSe⟩ := R.descend a r ha hr
      exact ⟨S, hSo, hSn, hSc.mono hqq', hSe⟩ }

theorem NativeAntisymmetricFrozenDescent.exists_diagonal_niltest {p q : ℝ}
    {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {N : ℕ}
    {V : NativeAntisymmetricOrbitFactors W N p} (R : NativeAntisymmetricFrozenDescent V q)
    (x : Fin 4 → ℤ) (hx : ∀ i, |(x i : ℝ)| ≤ (N : ℝ)) :
    ∃ S : R.model.Niltest (fun _ : Fin 4 => 1), S.orbit = R.orbit ∧
      S.ComplexityLE q ∧ S.eval x = W.antisymmetricBoxValue V.leftIndex V.rightIndex x := by
  let := R.productTopology
  let := R.productTopologicalAdd
  let := R.productContinuousSMul
  let := R.productHausdorff
  obtain ⟨S, hSo, _, hSc, hSe⟩ := R.descend _ _ (R.slow_values x hx) (R.rational_values x)
  exact ⟨S, hSo, hSc, (hSe x).trans (V.eval_factors R.nonnegative x).symm⟩

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct

theorem RationalFilteredNilmanifold.observable_frozen_right_eq
    {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d) (u : D.Space → ℂ)
    (a b r r' : D.RealGroup)
    (h : (QuotientGroup.mk r : D.Space) = QuotientGroup.mk r') :
    u (QuotientGroup.mk (a * b * r)) = u (QuotientGroup.mk (a * b * r')) :=
  congrArg (fun x : D.Space => u ((a * b) • x)) h

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeAntisymmetricFrozenDescent.lie NativeAntisymmetricFrozenDescent.algebra
  NativeAntisymmetricFrozenDescent.topology NativeAntisymmetricFrozenDescent.topologicalAdd
  NativeAntisymmetricFrozenDescent.continuousSMul NativeAntisymmetricFrozenDescent.hausdorff

structure NativeAntisymmetricLocalModels {p q : ℝ}
    {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {N : ℕ}
    {V : NativeAntisymmetricOrbitFactors W N p} (R : NativeAntisymmetricFrozenDescent V q)
    (b : ℝ) where
  period : ℕ
  period_pos : 0 < period
  period_bound : (period : ℝ) ≤ Real.exp b
  local_model : ∀ y : Fin 4 → ℤ, (∀ i, |(y i : ℝ)| ≤ (N : ℝ)) →
    ∃ S : R.model.Niltest (fun _ : Fin 4 => 1), S.orbit = R.orbit ∧ S.ComplexityLE q ∧
      ∀ (x : Fin 4 → ℤ) (δ : ℝ), 0 ≤ δ →
        (∀ i, |(x i : ℝ)| ≤ (N : ℝ)) → (∀ i, (period : ℤ) ∣ x i - y i) →
        (∀ i, |(x i : ℝ) - (y i : ℝ)| ≤ (N : ℝ) * δ) →
        ‖W.antisymmetricBoxValue V.leftIndex V.rightIndex x - S.eval x‖ ≤ Real.exp b * δ

theorem exists_antisymmetric_local_models :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q : ℝ}
      {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
      {N : ℕ} [NeZero N] {V : NativeAntisymmetricOrbitFactors W N p}
      (R : NativeAntisymmetricFrozenDescent V q),
      ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ y : Fin 4 → ℤ, (∀ i, |(y i : ℝ)| ≤ (N : ℝ)) →
          ∃ S : R.model.Niltest (fun _ : Fin 4 => 1), S.orbit = R.orbit ∧ S.ComplexityLE q ∧
            ∀ (x : Fin 4 → ℤ) (δ : ℝ), 0 ≤ δ →
              (∀ i, |(x i : ℝ)| ≤ (N : ℝ)) → (∀ i, (P : ℤ) ∣ x i - y i) →
              (∀ i, |(x i : ℝ) - (y i : ℝ)| ≤ (N : ℝ) * δ) →
              ‖W.antisymmetricBoxValue V.leftIndex V.rightIndex x - S.eval x‖ ≤
                Real.exp ((p + C) ^ C) * δ := by
  obtain ⟨A, _, hcontrol⟩ := exists_antisymmetric_local_control
  let X : Polynomial ℕ := Polynomial.X
  let Y := X + 8
  let T := (Y + 2) ^ 2 + Y + (Y + (Y ^ 2 + Y + 3) ^ 2) + Y ^ 2 + 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C A) ^ A + T)
  refine ⟨C, hC, ?_⟩
  intro p q W N _ V R
  have hp := R.nonnegative
  let := R.productTopology
  let := R.productTopologicalAdd
  let := R.productContinuousSMul
  let := R.productHausdorff
  let D := pi (fun _ : Fin 8 => W.model)
  let T₀ := W.antisymmetricBoxNiltest hp V.leftIndex V.rightIndex
  let a := fun x : Fin 4 → ℤ => D.filtration.adaptedPolynomialRealValueHom
    (fun _ : Fin 4 => 1) (fun i => (x i : ℝ)) V.slow
  let b := fun x : Fin 4 → ℤ => D.filtration.adaptedPolynomialRealValueHom
    (fun _ : Fin 4 => 1) (fun i => (x i : ℝ)) V.middle
  let r := fun x : Fin 4 → ℤ => D.filtration.adaptedPolynomialRealValueHom
    (fun _ : Fin 4 => 1) (fun i => (x i : ℝ)) V.rational
  let t := productNiltestBudget (p + 8)
  have ht : 0 ≤ t := by dsimp [t]; unfold productNiltestBudget productObservableLipBudget; positivity
  have hsum : (p + A) ^ A + t ≤ (p + C) ^ C := by
    simpa [T, Y, X, t, productNiltestBudget, productObservableLipBudget, Polynomial.eval₂_pow]
      using hbudget p hp
  have hAC : (p + A) ^ A ≤ (p + C) ^ C := (le_add_of_nonneg_right ht).trans hsum
  obtain ⟨P, hP, hPb, hperiod, hmotion⟩ := hcontrol W V hp
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  have hLip : (T₀.lipBound : ℝ) ≤ Real.exp t := by
    have h := T₀.observable_budget (W.antisymmetricBoxNiltest_complexity hp V.leftIndex V.rightIndex)
    linarith [T₀.normBound.coe_nonneg]
  refine ⟨P, hP, hPb.trans (Real.exp_le_exp.mpr hAC), ?_⟩
  intro y hy
  obtain ⟨S, hSo, _, hSc, hSe⟩ := R.descend (a y) (r y) (R.slow_values y hy) (R.rational_values y)
  refine ⟨S, hSo, hSc, ?_⟩
  intro x δ hδ hx hres hnear
  have heq : W.antisymmetricBoxValue V.leftIndex V.rightIndex x =
      T₀.observable (QuotientGroup.mk (a x * b x * r y)) :=
    (V.eval_factors hp x).trans
      (D.observable_frozen_right_eq T₀.observable (a x) (b x) (r x) (r y)
        (hperiod x y hres).1)
  have hchange := D.frozen_observable_change_left T₀.observable T₀.lipschitz (a x) (a y) (b x) (r y)
  have hdist := hmotion x y δ hδ hx hy hnear
  apply (congrArg₂ (fun z w : ℂ => ‖z - w‖) heq (hSe x)).trans_le
  apply hchange.trans
  calc
    _ ≤ Real.exp t * (Real.exp ((p + A) ^ A) * δ) :=
      mul_le_mul hLip hdist dist_nonneg (Real.exp_nonneg t)
    _ = Real.exp (t + (p + A) ^ A) * δ := by rw [← mul_assoc, ← Real.exp_add]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) hδ

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeAntisymmetricFrozenDescent.lie NativeAntisymmetricFrozenDescent.algebra
  NativeAntisymmetricFrozenDescent.topology NativeAntisymmetricFrozenDescent.topologicalAdd
  NativeAntisymmetricFrozenDescent.continuousSMul NativeAntisymmetricFrozenDescent.hausdorff

theorem NativeAntisymmetricLocalModels.select_partition {p q b : ℝ}
    {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {N : ℕ} [NeZero N]
    {V : NativeAntisymmetricOrbitFactors W N p} {R : NativeAntisymmetricFrozenDescent V q}
    (L : NativeAntisymmetricLocalModels R b) {I : Type*} [Fintype I]
    (B : Finset (ZMod N)) (A : I → (Fin 4 → ZMod N) → ℝ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hA : ∀ j x, 0 ≤ A j x) (hsum : ∀ x, ∑ j, A j x = 1)
    (hcells : ∀ j x y, (∀ i, x i ∉ B) → (∀ i, y i ∉ B) → 0 < A j x → 0 < A j y →
      (∀ i, (L.period : ℤ) ∣ ((x i).val : ℤ) - (y i).val) ∧
      (∀ i, |((x i).val : ℝ) - (y i).val| ≤ (N : ℝ) * ρ)) :
    ∃ S : I → R.model.Niltest (fun _ : Fin 4 => 1),
      (∀ j, (S j).orbit = R.orbit) ∧ (∀ j, (S j).ComplexityLE q) ∧
      (𝔼 x : Fin 4 → ZMod N,
        ‖W.antisymmetricBoxValue V.leftIndex V.rightIndex (fun i => ((x i).val : ℤ)) -
          ∑ j, (A j x : ℂ) * (S j).evalCyclic N x‖) ≤
        Real.exp b * ρ + 8 * Real.exp q * B.card / N := by
  classical
  let v := fun (x : Fin 4 → ZMod N) (i : Fin 4) => ((x i).val : ℤ)
  have hv (x : Fin 4 → ZMod N) (i : Fin 4) : |(v x i : ℝ)| ≤ (N : ℝ) := by
    simp only [v, Int.cast_natCast]
    rw [abs_of_nonneg (Nat.cast_nonneg ((x i).val))]
    exact Nat.cast_le.mpr (x i).val_lt.le
  let F := fun x : Fin 4 → ZMod N => W.antisymmetricBoxValue V.leftIndex V.rightIndex (v x)
  let E := coordinateExceptional (ι := Fin 4) B
  have hchoose (j : I) : ∃ y : Fin 4 → ZMod N,
      ∀ x, (∀ i, x i ∉ B) → 0 < A j x → (∀ i, y i ∉ B) ∧ 0 < A j y := by
    by_cases h : ∃ y, (∀ i, y i ∉ B) ∧ 0 < A j y
    · obtain ⟨y, hy⟩ := h
      exact ⟨y, fun _ _ _ => hy⟩
    · exact ⟨0, fun x hx hAx => False.elim (h ⟨x, hx, hAx⟩)⟩
  choose y hy using hchoose
  choose S hSo hSc hSe using fun j => L.local_model (v (y j)) (hv (y j))
  have hpoint (j : I) (x : Fin 4 → ZMod N) (hx : x ∉ E) (hAx : 0 < A j x) :
      ‖F x - (S j).evalCyclic N x‖ ≤ Real.exp b * ρ := by
    have hx' := (not_mem_coordinateExceptional B x).mp hx
    obtain ⟨hy', hAy⟩ := hy j x hx' hAx
    obtain ⟨hres, hnear⟩ := hcells j x (y j) hx' hy' hAx hAy
    exact hSe j (v x) ρ hρ (hv x) hres (by simpa only [v, Int.cast_natCast] using hnear)
  have hF (x : Fin 4 → ZMod N) : ‖F x‖ ≤ Real.exp q := by
    obtain ⟨T, _hTo, hTc, hTx⟩ := R.exists_diagonal_niltest (v x) (hv x)
    rw [show F x = T.eval (v x) from hTx.symm]
    exact T.eval_budget hTc (v x)
  have hcap (x : Fin 4 → ZMod N) :
      ‖F x - ∑ j, (A j x : ℂ) * (S j).evalCyclic N x‖ ≤ 2 * Real.exp q := by
    apply norm_sub_positive_sum_le (fun j => A j x) (fun j => (S j).evalCyclic N x)
      (F x) (2 * Real.exp q) (fun j => hA j x) (hsum x)
    intro j _
    have hSj : ‖(S j).evalCyclic N x‖ ≤ Real.exp q := (S j).eval_budget (hSc j) (v x)
    exact (norm_sub_le _ _).trans (by linarith [hSj, hF x])
  have hgood (x : Fin 4 → ZMod N) (hx : x ∉ E) :
      ‖F x - ∑ j, (A j x : ℂ) * (S j).evalCyclic N x‖ ≤ Real.exp b * ρ :=
    norm_sub_positive_sum_le (fun j => A j x) (fun j => (S j).evalCyclic N x)
      (F x) (Real.exp b * ρ) (fun j => hA j x) (hsum x) (fun j => hpoint j x hx)
  have herr := expect_abs_le_of_exceptional_set E
    (fun x => ‖F x - ∑ j, (A j x : ℂ) * (S j).evalCyclic N x‖)
    (mul_nonneg (Real.exp_nonneg b) hρ)
    (fun x => by simpa only [abs_of_nonneg (norm_nonneg _)] using hcap x)
    (fun x hx => by simpa only [abs_of_nonneg (norm_nonneg _)] using hgood x hx)
  have hdensity : (E.card : ℝ) / Fintype.card (Fin 4 → ZMod N) ≤ 4 * (B.card : ℝ) / N := by
    simpa only [Fintype.card_fin, ZMod.card, Nat.cast_ofNat] using
      coordinateExceptional_density_le (ι := Fin 4) B
  refine ⟨S, hSo, hSc, ?_⟩
  have herr' : (𝔼 x : Fin 4 → ZMod N, ‖F x - ∑ j, (A j x : ℂ) * (S j).evalCyclic N x‖) ≤
      Real.exp b * ρ + (2 * Real.exp q) * ((E.card : ℝ) / Fintype.card (Fin 4 → ZMod N)) := by
    simpa only [abs_of_nonneg (norm_nonneg _), mul_div_assoc] using herr
  apply herr'.trans
  calc
    _ ≤ Real.exp b * ρ + (2 * Real.exp q) * (4 * (B.card : ℝ) / N) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hdensity
        (show (0 : ℝ) ≤ 2 * Real.exp q by positivity))
    _ = _ := by ring

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeAntisymmetricFrozenDescent.lie NativeAntisymmetricFrozenDescent.algebra
  NativeAntisymmetricFrozenDescent.topology NativeAntisymmetricFrozenDescent.topologicalAdd
  NativeAntisymmetricFrozenDescent.continuousSMul NativeAntisymmetricFrozenDescent.hausdorff

theorem exists_antisymmetric_partition_approximation (a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q b t : ℝ}
      {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
      {N : ℕ} [NeZero N] {V : NativeAntisymmetricOrbitFactors W N p}
      (R : NativeAntisymmetricFrozenDescent V q) (L : NativeAntisymmetricLocalModels R b),
      letI : NeZero L.period := ⟨L.period_pos.ne'⟩
      0 ≤ t → q ≤ t → b ≤ t → ∀ {ρ : ℝ}, 0 < ρ → 1 / ρ ≤ Real.exp ((t + 2) ^ a) →
      ∃ n : ℕ, 0 < n ∧
        (Fintype.card (Fin 4 → Fin n × ZMod L.period) : ℝ) ≤ Real.exp ((t + C) ^ C) ∧
        ∃ A : (Fin n × ZMod L.period) → ZMod N → ℝ,
          (∀ j, PositiveCyclicNiltest.{0} 1 N ((t + C) ^ C) (A j)) ∧
          (∀ x, ∑ j, A j x = 1) ∧
          ∃ S : (Fin 4 → Fin n × ZMod L.period) → R.model.Niltest (fun _ : Fin 4 => 1),
            (∀ j, (S j).orbit = R.orbit) ∧ (∀ j, (S j).ComplexityLE ((t + C) ^ C)) ∧
            (𝔼 x : Fin 4 → ZMod N,
              ‖W.antisymmetricBoxValue V.leftIndex V.rightIndex (fun i => ((x i).val : ℤ)) -
                ∑ j, ((∏ i, A (j i) (x i)) : ℝ) * (S j).evalCyclic N x‖) ≤
              Real.exp (t + 73) * (ρ + 1 / N) := by
  obtain ⟨B, _, hpartition⟩ := exists_interval_residue_partition a
  let X : Polynomial ℕ := Polynomial.X
  let P := X + 73 + 4 * (X + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro p q b t W N _ V R L
  let : NeZero L.period := ⟨L.period_pos.ne'⟩
  intro ht hqt hbt ρ hρ hprec
  have hM : (L.period : ℝ) ≤ Real.exp t := L.period_bound.trans (Real.exp_le_exp.mpr hbt)
  obtain ⟨n, hn, hcard, A, hA, hsum, hdiam⟩ := hpartition N L.period ht hM hρ hprec
  have hsumcost : t + 73 + 4 * (t + B) ^ B ≤ (t + C) ^ C := by
    simpa [P, X, Polynomial.eval₂_pow] using hbudget t ht
  have hbase : 0 ≤ (t + B) ^ B := by positivity
  have hfour : 4 * (t + B) ^ B ≤ (t + C) ^ C := by linarith
  have hcost : (t + B) ^ B ≤ (t + C) ^ C := by linarith
  have htC : t + 73 ≤ (t + C) ^ C := by linarith
  let w := productPartitionWeight (fun _ : Fin 4 => A)
  let E := cyclicWrapExceptional (0 : ZMod N) ρ
  have hnonneg : ∀ i j x, 0 ≤ (fun _ : Fin 4 => A) i j x :=
    fun _ j x => ((hA j).unit_interval x).1
  have hw : ∀ j x, 0 ≤ w j x := productPartitionWeight_nonneg _ hnonneg
  have hwSum : ∀ x, ∑ j, w j x = 1 := sum_productPartitionWeight _ (fun _ => hsum)
  have hcells : ∀ j x y, (∀ i, x i ∉ E) → (∀ i, y i ∉ E) → 0 < w j x → 0 < w j y →
      (∀ i, (L.period : ℤ) ∣ ((x i).val : ℤ) - (y i).val) ∧
      (∀ i, |((x i).val : ℝ) - (y i).val| ≤ (N : ℝ) * ρ) := by
    intro j x y hx hy hwx hwy
    have hposx := productPartitionWeight_pos_coordinate _ hnonneg j x hwx
    have hposy := productPartitionWeight_pos_coordinate _ hnonneg j y hwy
    exact ⟨fun i => (hdiam (j i) (x i) (y i) (hx i) (hy i) (hposx i) (hposy i)).2,
      fun i => (hdiam (j i) (x i) (y i) (hx i) (hy i) (hposx i) (hposy i)).1⟩
  obtain ⟨S, hSo, hSc, herr⟩ := L.select_partition E w hρ.le hw hwSum hcells
  refine ⟨n, hn, ?_, A, fun j => (hA j).mono le_rfl hcost, hsum,
    S, hSo, fun j => (hSc j).mono (hqt.trans (by linarith)), ?_⟩
  · simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow]
    calc
      _ ≤ (Real.exp ((t + B) ^ B)) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg _) hcard 4
      _ = Real.exp (4 * (t + B) ^ B) := (Real.exp_nat_mul _ 4).symm
      _ ≤ _ := Real.exp_le_exp.mpr hfour
  · have hE := cyclicWrapExceptional_density_le (0 : ZMod N) hρ.le
    have hqexp : Real.exp q ≤ Real.exp t := Real.exp_le_exp.mpr hqt
    have hbexp : Real.exp b ≤ Real.exp t := Real.exp_le_exp.mpr hbt
    have hN : 0 ≤ (1 : ℝ) / N := one_div_nonneg.mpr (Nat.cast_nonneg N)
    have h73 : (73 : ℝ) ≤ Real.exp 73 := by linarith [Real.add_one_le_exp (73 : ℝ)]
    apply herr.trans
    calc
      _ = Real.exp b * ρ + (8 * Real.exp q) * ((E.card : ℝ) / N) := by ring
      _ ≤ Real.exp b * ρ + (8 * Real.exp q) * (6 * ρ + 3 / N) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hE
          (show (0 : ℝ) ≤ 8 * Real.exp q by positivity))
      _ ≤ Real.exp t * ρ + (8 * Real.exp t) * (6 * ρ + 3 / N) := by gcongr
      _ = Real.exp t * (49 * ρ + 24 * (1 / N)) := by ring
      _ ≤ Real.exp t * (73 * (ρ + 1 / N)) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.exp_nonneg t)
      _ = 73 * Real.exp t * (ρ + 1 / N) := by ring
      _ ≤ Real.exp 73 * Real.exp t * (ρ + 1 / N) := by gcongr
      _ = Real.exp (t + 73) * (ρ + 1 / N) := by rw [← Real.exp_add, add_comm 73 t]

end Erdos3

end

end OAI
