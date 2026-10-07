import OAI.Combinatorics.Progressions.Lattices.TopInvariantIntegerExpansion

namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def normalizedSquareProjectionBudget (p : ℝ) : ℝ :=
  (squareGeometryBudget p + p + 4) ^ 2

noncomputable def normalizedSquareLeftBudget (a b : ℕ) (p : ℝ) : ℝ :=
  (p + a + 2 + b) ^ b

noncomputable def normalizedSquareObservableBudget (a b : ℕ) (p : ℝ) : ℝ :=
  2 * p + normalizedSquareProjectionBudget p + normalizedSquareLeftBudget a b p + 1

noncomputable def normalizedSquareReconstructionBudget (a b : ℕ) (p : ℝ) : ℝ :=
  squareGeometryBudget p + 1 + normalizedSquareObservableBudget a b p + 2 * p

noncomputable def normalizedSquareComplexityBudget (a b c : ℕ) (p : ℝ) : ℝ :=
  squareGeometryBudget p + 2 * p + (normalizedSquareReconstructionBudget a b p + c) ^ c + 4

theorem normalizedSquareProjectionBudget_nonneg (p : ℝ) :
    0 ≤ normalizedSquareProjectionBudget p := sq_nonneg _

theorem normalizedSquareLeftBudget_nonneg (a b : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ normalizedSquareLeftBudget a b p := by
  unfold normalizedSquareLeftBudget
  positivity

theorem normalizedSquareObservableBudget_nonneg (a b : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ normalizedSquareObservableBudget a b p := by
  have h1 := normalizedSquareProjectionBudget_nonneg p
  have h2 := normalizedSquareLeftBudget_nonneg a b hp
  unfold normalizedSquareObservableBudget
  linarith

theorem normalizedSquareReconstructionBudget_nonneg (a b : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ normalizedSquareReconstructionBudget a b p := by
  have h1 := squareGeometryBudget_nonneg hp
  have h2 := normalizedSquareObservableBudget_nonneg a b hp
  unfold normalizedSquareReconstructionBudget
  linarith

theorem exists_normalizedSquareComplexityBudget_bound (a b c : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → normalizedSquareComplexityBudget a b c p ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let Q := ((X + 3) ^ 11 + 2 * X + 5) ^ 11
  let U := 2 * X + (Q + X + 4) ^ 2 + (X + Polynomial.C a + 2 + Polynomial.C b) ^ b + 1
  let R := Q + 1 + U + 2 * X
  let P := Q + 2 * X + (R + Polynomial.C c) ^ c + 4
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, fun p hp => ?_⟩
  simpa [P, R, U, Q, X, Polynomial.eval₂_pow, normalizedSquareComplexityBudget, normalizedSquareReconstructionBudget,
    normalizedSquareObservableBudget, normalizedSquareProjectionBudget,
    normalizedSquareLeftBudget, squareGeometryBudget] using hbound p hp

theorem squareObservableLipschitz_le_exp (A B K J : ℝ≥0) {p q r : ℝ}
    (hr : 0 ≤ r) (hA : (A : ℝ) ≤ Real.exp r) (hB : (B : ℝ) ≤ Real.exp p)
    (hK : (K : ℝ) ≤ Real.exp p) (hJ : (J : ℝ) ≤ Real.exp q) :
    ((B * (K * J) + B * (K * (A * J)) : ℝ≥0) : ℝ) ≤ Real.exp (2 * p + q + r + 1) := by
  have hfirst : (B : ℝ) * (K * J) ≤ Real.exp (2 * p + q) := by
    calc
      _ ≤ Real.exp p * (Real.exp p * Real.exp q) := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hsecond : (B : ℝ) * (K * (A * J)) ≤ Real.exp (2 * p + q + r) := by
    calc
      _ ≤ Real.exp p * (Real.exp p * (Real.exp r * Real.exp q)) := by gcongr
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  have hfirst' := hfirst.trans (Real.exp_le_exp.mpr (by linarith : 2 * p + q ≤ 2 * p + q + r))
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  change (B : ℝ) * (K * J) + B * (K * (A * J)) ≤ _
  calc
    _ ≤ 2 * Real.exp (2 * p + q + r) := by linarith
    _ ≤ Real.exp 1 * Real.exp (2 * p + q + r) :=
      mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem niltest_log_bound_of_exp (x y : ℝ≥0) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : (x : ℝ) ≤ Real.exp a) (hy : (y : ℝ) ≤ Real.exp b) :
    Real.log (2 + (x : ℝ) + y) ≤ a + b + 4 := by
  apply (Real.log_le_iff_le_exp (by positivity : 0 < 2 + (x : ℝ) + y)).mpr
  have hx' := hx.trans (Real.exp_le_exp.mpr (by linarith : a ≤ a + b))
  have hy' := hy.trans (Real.exp_le_exp.mpr (by linarith : b ≤ a + b))
  have h1 : 1 ≤ Real.exp (a + b) := Real.one_le_exp (by linarith)
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  calc
    _ ≤ 4 * Real.exp (a + b) := by linarith
    _ ≤ Real.exp 4 * Real.exp (a + b) := mul_le_mul_of_nonneg_right h4 (Real.exp_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_bounded_normalization_left_lipschitz (s a : ℕ) :
    ∃ b : ℕ, 2 ≤ b ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (p : ℝ),
      0 ≤ p → D.GeometryComplexityLE p →
      ∃ A : ℝ≥0, 0 < A ∧ (A : ℝ) ≤ Real.exp (normalizedSquareLeftBudget a b p) ∧
        ∀ ε : D.RealGroup,
          (∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp ((p + 1 + a) ^ a)) →
          letI := D.metricSpace
          LipschitzWith A (fun x : D.Space => ε • x) := by
  obtain ⟨b, hb, hleft⟩ := exists_uniform_quotient_left_lipschitz_exp_bound s a
  refine ⟨b, hb, ?_⟩
  intro L _ _ d _ _ _ _ D p hp hD
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  let q := p + a + 2
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hH : (⌈Real.exp p⌉₊ : ℝ) ≤ Real.exp q :=
    (ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr (by dsimp [q]; linarith))
  obtain ⟨A, hA, hAp, hLip⟩ := hleft (D.basis.baseChange ℝ)
    (lieStructureConstants D.basis) ⌈Real.exp p⌉₊ q
    D.filtration.realification.lowerCentralSeries_eq_bot
    (fun i j k => (realLieBasis_structure D.basis i j k).symm) hq
    (by simpa only [Fintype.card_fin] using hD.1.trans hpq) hH
    (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k))
  refine ⟨A, hA, hAp, ?_⟩
  intro ε hε
  apply hLip D.realLattice (D.realLattice_closed_discrete).1 ε
  intro i
  apply (hε i).trans (Real.exp_le_exp.mpr _)
  apply pow_le_pow_left₀ (by positivity)
  dsimp [q]
  linarith

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

noncomputable def comparisonProductLip (c : ℕ) (K L A : ℝ≥0) (p : ℝ) : ℝ≥0 :=
  c * K * (A * ⟨Real.exp ((p + 3) ^ 2), (Real.exp_pos _).le⟩) +
    L * ⟨Real.exp ((p + 3) ^ 2), (Real.exp_pos _).le⟩

theorem comparisonProductLip_le_exp (c : ℕ) (K L A : ℝ≥0) {p : ℝ} (hp : 0 ≤ p)
    (hc : (c : ℝ) ≤ Real.exp p) (hK : (K : ℝ) ≤ Real.exp p)
    (hL : (L : ℝ) ≤ Real.exp p) (hA : (A : ℝ) ≤ Real.exp p) :
    (comparisonProductLip c K L A p : ℝ) ≤ Real.exp ((p + 3) ^ 2 + 3 * p + 1) := by
  have hleft : (c : ℝ) * K * A ≤ Real.exp (3 * p) := by
    calc
      _ ≤ Real.exp p * Real.exp p * Real.exp p :=
        mul_le_mul (mul_le_mul hc hK K.coe_nonneg (Real.exp_pos _).le) hA
          A.coe_nonneg (by positivity)
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hright : (L : ℝ) ≤ Real.exp (3 * p) :=
    hL.trans (Real.exp_le_exp.mpr (by linarith))
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  change (c : ℝ) * K * (A * Real.exp ((p + 3) ^ 2)) + L * Real.exp ((p + 3) ^ 2) ≤ _
  calc
    _ = ((c : ℝ) * K * A + L) * Real.exp ((p + 3) ^ 2) := by ring
    _ ≤ (2 * Real.exp (3 * p)) * Real.exp ((p + 3) ^ 2) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
    _ ≤ (Real.exp 1 * Real.exp (3 * p)) * Real.exp ((p + 3) ^ 2) := by gcongr
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

noncomputable def comparisonProductCost (p : ℝ) : ℝ := (p + 3) ^ 2 + 3 * p + 5

noncomputable def comparisonDescentBudget (s : ℕ) (p : ℝ) : ℝ :=
  (comparisonProductCost p + RationalFilteredNilmanifold.topInvariantIntegerExponent s) ^
    RationalFilteredNilmanifold.topInvariantIntegerExponent s

theorem exists_comparisonDescent_cost (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → comparisonDescentBudget s p ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let a := RationalFilteredNilmanifold.topInvariantIntegerExponent s
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + 3) ^ 2 + 3 * X + 5 + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa [comparisonDescentBudget, comparisonProductCost, a, X, Polynomial.eval₂_pow] using hbudget p hp

end Erdos3

end

section

namespace Erdos3

noncomputable def comparisonEquivalenceBudget (s : ℕ) (p : ℝ) : ℝ :=
  comparisonDescentBudget s p + ((s + 1).factorial + 1 : ℝ) * (p + 1)

theorem comparisonEquivalenceBudget_bounds (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    comparisonDescentBudget s p ≤ comparisonEquivalenceBudget s p ∧
    p ≤ comparisonEquivalenceBudget s p ∧
    ((s + 1).factorial : ℝ) * p ≤ comparisonEquivalenceBudget s p := by
  have hdescent : 0 ≤ comparisonDescentBudget s p := by
    dsimp [comparisonDescentBudget, comparisonProductCost]
    positivity
  have hf : 0 ≤ ((s + 1).factorial : ℝ) := Nat.cast_nonneg _
  dsimp [comparisonEquivalenceBudget]
  constructor
  · nlinarith
  constructor <;> nlinarith

theorem exists_comparisonEquivalence_cost (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p → comparisonEquivalenceBudget s p ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let a := RationalFilteredNilmanifold.topInvariantIntegerExponent s
  let P := ((X + 3) ^ 2 + 3 * X + 5 + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (P + Polynomial.C ((s + 1).factorial + 1) * (X + 1))
  refine ⟨C, hC, ?_⟩
  intro p hp
  simpa [comparisonEquivalenceBudget, comparisonDescentBudget, comparisonProductCost,
    a, X, P, Polynomial.eval₂_pow] using hbudget p hp

end Erdos3

end

end OAI
