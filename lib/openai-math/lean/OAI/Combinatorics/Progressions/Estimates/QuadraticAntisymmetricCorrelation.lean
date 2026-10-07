import OAI.Combinatorics.Progressions.Geometry.NativeCoordinatePairs

namespace OAI

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_reflected_factor_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (z : ℤ),
      NativeIntegerVectorEquivalence 1 ((p + C) ^ C)
        (fun k (x : Fin 2 → ℤ) => W.eval k (correlationInput (x 0) (z - x 0 - x 1)))
        (fun k : Fin W.outputDim × Fin W.outputDim => fun x =>
          W.eval k.1 (correlationInput (x 0) (z - x 0)) *
            star (W.eval k.2 (correlationInput (x 0) (x 1)))) := by
  obtain ⟨C, hC, hadd⟩ := exists_addition_equivalence (mixedCorrelationDegree 1)
  refine ⟨C, hC, ?_⟩
  intro p W z
  let A : Option (Fin 2) → Fin 2 → ℤ := fun j => match j with
    | none => ![0, 1]
    | some i => if i = 0 then ![1, 0] else ![-1, -1]
  let b : Option (Fin 2) → ℤ := fun j => match j with
    | none => 0
    | some i => if i = 0 then 0 else z
  have hinput (x : Fin 2 → ℤ) : integerAffineMap A b x =
      coordinatePairInput (1 : Fin 2) (z - x 0 - x 1) (x 1) (x 0) := by
    funext j
    cases j with
    | none => simp [integerAffineMap, A, b, coordinatePairInput, Fin.sum_univ_two]
    | some i =>
      fin_cases i
      · simp [integerAffineMap, A, b, coordinatePairInput, coordinateConstantInput,
          Fin.sum_univ_two]
      · simp [integerAffineMap, A, b, coordinatePairInput, coordinateConstantInput,
          Fin.sum_univ_two]
        ring
  have hcoordinate (a n : ℤ) : coordinateConstantInput (1 : Fin 2) a n =
      correlationInput n a := by
    funext i
    fin_cases i <;> rfl
  have hdegree : (∑ i, mixedCorrelationDegree 1 i) - 1 = 1 := by
    rw [Fin.sum_univ_two]
    rfl
  have E := (hadd W (1 : Fin 2) rfl).affinePullback A b
  have E' : NativeIntegerVectorEquivalence 1 ((p + C) ^ C)
      (fun k (x : Fin 2 → ℤ) => W.eval k (correlationInput (x 0) (z - x 0)))
      (fun k : Fin W.outputDim × Fin W.outputDim => fun x =>
        W.eval k.1 (correlationInput (x 0) (z - x 0 - x 1)) *
          W.eval k.2 (correlationInput (x 0) (x 1))) := by
    simpa only [hdegree, coordinateSumVector, coordinateTensorVector, hinput,
      coordinatePairInput_sum, coordinatePairInput_left, coordinatePairInput_right,
      sub_add_cancel, hcoordinate] using E
  refine ⟨E'.left_dimension, E'.right_dimension, ?_⟩
  intro i k
  obtain ⟨R⟩ := E'.symm.expansion (i, k.2) k.1
  have heq : (fun x : Fin 2 → ℤ =>
      (W.eval i (correlationInput (x 0) (z - x 0 - x 1)) *
        W.eval k.2 (correlationInput (x 0) (x 1))) *
          star (W.eval k.1 (correlationInput (x 0) (z - x 0)))) =
      (fun x => W.eval i (correlationInput (x 0) (z - x 0 - x 1)) *
        star (W.eval k.1 (correlationInput (x 0) (z - x 0)) *
          star (W.eval k.2 (correlationInput (x 0) (x 1))))) := by
    funext x
    simp only [star_mul, star_star]
    ring
  exact ⟨heq ▸ R⟩

theorem exists_reflected_pair_equivalence :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (z : ℤ),
      NativeIntegerVectorEquivalence 1 ((p + C) ^ C)
        (fun k : Fin W.outputDim × Fin W.outputDim => fun x : Fin 2 → ℤ =>
          W.eval k.1 (correlationInput (x 0) (z - x 0 - x 1)) *
            star (W.eval k.2 (correlationInput (x 1) (z - x 0 - x 1))))
        (fun k : (Fin W.outputDim × Fin W.outputDim) ×
            (Fin W.outputDim × Fin W.outputDim) => fun x =>
          W.eval k.1.1 (correlationInput (x 0) (z - x 0)) *
            star (W.eval k.2.1 (correlationInput (x 1) (z - x 1))) *
            star (W.eval k.1.2 (correlationInput (x 0) (x 1))) *
            W.eval k.2.2 (correlationInput (x 1) (x 0))) := by
  obtain ⟨a, _, hfactor⟩ := exists_reflected_factor_equivalence
  obtain ⟨b, _, htensor⟩ := NativeIntegerVectorEquivalence.exists_tensor_budget
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((X + Polynomial.C a) ^ a + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p W z
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let q := (p + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have E := hfactor W z
  have F := (E.coordinatePullback (![1, 0] : Fin 2 → Fin 2)).conjugate
  have R := htensor hq E F
  have hcost : (q + b) ^ b ≤ (p + C) ^ C := by
    simpa [X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hsub (x : Fin 2 → ℤ) : z - x 1 - x 0 = z - x 0 - x 1 := by abel
  simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, hsub, star_mul, star_star,
    mul_assoc, mul_comm, mul_left_comm] using R.mono hcost

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeTwoVariableSplit.lie NativeTwoVariableSplit.algebra
  NativeTwoVariableSplit.topology NativeTwoVariableSplit.topologicalAdd
  NativeTwoVariableSplit.continuousSMul NativeTwoVariableSplit.hausdorff

theorem NativeTwoVariableSplit.second_eval_eq_degree_one {d : ℕ} {p epsilon : ℝ}
    {f : (Fin 2 → ℤ) → ℂ} (R : NativeTwoVariableSplit 1 d p epsilon f)
    (j : Fin R.count) (x y : Fin 2 → ℤ) (hxy : x 0 = y 0) :
    (R.test true j).eval x = (R.test true j).eval y := by
  unfold RationalFilteredNilmanifold.Niltest.eval
  rw [R.test_orbit true j, (R.multi true).orbitToOrdinary_eval,
    (R.multi true).orbitToOrdinary_eval]
  apply congrArg (R.test true j).observable
  apply congrArg QuotientGroup.mk
  apply (R.multi true).filtration.realification.polynomialOrbitEval_eq_of_zero_coordinate
    1 (show totalDegreeSplitBound 1 true 1 = 0 from rfl) (R.orbit true) x y
  intro i hi
  fin_cases i
  · exact hxy
  · exact (hi rfl).elim

theorem exists_linear_separated_approximation :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} {D : RationalFilteredNilmanifold L 1 d} {p : ℝ}
      (T : D.Niltest (fun _ : Fin 2 => 1)), T.ComplexityLE p → T.normBound ≤ 1 →
      ∀ epsilon : ℝ, 0 < epsilon → 1 / epsilon ≤ Real.exp ((p + 2) ^ 2) →
      ∃ r : ℕ, 0 < r ∧ (r : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ A B : Fin r → ℤ → ℂ,
          (∀ j x, ‖A j x‖ ≤ 1) ∧ (∀ j y, ‖B j y‖ ≤ 1) ∧
          ∀ x y, ‖T.eval ![x, y] - ∑ j, A j x * B j y‖ ≤ epsilon := by
  obtain ⟨C, hC, hsplit⟩ := exists_totalDegree_niltest_splitting 1 2
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D p T hT hnorm epsilon hepsilon hscale
  obtain ⟨R⟩ := hsplit T hT hnorm epsilon hepsilon hscale
  let A (j : Fin R.count) (x : ℤ) := (R.test true j).eval ![x, 0]
  let B (j : Fin R.count) (y : ℤ) := (R.test false j).eval ![0, y]
  refine ⟨R.count, R.count_pos, R.count_bound, A, B, ?_, ?_, ?_⟩
  · intro j x
    exact ((R.test true j).norm_eval_le _).trans
      (show ((R.test true j).normBound : ℝ) ≤ 1 from R.test_norm true j)
  · intro j y
    exact ((R.test false j).norm_eval_le _).trans
      (show ((R.test false j).normBound : ℝ) ≤ 1 from R.test_norm false j)
  · intro x y
    have heq (j : Fin R.count) :
        (R.test false j).eval ![x, y] * (R.test true j).eval ![x, y] = A j x * B j y := by
      rw [R.first_eval_eq j ![x, y] ![0, y] rfl,
        R.second_eval_eq_degree_one j ![x, y] ![x, 0] rfl]
      exact mul_comm _ _
    simpa only [heq] using R.approximation ![x, y]

theorem exists_absorb_linear_error :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} {D : RationalFilteredNilmanifold L 1 d} {p : ℝ}
      (T : D.Niltest (fun _ : Fin 2 => 1)), T.ComplexityLE p →
      ∀ {X : Type*} (S : Finset X), S.Nonempty → ∀ (x y : X → ℤ) (F : X → ℂ),
        (∀ u ∈ S, ‖F u‖ ≤ 1) →
        Real.exp (-p) ≤ ‖𝔼 u ∈ S, F u * T.eval ![x u, y u]‖ →
        ∃ A B : ℤ → ℂ, (∀ x, ‖A x‖ ≤ 1) ∧ (∀ y, ‖B y‖ ≤ 1) ∧
          Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 u ∈ S, F u * A (x u) * B (y u)‖ := by
  obtain ⟨a, _, hsplit⟩ := exists_linear_separated_approximation
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (2 * X + (X + Polynomial.C a) ^ a + 1)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d D p T hT Ω S hS x y F hF hcorr
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hT.1.1
  let U := T.conjugate.expNormalize p
  let epsilon := Real.exp (-(2 * p + 1))
  have hscale : 1 / epsilon ≤ Real.exp ((p + 2) ^ 2) := by
    dsimp [epsilon]
    rw [one_div, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg p]
  obtain ⟨r, _, hr, A, B, hA, hB, happ⟩ := hsplit U
    (T.conjugate.expNormalize_complexity hT) (T.conjugate.expNormalize_norm hT)
    epsilon (Real.exp_pos _) hscale
  have hmean : (𝔼 u ∈ S, F u * star (U.eval ![x u, y u])) =
      (Real.exp (-p) : ℂ) * (𝔼 u ∈ S, F u * T.eval ![x u, y u]) := by
    rw [Finset.mul_expect]
    apply Finset.expect_congr rfl
    intro u _
    simp only [U, RationalFilteredNilmanifold.Niltest.expNormalize_eval,
      RationalFilteredNilmanifold.Niltest.eval_conjugate, star_mul,
      Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
    ring
  have hnorm : Real.exp (-(2 * p)) ≤ ‖𝔼 u ∈ S, F u * star (U.eval ![x u, y u])‖ := by
    rw [hmean, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)]
    calc
      _ = Real.exp (-p) * Real.exp (-p) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hcorr (Real.exp_nonneg _)
  have hepsilon : epsilon ≤ Real.exp (-(2 * p)) / 2 := by
    simpa only [epsilon, show -(2 * p + 1) = -(2 * p) - 1 by ring] using
      exp_sub_one_le_half_exp (-(2 * p))
  obtain ⟨j, hj⟩ := exists_correlating_summand hS F (fun u => U.eval ![x u, y u])
    (fun j u => A j (x u) * B j (y u)) (Real.exp_pos (-(2 * p)))
    (Real.exp_pos ((p + a) ^ a)) (by simpa only [Fintype.card_fin] using hr) hF
    (fun u _ => by rw [norm_sub_rev]; exact (happ (x u) (y u)).trans hepsilon) hnorm
  have hcost : 2 * p + (p + a) ^ a + 1 ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hsmall : Real.exp (-((p + C) ^ C)) ≤
      Real.exp (-(2 * p)) / (2 * Real.exp ((p + a) ^ a)) := by
    calc
      _ ≤ Real.exp (-(2 * p + (p + a) ^ a) - 1) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ Real.exp (-(2 * p + (p + a) ^ a)) / 2 := exp_sub_one_le_half_exp _
      _ = _ := by rw [show -(2 * p + (p + a) ^ a) = -(2 * p) - (p + a) ^ a by ring,
        Real.exp_sub]; ring
  refine ⟨(fun x => star (A j x)), (fun y => star (B j y)), ?_, ?_, ?_⟩
  · intro x
    simpa only [norm_star] using hA j x
  · intro y
    simpa only [norm_star] using hB j y
  · simpa only [finiteCorrelation, star_mul, mul_assoc, mul_comm, mul_left_comm] using hsmall.trans hj

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem NativeMultidegreeNilcharacter.reflected_pair_target_unit {p : ℝ}
    (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (z a b : ℤ) :
    (∑ k : (Fin W.outputDim × Fin W.outputDim) × (Fin W.outputDim × Fin W.outputDim),
      ‖W.eval k.1.1 (correlationInput a (z - a)) *
        star (W.eval k.2.1 (correlationInput b (z - b))) *
        star (W.eval k.1.2 (correlationInput a b)) *
        W.eval k.2.2 (correlationInput b a)‖ ^ 2) = 1 := by
  calc
    _ = ∑ k : (Fin W.outputDim × Fin W.outputDim) × (Fin W.outputDim × Fin W.outputDim),
        ‖(W.eval k.1.1 (correlationInput a (z - a)) *
          star (W.eval k.1.2 (correlationInput a b))) *
          star (W.eval k.2.1 (correlationInput b (z - b)) *
            star (W.eval k.2.2 (correlationInput b a)))‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro k _
      congr 2
      simp only [star_mul, star_star]
      ring
    _ = 1 := by
      simp only [norm_mul, norm_star, mul_pow, Fintype.sum_prod_type,
        ← Finset.mul_sum, W.unit_eval, mul_one]

theorem exists_integer_antisymmetric_correlation :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p) (z : ℤ)
      (i j : Fin W.outputDim) {Ω : Type*} (S : Finset Ω), S.Nonempty →
      ∀ (x y : Ω → ℤ) (a b : ℤ → ℂ), (∀ n, ‖a n‖ ≤ 1) → (∀ n, ‖b n‖ ≤ 1) →
      Real.exp (-p) ≤ ‖𝔼 u ∈ S,
        W.eval i (correlationInput (x u) (z - x u - y u)) *
          star (W.eval j (correlationInput (y u) (z - x u - y u))) * a (x u) * b (y u)‖ →
      ∃ (i' j' : Fin W.outputDim) (A B : ℤ → ℂ),
        (∀ n, ‖A n‖ ≤ 1) ∧ (∀ n, ‖B n‖ ≤ 1) ∧
        Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 u ∈ S,
          star (W.eval i' (correlationInput (x u) (y u))) *
            W.eval j' (correlationInput (y u) (x u)) * A (x u) * B (y u)‖ := by
  obtain ⟨c, _, hcompare⟩ := NativeMultidegreeNilcharacter.exists_reflected_pair_equivalence
  obtain ⟨d, _, habsorb⟩ := exists_absorb_linear_error
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + Polynomial.C c) ^ c
  let R := X + 2 * Q + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((R + Polynomial.C d) ^ d)
  refine ⟨C, hC, ?_⟩
  intro p W z i j Ω S hS x y a b ha hb hcorr
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  let q := (p + c) ^ c
  let r := p + 2 * q + 2
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hqr : q ≤ r := by dsimp [r]; linarith
  have hpr : p + 2 * q ≤ r := by dsimp [r]; linarith
  let E := (hcompare W z).conjugate
  have hunit (u : Ω) : (∑ k : (Fin W.outputDim × Fin W.outputDim) ×
      (Fin W.outputDim × Fin W.outputDim), ‖star (W.eval k.1.1 (correlationInput (x u) (z - x u)) *
      star (W.eval k.2.1 (correlationInput (y u) (z - y u))) *
      star (W.eval k.1.2 (correlationInput (x u) (y u))) *
      W.eval k.2.2 (correlationInput (y u) (x u)))‖ ^ 2) = 1 := by
    simpa only [norm_star] using W.reflected_pair_target_unit z (x u) (y u)
  obtain ⟨k, l, htransfer⟩ := E.transfer_sample_correlation S (fun u => ![x u, y u])
    (i, j) (fun u => a (x u) * b (y u)) (fun u _ => hunit u)
    (by simpa only [star_star, Matrix.cons_val_zero, Matrix.cons_val_one,
      mul_assoc, mul_comm, mul_left_comm] using hcorr)
  let T := (E.selectedExpansion (i, j) k).test l
  let a₀ (n : ℤ) := W.eval k.1.1 (correlationInput n (z - n)) * a n
  let b₀ (n : ℤ) := star (W.eval k.2.1 (correlationInput n (z - n))) * b n
  let F (u : Ω) := (star (W.eval k.1.2 (correlationInput (x u) (y u))) *
    W.eval k.2.2 (correlationInput (y u) (x u))) * a₀ (x u) * b₀ (y u)
  have ha₀ (n : ℤ) : ‖a₀ n‖ ≤ 1 := by
    rw [show a₀ n = W.eval k.1.1 (correlationInput n (z - n)) * a n from rfl, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans (ha n)
  have hb₀ (n : ℤ) : ‖b₀ n‖ ≤ 1 := by
    simp only [b₀, norm_mul, norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans (hb n)
  have hF (u : Ω) : ‖F u‖ ≤ 1 := by
    simp only [F, norm_mul, norm_star]
    refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (hb₀ _)
    refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans (ha₀ _)
    exact (mul_le_of_le_one_left (norm_nonneg _) (W.norm_eval _ _)).trans (W.norm_eval _ _)
  have hT : T.conjugate.ComplexityLE r := ((E.selectedExpansion (i, j) k).complexity l).mono hqr
  have hFcorr : Real.exp (-r) ≤ ‖𝔼 u ∈ S, F u * T.conjugate.eval ![x u, y u]‖ := by
    have hlarge := (Real.exp_le_exp.mpr (neg_le_neg hpr)).trans htransfer
    simpa only [F, a₀, b₀, T, E, RationalFilteredNilmanifold.Niltest.eval_conjugate,
      Matrix.cons_val_zero, Matrix.cons_val_one, star_star,
      mul_assoc, mul_comm, mul_left_comm] using hlarge
  obtain ⟨A, B, hA, hB, hAB⟩ := habsorb T.conjugate hT S hS x y F (fun u _ => hF u) hFcorr
  have hcost : (r + d) ^ d ≤ (p + C) ^ C := by
    simpa [X, Q, R, q, r, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨k.1.2, k.2.2, (fun n => a₀ n * A n), (fun n => b₀ n * B n), ?_, ?_, ?_⟩
  · intro n
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (ha₀ n)).trans (hA n)
  · intro n
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hb₀ n)).trans (hB n)
  · simpa only [F, mul_assoc, mul_comm, mul_left_comm] using
      (Real.exp_le_exp.mpr (neg_le_neg hcost)).trans hAB

end Erdos3

end

end OAI
