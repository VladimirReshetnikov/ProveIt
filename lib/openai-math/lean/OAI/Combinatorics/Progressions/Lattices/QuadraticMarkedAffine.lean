import OAI.Combinatorics.Progressions.Estimates.CoveredInducedCorrelationFamily

namespace OAI

section

namespace Erdos3.QuadraticMarked

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

noncomputable def seedVector (a : ℝ) : ℝ ⊗[ℚ] Seed := a ⊗ₜ[ℚ] generators 0

theorem seedVector_mem (a : ℝ) :
    seedVector a ∈ (markedLieSpan generators weights marked 1 1 1).baseChange ℝ := by
  apply Submodule.tmul_mem_baseChange_of_mem
  simpa only [weights, marked, Bool.true_eq, ite_true] using
    markedLieSpan_leaf generators weights marked (0 : Fin 1)

noncomputable def affineCoefficient (t : ℕ) (a : ℝ) (b : Fin t → ℝ) :
    (markedPolynomialLayer (σ := Fin t) generators weights marked 1 0 1).baseChange ℝ :=
  ⟨realAffinePolynomial (seedVector a) (fun i => seedVector (b i)),
    realAffinePolynomial_mem_marked generators weights marked
      (Submodule.baseChange_mono ℝ
        (markedLieSpan_antitone generators weights marked le_rfl (by omega) le_rfl)
        (seedVector_mem a)) (fun i => seedVector_mem (b i))⟩

noncomputable def sourceLift (t : ℕ) (a : ℝ) (b : Fin t → ℝ) :
    ℝ ⊗[ℚ] markedShiftSubalgebra filtration generators weights marked t :=
  realMarkedPolynomialLift filtration generators weights marked weight_pos generator_mem t 1 0 1
    (affineCoefficient t a b)

noncomputable def projectedLift (t : ℕ) (a : ℝ) (b : Fin t → ℝ) : ℝ ⊗[ℚ] Algebra t :=
  (lieQuotientMap (markedShiftSecondIdeal filtration generators weights marked t)).toLinearMap.baseChange ℝ
    (sourceLift t a b)

theorem sourceLift_eval (t : ℕ) (a : ℝ) (b : Fin t → ℝ) (u : Fin t → ℚ) :
    (markedShiftEval filtration generators weights marked t u).baseChange ℝ (sourceLift t a b) =
      seedVector a + ∑ i, (u i : ℝ) • seedVector (b i) := by
  apply (realMarkedPolynomialLift_eval filtration generators weights marked weight_pos generator_mem
    t 1 0 1 (affineCoefficient t a b) u).trans
  simpa only [affineCoefficient, ← Rat.cast_smul_eq_qsmul ℝ] using
    realAffinePolynomial_eval (seedVector a) (fun i => seedVector (b i)) u

theorem projectedLift_mem (t : ℕ) (a : ℝ) (b : Fin t → ℝ) :
    projectedLift t a b ∈ (multidegree t).realification.layer (correlationInput 0 1) :=
  realMarkedPolynomialLift_quotient_mem filtration generators weights marked weight_pos generator_mem
    t 1 0 1 (affineCoefficient t a b)

theorem projectedLift_pure (t : ℕ) (a : ℝ) (b : Fin t → ℝ) :
    projectedLift t a b ∈
      (markedQuotientPolynomialAlgebra filtration generators weights marked t).toSubmodule.baseChange ℝ := by
  change projectedLift t a b ∈
    (LinearMap.ker (markedQuotientPhase filtration generators weights marked t).toLinearMap).baseChange ℝ
  rw [realification_ker, LinearMap.mem_ker]
  change (markedQuotientPhase filtration generators weights marked t).toLinearMap.baseChange ℝ
    ((lieQuotientMap (markedShiftSecondIdeal filtration generators weights marked t)).toLinearMap.baseChange ℝ
      (sourceLift t a b)) = 0
  rw [markedQuotientPhase_real_map]
  exact realMarkedPolynomialLift_phase filtration generators weights marked weight_pos generator_mem
    t 1 0 1 (by decide) (affineCoefficient t a b)

theorem projectedLift_phase (t m : ℕ) (a : ℝ) (b : Fin t → ℝ) :
    torusPhaseLinear (phase t m) (projectedLift t a b) = 0 :=
  normalizedMarkedPhase_real_pure filtration generators weights marked t m _
    (projectedLift_pure t a b)

noncomputable def seedCoordinate (η : RationalTorus.BottomQuotient 1 →ₗ[ℚ] ℚ) :
    (ℝ ⊗[ℚ] Seed) →ₗ[ℝ] ℝ :=
  (realifyFunctional η).comp ((lieQuotientMap (⊥ : LieIdeal ℚ Seed)).toLinearMap.baseChange ℝ)

theorem seedCoordinate_seedVector (η : RationalTorus.BottomQuotient 1 →ₗ[ℚ] ℚ)
    (hη : ∀ x : Seed, η (lieQuotientMap (⊥ : LieIdeal ℚ Seed) x) = x 0) (a : ℝ) :
    seedCoordinate η (seedVector a) = a := by
  have he : generators (0 : Fin 1) (0 : Fin 1) = 1 := by
    change (Pi.basisFun ℚ (Fin 1)) 0 0 = 1
    simp
  simp only [seedCoordinate, seedVector, LinearMap.comp_apply, LinearMap.baseChange_tmul,
    realifyFunctional_tmul]
  change a * ((η (lieQuotientMap (⊥ : LieIdeal ℚ Seed) (generators 0))) : ℝ) = a
  rw [hη, he, Rat.cast_one, mul_one]

theorem sourceLift_shift_coordinate (η : RationalTorus.BottomQuotient 1 →ₗ[ℚ] ℚ)
    (hη : ∀ x : Seed, η (lieQuotientMap (⊥ : LieIdeal ℚ Seed) x) = x 0)
    (t : ℕ) (a : ℝ) (b u : Fin t → ℝ) :
    seedCoordinate η ((markedShiftEval filtration generators weights marked t 0).baseChange ℝ
      (realMarkedAffineShift filtration generators weights marked weight_pos generator_mem t u
        (sourceLift t a b))) = a + ∑ i, u i * b i := by
  rw [realMarkedAffineShift_eval_affine filtration generators weights marked weight_pos generator_mem
    t u (sourceLift t a b) (seedVector a) (fun i => seedVector (b i)) (sourceLift_eval t a b)]
  simp only [map_add, map_sum, map_smul, seedCoordinate_seedVector η hη, smul_eq_mul]

theorem shiftedLift_coordinate (η : RationalTorus.BottomQuotient 1 →ₗ[ℚ] ℚ)
    (hη : ∀ x : Seed, η (lieQuotientMap (⊥ : LieIdeal ℚ Seed) x) = x 0)
    (t : ℕ) (a : ℝ) (b u : Fin t → ℝ) :
    realifyFunctional η ((evaluation t).baseChange ℝ
      ((lieQuotientMap (markedShiftSecondIdeal filtration generators weights marked t)).toLinearMap.baseChange ℝ
        (realMarkedAffineShift filtration generators weights marked weight_pos generator_mem t u
          (sourceLift t a b)))) = a + ∑ i, u i * b i := by
  rw [evaluation, markedBaseEvaluation_real_map]
  exact sourceLift_shift_coordinate η hη t a b u

noncomputable def pureOrbit (t : ℕ) (a : ℝ) (b : Fin t → ℝ) :
    (multidegree t).realification.PolynomialOrbit :=
  (multidegree t).realification.polynomialOrbitOfLog
    (monomial (correlationExponent 0 1) (projectedLift t a b)) (by
      apply (multidegree t).realification.monomial_mem_adaptedSubmodule
      simpa only [correlationExponent_apply] using projectedLift_mem t a b)

theorem pureOrbit_eval (t : ℕ) (a : ℝ) (b : Fin t → ℝ) (h n : ℤ) :
    ((multidegree t).realification.polynomialOrbitEval (correlationInput h n) (pureOrbit t a b)).coord =
      (n : ℝ) • projectedLift t a b := by
  change eval (fun i => ((correlationInput h n i : ℤ) : ℚ))
    (monomial (correlationExponent 0 1) (projectedLift t a b)) = _
  rw [eval_correlation_monomial]
  change ((h : ℚ) ^ 0 * (n : ℚ) ^ 1) • projectedLift t a b = _
  rw [pow_zero, pow_one, one_mul]
  simpa only [Rat.cast_intCast] using
    (Rat.cast_smul_eq_qsmul ℝ (n : ℚ) (projectedLift t a b)).symm

theorem pureOrbit_phase (t m : ℕ) (a : ℝ) (b : Fin t → ℝ) (h n : ℤ) :
    torusPhaseLinear (phase t m)
      ((multidegree t).realification.polynomialOrbitEval (correlationInput h n) (pureOrbit t a b)).coord = 0 := by
  rw [pureOrbit_eval, map_smul, projectedLift_phase, smul_zero]

theorem pureOrbit_at_zero (t : ℕ) (a : ℝ) (b : Fin t → ℝ) (h : ℤ) :
    (multidegree t).realification.polynomialOrbitEval (correlationInput h 0) (pureOrbit t a b) = 1 := by
  apply NilpotentLieBCHGroup.ext
  rw [pureOrbit_eval]
  simp

end Erdos3.QuadraticMarked

end

end OAI
