import OAI.Combinatorics.Progressions.Polynomial.PositivePolynomialVectorOrbit

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open scoped TensorProduct NNReal

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound) (J : Set (σ →₀ ℕ)) [DecidablePred (· ∈ J)]
  (hJ : IsLowerSet J)
  [TopologicalSpace (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
    VectorPolynomial.restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra J hJ))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
    VectorPolynomial.restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra J hJ))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
    VectorPolynomial.restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra J hJ))]
  [T2Space (ℝ ⊗[ℚ] (M.filtration.positivePolynomialAlgebra ⧸
    VectorPolynomial.restrictedOutsideDownsetIdeal M.filtration.positivePolynomialAlgebra J hJ))]
  (p : ℝ) (B : ℕ) (hB : 0 < B) (hstable : M.PositivePolynomialGridStable p B)
  (g : M.filtration.positivePolynomialMultidegree.realification.PolynomialOrbit)
  (ψ : (M.positivePolynomialDownsetModel J hJ p B hB hstable).Space → ℝ)
  (hψ : ∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) (K : ℝ≥0)
  (hLip : letI := (M.positivePolynomialDownsetModel J hJ p B hB hstable).metricSpace;
    LipschitzWith K ψ)

noncomputable def positivePolynomialFactorNiltest :
    (M.positivePolynomialDownsetModel J hJ p B hB hstable).Niltest (fun _ : σ => 1) :=
  (M.positivePolynomialDownsetModel J hJ p B hB hstable).sectionNiltest
    ((M.positivePolynomialDownsetModelMultidegree J hJ p B hB hstable).orbitToOrdinary
      (M.filtration.positivePolynomialDownsetOrbit J hJ g))
    (fun z (_ : Unit) => ψ z) (fun z _ => hψ z) K (fun _ => hLip) (some ())

theorem positivePolynomialFactorNiltest_normBound :
    (M.positivePolynomialFactorNiltest J hJ p B hB hstable g ψ hψ K hLip).normBound = 1 := rfl

theorem positivePolynomialFactorNiltest_unit_interval :
    (M.positivePolynomialFactorNiltest J hJ p B hB hstable g ψ hψ K hLip).UnitIntervalValued :=
  (M.positivePolynomialDownsetModel J hJ p B hB hstable).sectionNiltest_unit_interval _ _ _ _ _ _

theorem positivePolynomialFactorNiltest_eval (x : σ → ℤ) :
    (M.positivePolynomialFactorNiltest J hJ p B hB hstable g ψ hψ K hLip).eval x =
      (ψ (QuotientGroup.mk ((M.filtration.positivePolynomialDownsetQuotient J hJ).realification.polynomialOrbitEval x
        (M.filtration.positivePolynomialDownsetOrbit J hJ g))) : ℂ) := by
  exact congrArg (fun z : (M.positivePolynomialDownsetModel J hJ p B hB hstable).RealGroup =>
    (ψ (QuotientGroup.mk z) : ℂ))
    ((M.positivePolynomialDownsetModelMultidegree J hJ p B hB hstable).orbitToOrdinary_eval
      (M.filtration.positivePolynomialDownsetOrbit J hJ g) x)

theorem positivePolynomialFactorNiltest_complexity {q : ℝ}
    (hE : (M.positivePolynomialDownsetModel J hJ p B hB hstable).GeometryComplexityLE q)
    (hK : (K : ℝ) ≤ Real.exp q) :
    (M.positivePolynomialFactorNiltest J hJ p B hB hstable g ψ hψ K hLip).ComplexityLE (q + 2) := by
  have hq : 0 ≤ q := (Nat.cast_nonneg _).trans hE.1
  have h2 : (4 : ℝ) ≤ Real.exp 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.add_one_le_exp (1 : ℝ)]
  have hlog : Real.log (3 + (K : ℝ)) ≤ q + 2 := by
    apply (Real.log_le_iff_le_exp (by positivity)).mpr
    rw [Real.exp_add]
    nlinarith [Real.one_le_exp hq,
      mul_le_mul_of_nonneg_left h2 (Real.exp_nonneg q)]
  exact (M.positivePolynomialDownsetModel J hJ p B hB hstable).sectionNiltest_complexityLE
    _ _ _ _ _ _ (hE.mono _ (by linarith)) hlog

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
