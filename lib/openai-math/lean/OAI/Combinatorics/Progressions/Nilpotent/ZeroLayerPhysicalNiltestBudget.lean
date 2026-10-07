import OAI.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateTaggedPairFamily

namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped TensorProduct NNReal

theorem relativePatchComplexity_le_of_rank_lip
    {X : Type*} {s d : ℕ} (A : PolynomialPatch X s d) {p : ℝ}
    (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (hLip : (A.kernel.lip : ℝ) ≤ Real.exp p) :
    relativePatchComplexity A ≤ 2 * p + 1 := by
  have he : 1 ≤ Real.exp p := Real.one_le_exp hp
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hlog : Real.log (1 + (A.kernel.lip : ℝ)) ≤ p + 1 := by
    apply (Real.log_le_iff_le_exp (by positivity : 0 < 1 + (A.kernel.lip : ℝ))).mpr
    calc
      1 + (A.kernel.lip : ℝ) ≤ 1 + Real.exp p := by linarith
      _ ≤ 2 * Real.exp p := by linarith
      _ ≤ Real.exp 1 * Real.exp p := mul_le_mul_of_nonneg_right he1 (Real.exp_nonneg p)
      _ = Real.exp (p + 1) := by rw [← Real.exp_add]; congr 1; ring
  unfold relativePatchComplexity
  linarith

theorem exists_zeroLayer_physical_niltest_of_mass_bounds (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {V X : Type*} {J : Fin 0 → Type*} {d : ℕ}
      (A : PolynomialPatch V s d)
      [Fintype (PolynomialShearIndex A.weight)]
      [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
      [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
      (p : ℝ), 0 ≤ p → (d : ℝ) ≤ p →
      (∀ j, realPolynomialMass (A.form.center j) ≤ p) →
      (A.kernel.lip : ℝ) ≤ Real.exp p →
      ∀ g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
        (fullTaggedVariableWeight (X := X) J),
      relativePatchComplexity (A.ofZeroLayerShearOrbit g) ≤ (p + 2) ^ C ∧
      ∃ T : (polynomialShearNilmanifold A.weight s A.weight_le).Niltest (fun _ : X => 1),
        T.UnitIntervalValued ∧ T.ComplexityLE ((p + 2) ^ C) ∧
        ∀ x, T.eval x = ((A.ofZeroLayerShearOrbit g).value (fun i => (x i : ℝ)) : ℂ) := by
  obtain ⟨C, hC, hbudget⟩ := exists_mass_bounded_patch_niltest_budget s
  refine ⟨C, hC, ?_⟩
  intro V X J d A _ _ _ _ _ p hp hd hform hLip g
  let M : ℝ≥0 := ⟨p, hp⟩
  have hM : ∀ j, realPolynomialMass (A.form.center j) ≤ M := hform
  have hnative := hbudget A M hM p hp hd le_rfl hLip
  obtain ⟨T, _, hunit, hcomplex, heval⟩ :=
    A.exists_zeroLayer_physical_niltest M hM hnative g
  refine ⟨?_, T, hunit, hcomplex, heval⟩
  rw [PolynomialPatch.ofZeroLayerShearOrbit_complexity]
  calc
    relativePatchComplexity A ≤ 2 * p + 1 := relativePatchComplexity_le_of_rank_lip A hp hd hLip
    _ ≤ (p + 2) ^ 2 := by nlinarith [sq_nonneg p]
    _ ≤ (p + 2) ^ C := pow_le_pow_right₀ (by linarith : 1 ≤ p + 2) hC

end Erdos3

end

end OAI
