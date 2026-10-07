import OAI.Combinatorics.Progressions.Lattices.CommonAffineOrbitEvaluation

namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped TensorProduct

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r) (v : I → L) (w : I → ℕ) (marked : I → Bool)
  (hw : ∀ i, 0 < w i) (hv : ∀ i, v i ∈ F.layer (w i) 1) (t : ℕ)

noncomputable def realMarkedParameterOrbit (b a : Fin t → ℝ) :
    (markedShiftMultidegree F v w marked hw hv t).realification.PolynomialOrbit :=
  (markedShiftMultidegree F v w marked hw hv t).realification.polynomialOrbitOfLog
    (monomial 0 (realMarkedParameterDirection F v w marked t b) +
      monomial (correlationExponent 1 0) (realMarkedParameterDirection F v w marked t a)) (by
        apply (markedShiftMultidegree F v w marked hw hv t).realification.adaptedSubmodule.add_mem
        · apply MultidegreeLieFiltration.monomial_mem_adaptedSubmodule
          change _ ∈ (markedShiftMultidegree F v w marked hw hv t).realification.layer 0
          rw [MultidegreeLieFiltration.zero_eq_top]
          trivial
        · apply MultidegreeLieFiltration.monomial_mem_adaptedSubmodule
          simpa only [correlationExponent_apply] using
            realMarkedParameterDirection_mem_first F v w marked hw hv t a)

theorem realMarkedParameterOrbit_eval (b a : Fin t → ℝ) (h n : ℤ) :
    (markedShiftMultidegree F v w marked hw hv t).realification.polynomialOrbitEval
      (correlationInput h n) (realMarkedParameterOrbit F v w marked hw hv t b a) =
        realMarkedParameterElement F v w marked hw hv t (b + (h : ℝ) • a) := by
  apply NilpotentLieBCHGroup.ext
  change eval (fun i => ((correlationInput h n i : ℤ) : ℚ))
    (monomial 0 (realMarkedParameterDirection F v w marked t b) +
      monomial (correlationExponent 1 0) (realMarkedParameterDirection F v w marked t a)) =
        realMarkedParameterDirection F v w marked t (b + (h : ℝ) • a)
  rw [map_add, eval_correlation_monomial, eval_monomial]
  simp only [Finsupp.prod_zero_index, one_smul, pow_one, pow_zero, mul_one]
  change realMarkedParameterDirection F v w marked t b +
    (h : ℚ) • realMarkedParameterDirection F v w marked t a =
      realMarkedParameterDirection F v w marked t (b + (h : ℝ) • a)
  rw [map_add, map_smul]
  apply congrArg (realMarkedParameterDirection F v w marked t b + ·)
  simpa only [Rat.cast_intCast] using
    (Rat.cast_smul_eq_qsmul ℝ (h : ℚ) (realMarkedParameterDirection F v w marked t a)).symm

end Erdos3

end

end OAI
