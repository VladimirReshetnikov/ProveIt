/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Estimates.SquarefreeSplitCount
import OAI.Combinatorics.Progressions.Geometry.RealSquarefreeCoordinates

namespace OAI

section

namespace Erdos3

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]

noncomputable def blockMonomial (π : ι → σ) (a : σ → ℕ) : L →ₗ[ℚ] SquarefreePolynomial ι L := by
  classical
  exact squarefreePolynomialEquiv.symm.toLinearMap.comp
    (LinearMap.pi fun c : SquarefreeIndex ι => if blockDegree π c.val = a then LinearMap.id else 0)

theorem blockMonomial_coefficient [DecidableEq σ] (π : ι → σ) (a : σ → ℕ)
    (x : L) (c : SquarefreeIndex ι) :
    squarefreePolynomialEquiv (blockMonomial π a x) c =
      if blockDegree π c.val = a then x else 0 := by
  classical
  simp only [blockMonomial, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, LinearMap.pi_apply]
  split_ifs <;> rfl

noncomputable def factorialBlockMonomial (π : ι → σ) (a : σ → ℕ) :
    L →ₗ[ℚ] SquarefreePolynomial ι L :=
  (multidegreeFactorial a : ℚ) • blockMonomial π a

theorem factorialBlockMonomial_coefficient [DecidableEq σ] (π : ι → σ) (a : σ → ℕ)
    (x : L) (c : SquarefreeIndex ι) :
    squarefreePolynomialEquiv (factorialBlockMonomial π a x) c =
      if blockDegree π c.val = a then (multidegreeFactorial a : ℚ) • x else 0 := by
  simp only [factorialBlockMonomial, LinearMap.smul_apply, map_smul, Pi.smul_apply,
    blockMonomial_coefficient, smul_ite, smul_zero]

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]

noncomputable def blockPolynomialEval (π : ι → σ) (p : VectorPolynomial σ ℚ L)
    (x : σ → ℚ) : SquarefreePolynomial ι L :=
  ∑ a ∈ (coefficients p).support,
    (a.prod fun i n => x i ^ n) • factorialBlockMonomial π (fun i => a i) (coefficients p a)

theorem blockPolynomialEval_coefficient (π : ι → σ) (p : VectorPolynomial σ ℚ L)
    (x : σ → ℚ) (c : SquarefreeIndex ι) :
    squarefreePolynomialEquiv (blockPolynomialEval π p x) c =
      ((blockExponent π c.val).prod fun i n => x i ^ n) •
        ((multidegreeFactorial (blockDegree π c.val) : ℚ) •
          coefficients p (blockExponent π c.val)) := by
  classical
  simp only [blockPolynomialEval, map_sum, Finset.sum_apply, map_smul, Pi.smul_apply]
  rw [Finset.sum_eq_single (blockExponent π c.val)]
  · simp only [factorialBlockMonomial_coefficient, blockExponent_apply, ite_true]
  · intro a _ ha
    rw [factorialBlockMonomial_coefficient]
    have hca : blockDegree π c.val ≠ (fun i => a i) := by
      intro h
      apply ha
      ext i
      exact (congrFun h i).symm
    rw [ite_eq_right hca, smul_zero]
  · intro hc
    rw [Finsupp.notMem_support_iff.mp hc, map_zero, map_zero, Pi.zero_apply, smul_zero]

end Erdos3

end

section

namespace Erdos3

open VectorPolynomial
open scoped TensorProduct BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]

theorem realFactorialBlockMonomial_coefficient [DecidableEq σ] (π : ι → σ) (a : σ → ℕ)
    (x : ℝ ⊗[ℚ] L) (c : SquarefreeIndex ι) :
    realSquarefreePolynomialEquiv ((factorialBlockMonomial π a).baseChange ℝ x) c =
      if blockDegree π c.val = a then (multidegreeFactorial a : ℚ) • x else 0 := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    rw [LinearMap.baseChange_tmul, realSquarefreePolynomialEquiv_tmul,
      factorialBlockMonomial_coefficient]
    by_cases h : blockDegree π c.val = a
    · simp only [h, ite_true, TensorProduct.tmul_smul]
    · simp only [h, ite_false, TensorProduct.tmul_zero]
  | add x y hx hy =>
    rw [map_add, map_add, Pi.add_apply, hx, hy]
    split_ifs <;> simp only [smul_add, add_zero]

noncomputable def realBlockPolynomialEval (π : ι → σ) (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (x : σ → ℚ) : ℝ ⊗[ℚ] SquarefreePolynomial ι L :=
  ∑ a ∈ (coefficients p).support,
    (a.prod fun i n => x i ^ n) • (factorialBlockMonomial π (fun i => a i)).baseChange ℝ (coefficients p a)

theorem realBlockPolynomialEval_coefficient (π : ι → σ) (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (x : σ → ℚ) (c : SquarefreeIndex ι) :
    realSquarefreePolynomialEquiv (realBlockPolynomialEval π p x) c =
      ((blockExponent π c.val).prod fun i n => x i ^ n) •
        ((multidegreeFactorial (blockDegree π c.val) : ℚ) •
          coefficients p (blockExponent π c.val)) := by
  classical
  simp only [realBlockPolynomialEval, map_sum, Finset.sum_apply, map_rat_smul, Pi.smul_apply]
  rw [Finset.sum_eq_single (blockExponent π c.val)]
  · simp only [realFactorialBlockMonomial_coefficient, blockExponent_apply, ite_true]
  · intro a _ ha
    rw [realFactorialBlockMonomial_coefficient]
    have hca : blockDegree π c.val ≠ (fun i => a i) := by
      intro h
      apply ha
      ext i
      exact (congrFun h i).symm
    rw [ite_eq_right hca, smul_zero]
  · intro hc
    rw [Finsupp.notMem_support_iff.mp hc, map_zero, map_zero, Pi.zero_apply, smul_zero]

end Erdos3

end

end OAI
