import Mathlib.Algebra.BigOperators.Pi
import OAI.Combinatorics.Progressions.Polynomial.MixedWeightedPolynomialRename

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {σ τ : Type*} [Fintype τ]

def integerAffineMap (A : σ → τ → ℤ) (b : σ → ℤ) (x : τ → ℤ) (i : σ) : ℤ :=
  b i + ∑ j, A i j * x j

noncomputable def integerAffinePolynomial (A : σ → τ → ℤ) (b : σ → ℤ) (i : σ) :
    MvPolynomial τ ℚ :=
  MvPolynomial.C (b i : ℚ) + ∑ j, MvPolynomial.C (A i j : ℚ) * MvPolynomial.X j

theorem integerAffinePolynomial_support (A : σ → τ → ℤ) (b : σ → ℤ) (i : σ) :
    integerAffinePolynomial A b i ∈ weightedSupportLE (fun _ : τ => 1) 1 := by
  apply Submodule.add_mem
  · exact weightedSupportLE_C _ 1 (b i : ℚ)
  · apply Submodule.sum_mem
    intro j _
    have hx : (MvPolynomial.X j : MvPolynomial τ ℚ) ∈ weightedSupportLE (fun _ : τ => 1) 1 := by
      simpa only [MvPolynomial.X, Finsupp.weight_single, smul_eq_mul, mul_one] using
        weightedSupportLE_monomial (fun _ : τ => 1) (Finsupp.single j 1) (1 : ℚ)
    simpa only [zero_add] using weightedSupportLE_mul (weightedSupportLE_C _ 0 (A i j : ℚ)) hx

theorem integerAffinePolynomial_eval (A : σ → τ → ℤ) (b : σ → ℤ) (x : τ → ℤ) (i : σ) :
    MvPolynomial.aeval (fun j => (x j : ℚ)) (integerAffinePolynomial A b i) =
      (integerAffineMap A b x i : ℚ) := by
  simp [integerAffinePolynomial, integerAffineMap]

theorem integerLinearForm_eq_sum [DecidableEq τ] (f : (τ → ℤ) →+ ℤ) (x : τ → ℤ) :
    f x = ∑ j, f (Pi.single j 1) * x j := by
  conv_lhs => rw [pi_eq_sum_univ' x]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_zsmul]
  change x j * f (Pi.single j 1) = f (Pi.single j 1) * x j
  exact mul_comm _ _

end Erdos3

end

end OAI
