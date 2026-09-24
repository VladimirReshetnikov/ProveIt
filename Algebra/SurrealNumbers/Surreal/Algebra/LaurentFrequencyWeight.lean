import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Tactic

/-!
# Frequency weights on native Laurent polynomials

Coefficient-wise weights preserve a finite Laurent frequency band. These
finite algebraic facts support the angular derivative and stationary-angle
bound in `trigonometry:cor:chebyshev`.
-/

namespace Surreal.LaurentFrequency

noncomputable section
variable {K : Type*} [CommRing K]

/-- Multiply each coefficient by a weight depending on its integer frequency. -/
def weight (p : LaurentPolynomial K) (w : ℤ → K) : LaurentPolynomial K :=
  AddMonoidAlgebra.ofCoeff (Finsupp.onFinset p.coeff.support (fun k => w k * p.coeff k)
    (fun k hk => Finsupp.mem_support_iff.mpr (fun he => hk (by rw [he, mul_zero]))))

@[simp] theorem coeff_weight (p : LaurentPolynomial K) (w : ℤ → K) (k : ℤ) :
    (weight p w).coeff k = w k * p.coeff k := rfl

/-- Weighting introduces no new frequencies. -/
theorem support_weight_subset (p : LaurentPolynomial K) (w : ℤ → K) :
    (weight p w).coeff.support ⊆ p.coeff.support := by
  intro k hk
  apply Finsupp.mem_support_iff.mpr
  intro he
  have hn := Finsupp.mem_support_iff.mp hk
  rw [coeff_weight, he, mul_zero] at hn
  exact hn rfl

/-- Evaluation of a weighted polynomial can use the original finite support. -/
theorem smeval_weight (p : LaurentPolynomial K) (w : ℤ → K) (z : Kˣ) :
    (weight p w).smeval z = ∑ k ∈ p.coeff.support, (w k * p.coeff k) * (z ^ k).val := by
  classical
  unfold LaurentPolynomial.smeval
  simp only [Finsupp.sum, smul_eq_mul]
  calc
    _ = ∑ k ∈ p.coeff.support, (weight p w).coeff k * (z ^ k).val := by
      apply Finset.sum_subset (support_weight_subset p w)
      intro k _ hk
      rw [Finsupp.notMem_support_iff.mp hk, zero_mul]
    _ = _ := by simp only [coeff_weight]

/-- A Laurent polynomial is constant exactly when every nonzero frequency vanishes. -/
theorem eq_constant_iff (p : LaurentPolynomial K) :
    p = LaurentPolynomial.C (p.coeff 0) ↔ ∀ k : ℤ, k ≠ 0 → p.coeff k = 0 := by
  classical
  constructor
  · intro he k hk
    have hc := congrArg (fun q : LaurentPolynomial K => q.coeff k) he
    simpa [LaurentPolynomial.C_apply, hk] using hc
  · intro h
    apply LaurentPolynomial.ext
    intro k
    by_cases hk : k = 0
    · subst k
      simp [LaurentPolynomial.C_apply]
    · simp [LaurentPolynomial.C_apply, hk, h k hk]

end
end Surreal.LaurentFrequency
