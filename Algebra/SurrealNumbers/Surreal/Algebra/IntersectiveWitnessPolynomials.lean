import Surreal.Algebra.IntersectiveDetector
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Explicit polynomial witnesses for the intersective detector

The displayed witnesses preceding `odg:def:prop:support` are polynomials
of degrees one and five in the input. Their factorization gives a
certificate in every commutative coefficient-field algebra, including
algebras with zero divisors.
-/

namespace Surreal.IntersectivePolynomial

open Polynomial

noncomputable section

variable {K H O : Type*} [Field K] [CommRing H] [Algebra K H] [CommRing O]

/-- The affine polynomial producing the witness t. -/
def witnessTPolynomial (r α : K) : K[X] := C r + C α * X

/-- The degree-five quotient of Lambda by its factor T-r when r²=13. -/
def rootQuotientPolynomial (r : K) : K[X] :=
  (X + C r) * (X ^ 2 - C 17) * (X ^ 2 - C 221)

/-- The polynomial producing the witness s from the original input a. -/
def witnessSPolynomial (r α : K) : K[X] :=
  C α * (rootQuotientPolynomial r).comp (witnessTPolynomial r α)

theorem witnessTPolynomial_natDegree (r α : K) (hα : α ≠ 0) :
    (witnessTPolynomial r α).natDegree = 1 := by
  rw [witnessTPolynomial, add_comm, natDegree_add_C, natDegree_C_mul_X α hα]

theorem rootQuotientPolynomial_natDegree (r : K) :
    (rootQuotientPolynomial r).natDegree = 5 := by
  have h₁ := monic_X_add_C r
  have h₂ := monic_X_pow_sub_C (17 : K) (by decide : 2 ≠ 0)
  have h₃ := monic_X_pow_sub_C (221 : K) (by decide : 2 ≠ 0)
  rw [rootQuotientPolynomial, natDegree_mul (h₁.mul h₂).ne_zero h₃.ne_zero,
    natDegree_mul h₁.ne_zero h₂.ne_zero, natDegree_X_add_C,
    natDegree_X_pow_sub_C, natDegree_X_pow_sub_C]

theorem witnessSPolynomial_natDegree (r α : K) (hα : α ≠ 0) :
    (witnessSPolynomial r α).natDegree = 5 := by
  rw [witnessSPolynomial, natDegree_C_mul hα, natDegree_comp,
    rootQuotientPolynomial_natDegree, witnessTPolynomial_natDegree r α hα]

/-- The printed quotient really factors Lambda at the chosen square root. -/
theorem rootQuotientPolynomial_factor (r : K) (hr : r ^ 2 = 13) :
    polynomial.map (Int.castRingHom K) = (X - C r) * rootQuotientPolynomial r := by
  have hr' : (C r : K[X]) ^ 2 = 13 := by rw [← map_pow, hr, map_ofNat]
  simp [polynomial, rootQuotientPolynomial]
  simp only [map_ofNat]
  rw [← hr']
  ring

/-- Evaluation of the affine polynomial is the augmentation construction's t. -/
theorem witnessTPolynomial_eval (r α : K) (a : H) :
    (witnessTPolynomial r α).eval₂ (algebraMap K H) a =
      AugmentationRootDetector.affineWitness r α a := by
  simp [witnessTPolynomial, AugmentationRootDetector.affineWitness]

/-- Evaluation of the degree-five polynomial is the augmentation construction's s. -/
theorem witnessSPolynomial_eval (r α : K) (a : H) :
    (witnessSPolynomial r α).eval₂ (algebraMap K H) a =
      AugmentationRootDetector.quotientWitness (rootQuotientPolynomial r) α
        (AugmentationRootDetector.affineWitness r α a) := by
  simp [witnessSPolynomial, AugmentationRootDetector.quotientWitness,
    eval₂_comp, witnessTPolynomial_eval]

/-- The second witness is the literal factored expression printed in the manuscript. -/
theorem witnessSPolynomial_eval_explicit (r α : K) (a : H) :
    let t := AugmentationRootDetector.affineWitness r α a
    (witnessSPolynomial r α).eval₂ (algebraMap K H) a =
      algebraMap K H α * (2 * algebraMap K H r + algebraMap K H α * a) *
        (t ^ 2 - 17) * (t ^ 2 - 221) := by
  simp only [witnessSPolynomial_eval, AugmentationRootDetector.quotientWitness,
    rootQuotientPolynomial, eval₂_mul, eval₂_add, eval₂_X, eval₂_C, eval₂_sub,
    eval₂_pow, map_ofNat, eval₂_ofNat, AugmentationRootDetector.affineWitness]
  ring

/-- The two explicit polynomials satisfy the detector equation. -/
theorem witnessPolynomials_identity (r α : K) (hr : r ^ 2 = 13) (a : H) :
    a * (witnessSPolynomial r α).eval₂ (algebraMap K H) a =
      value ((witnessTPolynomial r α).eval₂ (algebraMap K H) a) := by
  rw [witnessSPolynomial_eval, witnessTPolynomial_eval]
  have h := AugmentationRootDetector.witness_identity
    (polynomial.map (Int.castRingHom K)) (rootQuotientPolynomial r) r α a
    (rootQuotientPolynomial_factor r hr)
  simpa only [eval₂_mapped_polynomial] using h

/-- Root exclusion in the ordinary coefficient ring forces a nonzero affine slope. -/
theorem witness_slope_ne_zero (i : O →+* K) (hi : Function.Injective i)
    (hno : ∀ b : O, value b ≠ 0) (r : K) (hr : r ^ 2 = 13)
    (b c : O) (hc : i c ≠ 0) : (i b - r) / i c ≠ 0 := by
  apply div_ne_zero _ hc
  intro hz
  have hb : value (i b) = 0 := by simp [value, sub_eq_zero.mp hz, hr]
  exact hno b (hi (by simpa only [map_value, map_zero] using hb))

/-- The witnesses have the prescribed ordinary constant coefficients and satisfy the equation. -/
theorem witnessPolynomials_augmentation (ε : H →ₐ[K] K) (i : O →+* K)
    (r : K) (hr : r ^ 2 = 13) (b c d : O) (hc : i c ≠ 0)
    (hbd : value b = c * d) (a : H) (ha : ε a = i c) :
    let α := (i b - r) / i c
    let t := (witnessTPolynomial r α).eval₂ (algebraMap K H) a
    let s := (witnessSPolynomial r α).eval₂ (algebraMap K H) a
    ε t = i b ∧ ε s = i d ∧ a * s = value t := by
  dsimp only
  have ht : ε ((witnessTPolynomial r ((i b - r) / i c)).eval₂ (algebraMap K H) a) = i b := by
    rw [witnessTPolynomial_eval]
    exact AugmentationRootDetector.affineWitness_augmentation ε r (i b) (i c) hc a ha
  have he := witnessPolynomials_identity r ((i b - r) / i c) hr a
  refine ⟨ht, ?_, he⟩
  have hm := congrArg ε.toRingHom he
  rw [map_mul, map_value] at hm
  change ε a * ε ((witnessSPolynomial r ((i b - r) / i c)).eval₂ (algebraMap K H) a) =
    value (ε ((witnessTPolynomial r ((i b - r) / i c)).eval₂ (algebraMap K H) a)) at hm
  rw [ha, ht, ← map_value, hbd, map_mul] at hm
  exact mul_left_cancel₀ hc hm

end
end Surreal.IntersectivePolynomial
