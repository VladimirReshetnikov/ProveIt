import Surreal.Surcomplex.AngularLaurentEvaluation

/-!
# The sine family as native Laurent polynomials

The sharpness witness for `trigonometry:thm:polyroots` is `sin(nθ)`.
Its cleared polynomial is a nonzero scalar times `X^(2n)-1`.
-/

universe u
namespace Surreal.Surcomplex.SineLaurent

open Foundations Polynomial

noncomputable section

/-- The positive-frequency coefficient `1/(2i)`. -/
def amplitude : Surcomplex.{u} := -I / 2

/-- The two-frequency Laurent presentation of `sin(nθ)`. -/
def fourier (n : ℕ) : LaurentPolynomial Surcomplex.{u} :=
  LaurentPolynomial.C amplitude * LaurentPolynomial.T n +
    LaurentPolynomial.C (-amplitude) * LaurentPolynomial.T (-(n : ℤ))

theorem amplitude_ne_zero : (amplitude : Surcomplex.{u}) ≠ 0 := by
  apply div_ne_zero _ (by norm_num)
  apply neg_ne_zero.mpr
  intro h
  have hi := congrArg (fun z : Surcomplex.{u} => z.im) h
  simp at hi

/-- The exact two Fourier coefficients, including the cancellation when `n=0`. -/
theorem coeff_fourier (n : ℕ) (k : ℤ) :
    (fourier n : LaurentPolynomial Surcomplex.{u}).coeff k =
      (if k = n then amplitude else 0) + (if k = -(n : ℤ) then -amplitude else 0) := by
  classical
  simp only [fourier, AddMonoidAlgebra.coeff_add, ← LaurentPolynomial.single_eq_C_mul_T,
    AddMonoidAlgebra.coeff_single, Finsupp.add_apply, Finsupp.single_apply]
  simp only [eq_comm]

/-- Every frequency of the sine witness lies between `-n` and `n`. -/
theorem frequency_bound (n : ℕ) :
    ∀ k ∈ (fourier n : LaurentPolynomial Surcomplex.{u}).coeff.support, k.natAbs ≤ n := by
  classical
  intro k hk
  have hc := Finsupp.mem_support_iff.mp hk
  rw [coeff_fourier] at hc
  split_ifs at hc <;> simp_all

/-- At positive frequency the Laurent polynomial is nonzero. -/
theorem fourier_ne_zero (n : ℕ) (hn : 0 < n) :
    (fourier n : LaurentPolynomial Surcomplex.{u}) ≠ 0 := by
  intro h
  have he := congrArg (fun p : LaurentPolynomial Surcomplex.{u} => p.coeff (n : ℤ)) h
  rw [coeff_fourier, if_pos rfl, if_neg (by omega), add_zero] at he
  exact amplitude_ne_zero he

/-- The Laurent presentation evaluates to the original finite-angle sine family. -/
theorem evaluate (n : ℕ) (θ : SignSequence.FiniteElement.{u}) :
    trigonometricPolynomial (fourier n) θ = ofReal (finiteSin (n • θ)) := by
  simp only [trigonometricPolynomial, fourier, LaurentPolynomial.smeval_add,
    LaurentPolynomial.smeval_C_mul_T_n, smul_eq_mul, Units.val_zpow_eq_zpow_val, phaseUnit_val,
    ← finitePhase_zsmul, neg_smul, natCast_zsmul, finitePhase_neg]
  rw [← finitePhase_neg, finitePhase_eq_cos_add_sin_mul_I,
    finitePhase_eq_cos_add_sin_mul_I, finiteCos_neg, finiteSin_neg, map_neg]
  unfold amplitude
  linear_combination -ofReal (finiteSin (n • θ)) * I_sq

/-- The cleared polynomial is exactly the scalar multiple of `X^(2n)-1`. -/
theorem cleared_polynomial (n : ℕ) :
    LaurentAlgebraization.polynomial n (fourier n : LaurentPolynomial Surcomplex.{u}).coeff =
      Polynomial.C amplitude * (Polynomial.X ^ (2 * n) - 1) := by
  classical
  apply Polynomial.ext
  intro j
  rw [LaurentAlgebraization.coeff_polynomial, coeff_C_mul, coeff_sub, coeff_X_pow, coeff_one]
  by_cases hj : j ≤ 2 * n
  · rw [if_pos hj, coeff_fourier]
    have hhi : (j : ℤ) - n = n ↔ j = 2 * n := by omega
    have hlo : (j : ℤ) - n = -(n : ℤ) ↔ j = 0 := by omega
    simp only [hhi, hlo]
    split_ifs <;> ring
  · rw [if_neg hj, if_neg (by omega), if_neg (by omega)]
    ring

/-- Every root of the cleared sine polynomial is simple in characteristic zero. -/
theorem multiplicity_one (n : ℕ) (hn : 0 < n) (z : Surcomplex.{u}) (hz : z ≠ 0)
    (hr : (LaurentAlgebraization.polynomial n (fourier n).coeff).IsRoot z) :
    (LaurentAlgebraization.polynomial n (fourier n).coeff).rootMultiplicity z = 1 := by
  let P := LaurentAlgebraization.polynomial n (fourier n : LaurentPolynomial Surcomplex.{u}).coeff
  have hp : P ≠ 0 := by
    dsimp only [P]
    rw [cleared_polynomial]
    apply mul_ne_zero (by simpa only [ne_eq, Polynomial.C_eq_zero] using amplitude_ne_zero)
    intro he
    have hc := congrArg (fun Q : Polynomial Surcomplex.{u} => Q.coeff (2 * n)) he
    simp [coeff_sub, coeff_one, show 2 * n ≠ 0 by omega] at hc
  have hd : P.derivative.eval z ≠ 0 := by
    dsimp only [P]
    rw [cleared_polynomial]
    simp only [derivative_C_mul, derivative_sub, derivative_X_pow, derivative_one, sub_zero,
      eval_mul, eval_C, eval_pow, eval_X]
    exact mul_ne_zero amplitude_ne_zero
      (mul_ne_zero (by exact_mod_cast (by omega : 2 * n ≠ 0)) (pow_ne_zero _ hz))
  have hpos := (Polynomial.rootMultiplicity_pos hp).mpr hr
  have hnot : ¬ 1 < P.rootMultiplicity z := by
    rw [Polynomial.one_lt_rootMultiplicity_iff_isRoot hp]
    exact fun h => hd h.2
  change P.rootMultiplicity z = 1
  omega

end
end Surreal.Surcomplex.SineLaurent
