import Surreal.Algebra.LaurentCayleyDegree
import Surreal.Surcomplex.CayleySpectralFactor
import Surreal.Surcomplex.NonnegativePolynomialFactorization
import Surreal.Surcomplex.TrigonometricPolynomialCayley

/-!
# Fejér–Riesz factorization on the affine Cayley chart

The positive cleared polynomial in `trigonometry:eq:cayleypositive` and
the construction in `trigonometry:eq:fejerconstruction`. Positivity is
assumed at all actual finite surreal angles, including infinitesimal ones.
-/

universe u
namespace Surreal.Surcomplex.FejerRiesz

open Foundations Polynomial

noncomputable section

/-- The actual unit represented by the affine Cayley chart. -/
def cayleyUnit (t : SignSequence.{u}) : Surcomplex.{u}ˣ :=
  Unitary.toUnits (⟨cayley t, (mem_unitCircle_iff _).mpr (modulus_cayley t)⟩ : UnitCircle)

@[simp] theorem cayleyUnit_val (t : SignSequence.{u}) : (cayleyUnit t).val = cayley t := rfl

/-- The real polynomial obtained by clearing a degree-`N` Fourier sum in the Cayley chart. -/
def numerator (p : LaurentPolynomial Surcomplex.{u}) (N : ℕ) : Polynomial SignSequence.{u} :=
  Complexify.realPartPolynomial (LaurentCayley.numerator p 1 I N)

/-- The cleared real polynomial has degree at most `2N`. -/
theorem natDegree_numerator_le (p : LaurentPolynomial Surcomplex.{u}) (N : ℕ)
    (hN : ∀ k ∈ p.coeff.support, k.natAbs ≤ N) : (numerator p N).natDegree ≤ 2 * N :=
  (Complexify.natDegree_realPartPolynomial_le _).trans
    (LaurentCayley.natDegree_numerator_le p 1 I N hN)

/-- Exact evaluation of the positive-denominator pullback, for every surreal parameter. -/
theorem eval_numerator (p : LaurentPolynomial Surcomplex.{u}) (N : ℕ)
    (hN : ∀ k ∈ p.coeff.support, k.natAbs ≤ N) (t : SignSequence.{u}) :
    (numerator p N).eval t = (1 + t ^ 2) ^ N * (p.smeval (cayleyUnit t)).re := by
  have hp : 1 + I * ofReal t ≠ 0 := by
    intro h
    have hr := congrArg (fun z : Surcomplex.{u} => z.re) h
    norm_num [QuadraticAlgebra.re_one] at hr
  have hm : 1 - I * ofReal t ≠ 0 := by
    intro h
    have hr := congrArg (fun z : Surcomplex.{u} => z.re) h
    norm_num [QuadraticAlgebra.re_one] at hr
  have hu : Units.mk0 ((1 + I * ofReal t) / (1 - I * ofReal t)) (div_ne_zero hp hm) =
      cayleyUnit t := by
    apply Units.ext
    simp only [Units.val_mk0, cayleyUnit_val, cayley_eq_fraction]
  have hd : (LaurentCayley.denominator I N).eval (ofReal t) = ofReal ((1 + t ^ 2) ^ N) := by
    simp only [LaurentCayley.denominator, eval_pow, eval_mul, eval_add, eval_sub,
      eval_one, eval_C, eval_X, map_pow, map_add, map_one]
    congr 1
    linear_combination -(ofReal t) ^ 2 * I_sq.{u}
  rw [numerator, Complexify.eval_realPartPolynomial]
  change (Polynomial.eval (ofReal t) (LaurentCayley.numerator p 1 I N)).re = _
  rw [LaurentCayley.eval_numerator p 1 I (ofReal t) N hN hp hm, one_mul, hu, hd]
  simp only [Complexify.mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]

/-- Testing all finite angles guarantees nonnegativity of the cleared polynomial on all surreals. -/
theorem numerator_nonnegative (p : LaurentPolynomial Surcomplex.{u})
    (hp : ∀ θ : SignSequence.FiniteElement.{u}, 0 ≤ (trigonometricPolynomial p θ).re)
    (N : ℕ) (hN : ∀ k ∈ p.coeff.support, k.natAbs ≤ N) (t : SignSequence.{u}) :
    0 ≤ (numerator p N).eval t := by
  obtain ⟨θ, hθ⟩ := exists_finitePhase_eq_of_modulus_eq_one (cayley t) (modulus_cayley t)
  have hu : phaseUnit θ = cayleyUnit t := Units.ext hθ
  have hpos : 0 ≤ (p.smeval (cayleyUnit t)).re := by
    simpa only [trigonometricPolynomial, hu] using hp θ
  rw [eval_numerator p N hN t]
  exact mul_nonneg (pow_nonneg (by positivity) _) hpos

/-- A polynomial of degree at most `N` realizes the squared modulus on the entire affine chart. -/
theorem exists_factor_on_cayley (p : LaurentPolynomial Surcomplex.{u})
    (hp : ∀ θ : SignSequence.FiniteElement.{u}, 0 ≤ (trigonometricPolynomial p θ).re)
    (N : ℕ) (hN : ∀ k ∈ p.coeff.support, k.natAbs ≤ N) :
    ∃ Q : Polynomial Surcomplex.{u}, Q.natDegree ≤ N ∧
      ∀ t : SignSequence.{u}, (p.smeval (cayleyUnit t)).re = modulus (Q.eval (cayley t)) ^ 2 := by
  obtain ⟨q, hq, _, he⟩ := nonnegative_polynomial_factorization_degree_le (numerator p N)
    (numerator_nonnegative p hp N hN) N (natDegree_numerator_le p N hN)
  refine ⟨CayleySpectral.factor q N, CayleySpectral.natDegree_factor_le q N hq, ?_⟩
  intro t
  have hd : (1 + t ^ 2) ^ N ≠ 0 := pow_ne_zero _ (ne_of_gt (by positivity))
  apply mul_right_cancel₀ hd
  calc
    _ = (numerator p N).eval t := by rw [eval_numerator p N hN t, mul_comm]
    _ = modulus (q.eval (ofReal t)) ^ 2 := he t
    _ = _ := (CayleySpectral.modulus_sq_factor_cayley_mul q N hq t).symm


/-- The constructed factor works at every finite angle whose phase is in the affine chart. -/
theorem exists_factor_away_from_neg_one (p : LaurentPolynomial Surcomplex.{u})
    (hreal : ∀ θ : SignSequence.FiniteElement.{u}, (trigonometricPolynomial p θ).im = 0)
    (hp : ∀ θ : SignSequence.FiniteElement.{u}, 0 ≤ (trigonometricPolynomial p θ).re)
    (N : ℕ) (hN : ∀ k ∈ p.coeff.support, k.natAbs ≤ N) :
    ∃ Q : Polynomial Surcomplex.{u}, Q.natDegree ≤ N ∧
      ∀ θ : SignSequence.FiniteElement.{u}, finitePhase θ ≠ -1 →
        trigonometricPolynomial p θ = ofReal (modulus (Q.eval (finitePhase θ)) ^ 2) := by
  obtain ⟨Q, hQ, he⟩ := exists_factor_on_cayley p hp N hN
  refine ⟨Q, hQ, ?_⟩
  intro θ hθ
  have hc : cayley (cayleyCoord (finitePhase θ)) = finitePhase θ :=
    cayley_cayleyCoord (finitePhaseHom (Multiplicative.ofAdd θ)) hθ
  have hu : cayleyUnit (cayleyCoord (finitePhase θ)) = phaseUnit θ := Units.ext hc
  apply QuadraticAlgebra.ext
  · simpa only [trigonometricPolynomial, hu, hc, ofReal_re] using he (cayleyCoord (finitePhase θ))
  · exact hreal θ

end
end Surreal.Surcomplex.FejerRiesz
