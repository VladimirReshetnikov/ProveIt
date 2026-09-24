import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Tactic

/-!
# Rational descent from values on the natural grid

A rational-linear projection from the complex numbers onto the rationals
commutes with polynomial evaluation at rational assignments when it is applied
coefficientwise. If every value on the natural grid is rational, the projected
polynomial agrees there with the original polynomial. Infinite-grid polynomial
extensionality then gives descent of every coefficient to the rationals.

The denominator-clearing lemma uses only the finite sum of monomials in a
polynomial. Its common denominator is a positive natural number.
-/

namespace Diophantine

open MvPolynomial

noncomputable section

/-- Equality on the nonnegative integer grid determines a complex polynomial.
The variable type may be empty or infinite. -/
theorem complexPolynomial_eq_of_nat_eval_eq {σ : Type*}
    {P Q : MvPolynomial σ ℂ}
    (h : ∀ v : σ → ℕ, eval (fun i => (v i : ℂ)) P =
      eval (fun i => (v i : ℂ)) Q) : P = Q := by
  apply MvPolynomial.funext_set (fun _ : σ => Set.range (Nat.cast : ℕ → ℂ))
    (fun _ => Set.infinite_range_of_injective Nat.cast_injective)
  intro x hx
  choose v hv using fun i => hx i (Set.mem_univ i)
  have hxv : x = fun i => (v i : ℂ) := funext fun i => (hv i).symm
  rw [hxv]
  exact h v

private def projectCoefficients {σ : Type*} (π : ℂ →ₗ[ℚ] ℚ)
    (P : MvPolynomial σ ℂ) : MvPolynomial σ ℚ :=
  ∑ d ∈ P.support, monomial d (π (P.coeff d))

private theorem eval_projectCoefficients {σ : Type*} (π : ℂ →ₗ[ℚ] ℚ)
    (P : MvPolynomial σ ℂ) (v : σ → ℕ) :
    eval (fun i => (v i : ℚ)) (projectCoefficients π P) =
      π (eval (fun i => (v i : ℂ)) P) := by
  classical
  rw [projectCoefficients, eval_sum]
  conv_rhs => rw [eval_eq, map_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [eval_monomial]
  let w : ℚ := ∏ i ∈ d.support, (v i : ℚ) ^ d i
  have hw : (w : ℂ) = ∏ i ∈ d.support, (v i : ℂ) ^ d i := by
    simp [w]
  change π (P.coeff d) * w = π (P.coeff d * _)
  calc
    π (P.coeff d) * w = w • π (P.coeff d) := by simp [smul_eq_mul, mul_comm]
    _ = π (w • P.coeff d) := (π.map_smul w (P.coeff d)).symm
    _ = π (P.coeff d * ∏ i ∈ d.support, (v i : ℂ) ^ d i) := by
      congr 1
      rw [Algebra.smul_def]
      change (w : ℂ) * P.coeff d = _
      rw [hw, mul_comm]

/-- A complex polynomial with rational values on the nonnegative integer grid
has rational coefficients. No assumption on the number of variables is needed. -/
theorem exists_rationalPolynomial_of_nat_values {σ : Type*}
    (P : MvPolynomial σ ℂ)
    (hP : ∀ v : σ → ℕ, ∃ q : ℚ, eval (fun i => (v i : ℂ)) P = (q : ℂ)) :
    ∃ Q : MvPolynomial σ ℚ, map (algebraMap ℚ ℂ) Q = P := by
  obtain ⟨π, hπ⟩ := (Algebra.linearMap ℚ ℂ).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (algebraMap ℚ ℂ).injective)
  have hπrat (q : ℚ) : π (q : ℂ) = q := by
    exact DFunLike.congr_fun hπ q
  refine ⟨projectCoefficients π P, complexPolynomial_eq_of_nat_eval_eq ?_⟩
  intro v
  obtain ⟨q, hq⟩ := hP v
  have hmap := MvPolynomial.map_eval (algebraMap ℚ ℂ)
    (fun i => (v i : ℚ)) (projectCoefficients π P)
  have hmap' : eval (fun i => (v i : ℂ))
      (map (algebraMap ℚ ℂ) (projectCoefficients π P)) =
      (eval (fun i => (v i : ℚ)) (projectCoefficients π P) : ℂ) := by
    simpa only [Function.comp_def, map_natCast, eq_ratCast] using hmap.symm
  rw [hmap', eval_projectCoefficients, hq, hπrat]

/-- Every rational multivariate polynomial has a positive natural common
denominator, with an explicitly asserted integer polynomial after scaling. -/
theorem exists_positive_integer_multiple {σ : Type*} (P : MvPolynomial σ ℚ) :
    ∃ l : ℕ, 0 < l ∧ ∃ A : MvPolynomial σ ℤ,
      map (Int.castRingHom ℚ) A = C (l : ℚ) * P := by
  induction P using MvPolynomial.induction_on' with
  | monomial d q =>
      refine ⟨q.den, q.den_pos, monomial d q.num, ?_⟩
      rw [map_monomial, C_mul_monomial]
      congr 1
      change (q.num : ℚ) = (q.den : ℚ) * q
      have hden : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_ne_zero
      calc
        (q.num : ℚ) = (q.den : ℚ) * ((q.num : ℚ) / (q.den : ℚ)) := by
          field_simp
        _ = (q.den : ℚ) * q := by rw [q.num_div_den]
  | add P Q hP hQ =>
      obtain ⟨l, hl, A, hA⟩ := hP
      obtain ⟨m, hm, B, hB⟩ := hQ
      refine ⟨l * m, Nat.mul_pos hl hm, C (m : ℤ) * A + C (l : ℤ) * B, ?_⟩
      simp only [map_add, map_mul, map_C, Int.coe_castRingHom, Int.cast_natCast,
        hA, hB, Nat.cast_mul]
      ring

end

end Diophantine
