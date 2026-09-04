import FabiusFunction.BellGeneratingFunctions
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Partial derivatives of the Bell polynomials

A derivation `D` of a ring `A` acts coefficientwise on `A⟦t⟧` and is again a derivation
(`coeffDerivation`).  Applied to `∂/∂x_i` on `ℚ[x_1, x_2, …]` and to the column theorem
`X(t)^k = k! ∑_n B_{n,k} t^n/n!` for the weight series `X(t) = ∑_j x_j t^j/j!`, this gives the
derivative identities

`∂B_{n,k}/∂x_i = C(n,i) B_{n-i,k-1}`,  `∂B_n/∂x_i = C(n,i) B_{n-i}`

for the partial and complete exponential Bell polynomials (`pderiv_partialBell_succ`,
`pderiv_bellComplete`).

## Main results

* `coeffDerivation`, `coeff_coeffDerivation`, `coeffDerivation_egfA`.
* `coeffDerivation_pderiv_bellWeightSeries`, `pderiv_partialBell_zero`, `pderiv_partialBell_succ`,
  `pderiv_bellComplete`.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

section CoeffDerivation

variable {R : Type*} {A : Type*} [CommSemiring R] [CommRing A] [Algebra R A]

/-- A derivation `D` of `A` acts coefficientwise on `A⟦t⟧`. -/
noncomputable def coeffDerivation (D : Derivation R A A) : Derivation R A⟦X⟧ A⟦X⟧ where
  toFun f := PowerSeries.mk fun n => D (coeff n f)
  map_add' f g := by
    ext n
    simp only [coeff_mk, map_add]
  map_smul' c f := by
    ext n
    simp only [coeff_mk, coeff_smul, Derivation.map_smul, RingHom.id_apply]
  map_one_eq_zero' := by
    ext n
    simp only [LinearMap.coe_mk, AddHom.coe_mk, coeff_mk, coeff_one, map_zero]
    split_ifs <;> simp
  leibniz' f g := by
    ext n
    simp only [LinearMap.coe_mk, AddHom.coe_mk, coeff_mk, map_add, smul_eq_mul, coeff_mul,
      map_sum, Derivation.leibniz, Finset.sum_add_distrib]
    congr 1
    rw [← Finset.Nat.sum_antidiagonal_swap]
    simp only [Prod.fst_swap, Prod.snd_swap]

/-- Coefficient extraction commutes with the coefficientwise derivation. -/
theorem coeff_coeffDerivation (D : Derivation R A A) (f : A⟦X⟧) (n : ℕ) :
    coeff n (coeffDerivation D f) = D (coeff n f) := by
  show coeff n (PowerSeries.mk fun n => D (coeff n f)) = D (coeff n f)
  exact coeff_mk _ _

/-- The coefficientwise derivation acts on exponential generating functions termwise. -/
theorem coeffDerivation_egfA [Algebra ℚ A] (D : Derivation ℚ A A) (a : ℕ → A) :
    coeffDerivation D (egfA A a) = egfA A fun n => D (a n) := by
  ext n
  rw [coeff_coeffDerivation, coeff_egfA, coeff_egfA, Derivation.leibniz, Derivation.map_algebraMap,
    smul_zero, add_zero, smul_eq_mul]

end CoeffDerivation

/-! ### The Bell polynomials in the variables `x_1, x_2, …` -/

section Bell

local notation "𝔹" => MvPolynomial ℕ ℚ

/-- `∂/∂x_{i+1}` of the weight series `∑_{j ≥ 1} x_j t^j/j!` is `t^{i+1}/(i+1)!`. -/
theorem coeffDerivation_pderiv_bellWeightSeries (i : ℕ) :
    coeffDerivation (MvPolynomial.pderiv (i + 1)) (bellWeightSeries 𝔹 MvPolynomial.X) =
      PowerSeries.C (algebraMap ℚ 𝔹 (1 / (i + 1).factorial)) * X ^ (i + 1) := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_coeffDerivation, bellWeightSeries, coeff_egfA, coeff_C_mul, coeff_X_pow,
    Derivation.leibniz, Derivation.map_algebraMap, smul_zero, add_zero, smul_eq_mul]
  by_cases hn : n = 0
  · subst hn
    simp
  · rw [if_neg hn, MvPolynomial.pderiv_X, Pi.single_apply]
    by_cases h : n = i + 1
    · subst h
      simp
    · simp [h]

/-- `∂B_{n,0}/∂x_{i+1} = 0`. -/
theorem pderiv_partialBell_zero (i n : ℕ) :
    MvPolynomial.pderiv (i + 1) (partialBell (MvPolynomial.X : ℕ → 𝔹) n 0) = 0 := by
  cases n with
  | zero =>
    rw [partialBell]
    exact (MvPolynomial.pderiv (i + 1)).map_one_eq_zero
  | succ n =>
    rw [partialBell]
    exact map_zero _

/-- The column theorem with the scalar written as a natural-number cast. -/
theorem bellWeightSeries_pow_natCast (k : ℕ) :
    bellWeightSeries 𝔹 MvPolynomial.X ^ k =
      ((k.factorial : ℕ) : 𝔹⟦X⟧) * egfA 𝔹 fun n => partialBell MvPolynomial.X n k := by
  rw [bellWeightSeries_pow, smul_eq_C_mul, map_natCast]

/-- **Derivative of the partial Bell polynomials:**
`∂B_{n,k+1}/∂x_{i+1} = C(n,i+1) B_{n-i-1,k}`. -/
theorem pderiv_partialBell_succ (i n k : ℕ) :
    MvPolynomial.pderiv (i + 1) (partialBell MvPolynomial.X n (k + 1)) =
      (n.choose (i + 1) : 𝔹) * partialBell MvPolynomial.X (n - (i + 1)) k := by
  set D := coeffDerivation (MvPolynomial.pderiv (i + 1) : Derivation ℚ 𝔹 𝔹) with hD
  have h := congrArg D (bellWeightSeries_pow_natCast (k + 1))
  rw [Derivation.leibniz_pow, Nat.add_sub_cancel, bellWeightSeries_pow_natCast, hD,
    coeffDerivation_pderiv_bellWeightSeries, Derivation.leibniz, Derivation.map_natCast, smul_zero,
    add_zero, coeffDerivation_egfA] at h
  simp only [smul_eq_mul, nsmul_eq_mul] at h
  have hL : ((k + 1 : ℕ) : 𝔹⟦X⟧) * (((k.factorial : ℕ) : 𝔹⟦X⟧) *
      (egfA 𝔹 fun n => partialBell MvPolynomial.X n k) *
        (PowerSeries.C (algebraMap ℚ 𝔹 (1 / (i + 1).factorial)) * X ^ (i + 1))) =
      PowerSeries.C (algebraMap ℚ 𝔹 (((k + 1 : ℕ) : ℚ) * (k.factorial : ℚ) * (1 / (i + 1).factorial))) *
        (X ^ (i + 1) * egfA 𝔹 fun n => partialBell MvPolynomial.X n k) := by
    simp only [map_mul, map_natCast]
    ring
  have hR : (((k + 1).factorial : ℕ) : 𝔹⟦X⟧) *
      (egfA 𝔹 fun n => MvPolynomial.pderiv (i + 1) (partialBell MvPolynomial.X n (k + 1))) =
      PowerSeries.C (algebraMap ℚ 𝔹 (((k + 1).factorial : ℕ) : ℚ)) *
        egfA 𝔹 fun n => MvPolynomial.pderiv (i + 1) (partialBell MvPolynomial.X n (k + 1)) := by
    simp only [map_natCast]
  rw [hL, hR] at h
  have hc := congrArg (coeff n) h
  rw [coeff_C_mul, coeff_C_mul, coeff_egfA, coeff_X_pow_mul'] at hc
  have hinj : ∀ q : ℚ, q ≠ 0 → algebraMap ℚ 𝔹 q ≠ 0 := fun q hq =>
    (map_ne_zero (algebraMap ℚ 𝔹)).mpr hq
  have hfac : (n.factorial : ℚ) ≠ 0 := by positivity
  have hkfac : ((k + 1).factorial : ℚ) ≠ 0 := by positivity
  split_ifs at hc with hin
  · -- `i + 1 ≤ n`: solve for the derivative
    rw [coeff_egfA, ← mul_assoc, ← map_mul, ← mul_assoc, ← map_mul] at hc
    have hq : algebraMap ℚ 𝔹 ((((k + 1).factorial : ℕ) : ℚ) * (1 / n.factorial)) ≠ 0 :=
      hinj _ (mul_ne_zero hkfac (one_div_ne_zero hfac))
    apply mul_left_cancel₀ hq
    rw [← hc, ← mul_assoc, ← map_natCast (algebraMap ℚ 𝔹) (n.choose (i + 1)), ← map_mul]
    congr 2
    rw [Nat.cast_choose ℚ hin, Nat.factorial_succ k]
    have h1 : ((i + 1).factorial : ℚ) ≠ 0 := by positivity
    have h2 : ((n - (i + 1)).factorial : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
  · -- `n < i + 1`: both sides vanish
    rw [mul_zero] at hc
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul]
    have hq : algebraMap ℚ 𝔹 ((((k + 1).factorial : ℕ) : ℚ) * (1 / n.factorial)) ≠ 0 :=
      hinj _ (mul_ne_zero hkfac (one_div_ne_zero hfac))
    rw [← mul_assoc, ← map_mul] at hc
    exact (mul_eq_zero.mp hc.symm).resolve_left hq

/-- **Derivative of the complete Bell polynomials:** `∂B_n/∂x_{i+1} = C(n,i+1) B_{n-i-1}`. -/
theorem pderiv_bellComplete (i n : ℕ) :
    MvPolynomial.pderiv (i + 1) (Bell.complete MvPolynomial.X n) =
      (n.choose (i + 1) : 𝔹) * Bell.complete MvPolynomial.X (n - (i + 1)) := by
  rw [bell_complete_eq_sum_partialBell, bell_complete_eq_sum_partialBell, map_sum,
    Finset.sum_range_succ', pderiv_partialBell_zero, add_zero, Finset.mul_sum]
  simp only [pderiv_partialBell_succ]
  rcases le_or_gt (i + 1) n with hin | hin
  · symm
    refine Finset.sum_subset (Finset.range_subset.mpr fun x hx => Finset.mem_range.mpr (by omega))
      fun k hk hk' => ?_
    rw [Finset.mem_range] at hk hk'
    rw [partialBell_eq_zero_of_lt _ (by omega), mul_zero]
  · rw [Nat.choose_eq_zero_of_lt hin, Nat.cast_zero]
    simp

end Bell

end Fabius
