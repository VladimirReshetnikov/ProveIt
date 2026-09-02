import FabiusFunction.CyclotomicDivisibility
import FabiusFunction.PolynomialQDerivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Combinatorics.Enumerative.Catalan.Basic

/-!
# MacMahon's q-Catalan polynomial

`[n+1]_X = ∏_{d ∣ n+1, d > 1} Φ_d(X)`, and each such `Φ_d` divides the central
Gaussian coefficient `[2n,n]_X` by the carry criterion (`n ≡ -1 (mod d)`, so
`2n mod d = d-2 < d-1 = n mod d`).  Distinct cyclotomic polynomials being
coprime over `ℚ`, `[n+1]_X ∣ [2n,n]_X` in `ℚ[X]`, hence in `ℤ[X]` since
`[n+1]_X` is monic.  The quotient is MacMahon's **`q`-Catalan polynomial**

`C_n(q) = [2n,n]_q / [n+1]_q ∈ ℤ[q]`,

of degree `n(n-1)`, with `(n+1) C_n(1) = \binom{2n}{n}`, i.e. `C_n(1)` is the
Catalan number.

## Main declarations

* `qInt_X_eq_prod_cyclotomic`: `[n+1]_X = ∏_{d ∣ n+1, d ≠ 1} Φ_d` in `ℚ[X]`.
* `qInt_X_dvd_gaussianBinomial_int`: `[n+1]_X ∣ [2n,n]_X` in `ℤ[X]`.
* `qCatalan`, `qInt_X_mul_qCatalan`, `qCatalan_natDegree`, `qCatalan_eval_one`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Polynomial Finset

/-- Ring homomorphisms commute with `q`-integers. -/
theorem map_qInt {R S : Type*} [Semiring R] [Semiring S] (φ : R →+* S) (q : R) (n : ℕ) :
    φ (qInt q n) = qInt (φ q) n := by
  unfold qInt
  rw [map_sum]
  simp_rw [map_pow]

/-- `[n+1]_X` is monic. -/
theorem qInt_X_monic {R : Type*} [CommRing R] [Nontrivial R] (n : ℕ) :
    (qInt (X : R[X]) (n + 1)).Monic :=
  monic_geom_sum_X (Nat.succ_ne_zero n)

/-- `[n+1]_X` has degree `n`. -/
theorem qInt_X_natDegree {R : Type*} [CommRing R] [Nontrivial R] (n : ℕ) :
    (qInt (X : R[X]) (n + 1)).natDegree = n := by
  refine natDegree_eq_of_le_of_coeff_ne_zero ?_ ?_
  · unfold qInt
    exact natDegree_sum_le_of_forall_le _ _ fun i hi =>
      (natDegree_X_pow_le i).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
  · unfold qInt
    rw [finsetSum_coeff]
    simp [coeff_X_pow]

/-- `(X - 1) [n+1]_X = X^{n+1} - 1`. -/
theorem X_sub_one_mul_qInt {R : Type*} [CommRing R] (n : ℕ) :
    ((X : R[X]) - 1) * qInt X (n + 1) = X ^ (n + 1) - 1 := by
  calc ((X : R[X]) - 1) * qInt X (n + 1) = -((1 - X) * qInt X (n + 1)) := by ring
    _ = X ^ (n + 1) - 1 := by rw [one_sub_mul_qInt]; ring

/-- `[n+1]_X = ∏_{d ∣ n+1, d ≠ 1} Φ_d(X)` in `ℚ[X]`. -/
theorem qInt_X_eq_prod_cyclotomic (n : ℕ) :
    qInt (X : ℚ[X]) (n + 1) = ∏ d ∈ (n + 1).divisors.erase 1, cyclotomic d ℚ := by
  have hX : ((X : ℚ[X]) - 1) ≠ 0 := by
    intro h
    have := congrArg (eval 0) h
    simp at this
  refine mul_left_cancel₀ hX ?_
  rw [X_sub_one_mul_qInt, ← prod_cyclotomic_eq_X_pow_sub_one (Nat.succ_pos n) ℚ,
    ← Finset.mul_prod_erase _ _ (Nat.one_mem_divisors.mpr (Nat.succ_ne_zero n)), cyclotomic_one]

/-- `[n+1]_X ∣ [2n,n]_X` in `ℚ[X]`. -/
theorem qInt_X_dvd_gaussianBinomial_rat (n : ℕ) :
    qInt (X : ℚ[X]) (n + 1) ∣ gaussianBinomial (X : ℚ[X]) (2 * n) n := by
  rw [qInt_X_eq_prod_cyclotomic]
  refine Finset.prod_dvd_of_coprime (fun d _ d' _ hne => cyclotomic.isCoprime_rat hne) ?_
  intro d hd
  rw [Finset.mem_erase, Nat.mem_divisors] at hd
  obtain ⟨hd1, hdvd, -⟩ := hd
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdvd (Nat.succ_pos n)
  have hd2 : 2 ≤ d := by omega
  obtain ⟨t, ht⟩ := hdvd
  have ht1 : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with rfl | h
    · omega
    · exact h
  refine (cyclotomic_dvd_gaussianBinomial_iff (by omega) hd0).mpr ?_
  have h1 : d * (t - 1) = d * t - d := Nat.mul_sub_one d t
  have h2 : d * (2 * t - 1) = d * (2 * t) - d := Nat.mul_sub_one d (2 * t)
  have h3 : d * (2 * t) = 2 * (d * t) := by ring
  have h4 : d ≤ d * t := Nat.le_mul_of_pos_right d ht1
  have hn : n = (d - 1) + d * (t - 1) := by omega
  have h2n : 2 * n = (d - 2) + d * (2 * t - 1) := by omega
  rw [hn, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega : d - 1 < d), ← hn, h2n,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega : d - 2 < d)]
  omega

/-- `[n+1]_X ∣ [2n,n]_X` in `ℤ[X]`. -/
theorem qInt_X_dvd_gaussianBinomial_int (n : ℕ) :
    qInt (X : ℤ[X]) (n + 1) ∣ gaussianBinomial (X : ℤ[X]) (2 * n) n := by
  have h := qInt_X_dvd_gaussianBinomial_rat n
  rw [← (map_dvd_map (Int.castRingHom ℚ) Int.cast_injective (qInt_X_monic n))]
  have e1 : (qInt (X : ℤ[X]) (n + 1)).map (Int.castRingHom ℚ) = qInt (X : ℚ[X]) (n + 1) := by
    rw [← coe_mapRingHom, map_qInt, coe_mapRingHom, map_X]
  have e2 : (gaussianBinomial (X : ℤ[X]) (2 * n) n).map (Int.castRingHom ℚ) =
      gaussianBinomial (X : ℚ[X]) (2 * n) n := by
    rw [← coe_mapRingHom, map_gaussianBinomial, coe_mapRingHom, map_X]
  rwa [e1, e2]

/-- **MacMahon's `q`-Catalan polynomial** `C_n(q) = [2n,n]_q / [n+1]_q ∈ ℤ[q]`. -/
noncomputable def qCatalan (n : ℕ) : ℤ[X] :=
  gaussianBinomial (X : ℤ[X]) (2 * n) n /ₘ qInt (X : ℤ[X]) (n + 1)

/-- `[n+1]_X · C_n(X) = [2n,n]_X`. -/
theorem qInt_X_mul_qCatalan (n : ℕ) :
    qInt (X : ℤ[X]) (n + 1) * qCatalan n = gaussianBinomial (X : ℤ[X]) (2 * n) n := by
  have h := modByMonic_add_div (gaussianBinomial (X : ℤ[X]) (2 * n) n) (qInt (X : ℤ[X]) (n + 1))
  rwa [(modByMonic_eq_zero_iff_dvd (qInt_X_monic n)).mpr (qInt_X_dvd_gaussianBinomial_int n),
    zero_add] at h

/-- `C_n(q)` has degree `n(n-1)`. -/
theorem qCatalan_natDegree (n : ℕ) : (qCatalan n).natDegree = n * (n - 1) := by
  rw [qCatalan, natDegree_divByMonic _ (qInt_X_monic n), qInt_X_natDegree,
    gaussianBinomial_natDegree (by omega : n ≤ 2 * n), show 2 * n - n = n by omega,
    Nat.mul_sub_one]

/-- `(n+1) · C_n(1) = \binom{2n}{n}`: the value of the `q`-Catalan polynomial at `q = 1` is
the Catalan number. -/
theorem qCatalan_eval_one_mul (n : ℕ) :
    ((n : ℤ) + 1) * (qCatalan n).eval 1 = ((2 * n).choose n : ℤ) := by
  have h := congrArg (eval (1 : ℤ)) (qInt_X_mul_qCatalan n)
  rw [eval_mul] at h
  have e1 : (qInt (X : ℤ[X]) (n + 1)).eval 1 = (n : ℤ) + 1 := by
    rw [← coe_evalRingHom, map_qInt, coe_evalRingHom, eval_X, qInt_one_left, Nat.cast_succ]
  have e2 : (gaussianBinomial (X : ℤ[X]) (2 * n) n).eval 1 = ((2 * n).choose n : ℤ) := by
    rw [← coe_evalRingHom, map_gaussianBinomial, coe_evalRingHom, eval_X,
      gaussianBinomial_one_eq_natCast_choose]
  rwa [e1, e2] at h

/-- `C_n(1) = catalan n`. -/
theorem qCatalan_eval_one (n : ℕ) : (qCatalan n).eval 1 = (catalan n : ℤ) := by
  have h := qCatalan_eval_one_mul n
  have hc : ((n : ℤ) + 1) * (catalan n : ℤ) = ((2 * n).choose n : ℤ) := by
    have := succ_mul_catalan_eq_centralBinom n
    rw [Nat.centralBinom_eq_two_mul_choose] at this
    exact_mod_cast this
  exact mul_left_cancel₀ (by positivity) (h.trans hc.symm)

end Fabius
