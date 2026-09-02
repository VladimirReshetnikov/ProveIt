import FabiusFunction.CyclotomicDivisibility

/-!
# The cyclotomic factor list of a Gaussian coefficient

The factor-list algorithm computes, for `1 ≤ d ≤ n`, the exponent
`e_d = ⌊n/d⌋ - ⌊k/d⌋ - ⌊(n-k)/d⌋` and returns the `d` with `e_d = 1`.  Since every exponent is
`0` or `1`, the returned list is exactly the set of cyclotomic factors of `[n,k]_q`, each with
multiplicity one:

`[n,k]_X = ∏_{d ∈ list} Φ_d(X)`,

and over `ℚ` membership in the list is equivalent to divisibility `Φ_d ∣ [n,k]_X`, i.e. to the
carry criterion `n mod d < k mod d`.

## Main declarations

* `cyclotomicFactorList`, `mem_cyclotomicFactorList`, `cyclotomic_exponent_le_one`.
* `gaussianBinomial_X_eq_prod_cyclotomicFactorList`: the multiplicity-one factorization.
* `cyclotomic_dvd_gaussianBinomial_iff_mem`: correctness of the list over `ℚ`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Polynomial Finset

/-- Every cyclotomic exponent of `[n,k]_X` is `0` or `1`. -/
theorem cyclotomic_exponent_le_one {n k d : ℕ} (hk : k ≤ n) (hd : 0 < d) :
    n / d - k / d - (n - k) / d ≤ 1 := by
  have := div_le_div_add_div_add_one hk hd
  omega

/-- **The factor-list algorithm**: the `d ∈ [1, n]` with `⌊n/d⌋ - ⌊k/d⌋ - ⌊(n-k)/d⌋ = 1`. -/
def cyclotomicFactorList (n k : ℕ) : Finset ℕ :=
  (Icc 1 n).filter fun d => n / d - k / d - (n - k) / d = 1

/-- Membership in the list is the carry criterion. -/
theorem mem_cyclotomicFactorList {n k d : ℕ} (hk : k ≤ n) :
    d ∈ cyclotomicFactorList n k ↔ (1 ≤ d ∧ d ≤ n) ∧ n % d < k % d := by
  unfold cyclotomicFactorList
  rw [mem_filter, mem_Icc]
  constructor
  · rintro ⟨hd, he⟩
    exact ⟨hd, (cyclotomic_exponent_eq_one_iff hk (by omega)).mp he⟩
  · rintro ⟨hd, he⟩
    exact ⟨hd, (cyclotomic_exponent_eq_one_iff hk (by omega)).mpr he⟩

variable {R : Type*} [CommRing R]

/-- **Correctness of the factor list**: `[n,k]_X = ∏_{d ∈ list} Φ_d`, each factor once, over
every integral domain. -/
theorem gaussianBinomial_X_eq_prod_cyclotomicFactorList [IsDomain R] {n k : ℕ} (hk : k ≤ n) :
    gaussianBinomial (X : R[X]) n k = ∏ d ∈ cyclotomicFactorList n k, cyclotomic d R := by
  rw [gaussianBinomial_X_eq_prod_cyclotomic hk, cyclotomicFactorList, prod_filter]
  refine prod_congr rfl fun d hd => ?_
  have hd0 : 0 < d := (mem_Icc.mp hd).1
  have hle := cyclotomic_exponent_le_one hk hd0
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h | h
  · rw [h, pow_zero, if_neg (by omega)]
  · rw [h, pow_one, if_pos rfl]

/-- Over `ℚ`, `Φ_d ∣ [n,k]_X` exactly for the `d` in the list. -/
theorem cyclotomic_dvd_gaussianBinomial_iff_mem {n k d : ℕ} (hk : k ≤ n) (hd : 0 < d) :
    cyclotomic d ℚ ∣ gaussianBinomial (X : ℚ[X]) n k ↔ d ∈ cyclotomicFactorList n k := by
  rw [cyclotomic_dvd_gaussianBinomial_iff hk hd, mem_cyclotomicFactorList hk]
  constructor
  · intro h
    refine ⟨⟨hd, ?_⟩, h⟩
    by_contra hdn
    push_neg at hdn
    rw [Nat.mod_eq_of_lt hdn, Nat.mod_eq_of_lt (by omega : k < d)] at h
    omega
  · exact fun h => h.2

end Fabius
