import FabiusFunction.QLucas

/-!
# Which cyclotomic polynomials divide a Gaussian coefficient

By the cyclotomic factorization, `Φ_d` occurs in `[n,k]_X` with exponent
`e_d(n,k) = ⌊n/d⌋ - ⌊k/d⌋ - ⌊(n-k)/d⌋ ∈ {0,1}`, and `e_d = 1` exactly when
adding `k` and `n-k` carries in the units place in base `d`, that is when
`n mod d < k mod d`.  Since distinct cyclotomic polynomials are coprime over
`ℚ`, this gives the **carry criterion**

`Φ_d ∣ [n,k]_X ⟺ n mod d < k mod d`

in `ℚ[X]`; in particular every Gaussian polynomial is a product of distinct
cyclotomic polynomials.  The `q`-Lucas theorem with `b = s = 0` gives the
value `[an, bn]_ζ = \binom ab` at a primitive `n`-th root of unity.

## Main declarations

* `cyclotomic_exponent_eq_one_iff`: `e_d(n,k) = 1 ↔ n mod d < k mod d`.
* `cyclotomic_dvd_gaussianBinomial_iff`: the carry criterion over `ℚ`.
* `gaussianBinomial_mul_isPrimitiveRoot`: `[an, bn]_ζ = \binom ab`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Polynomial Finset

/-- The exponent of `Φ_d` in `[n,k]_X` is `1` exactly when adding `k` and `n - k`
carries in base `d`: `n mod d < k mod d`. -/
theorem cyclotomic_exponent_eq_one_iff {n k d : ℕ} (hk : k ≤ n) (hd : 0 < d) :
    n / d - k / d - (n - k) / d = 1 ↔ n % d < k % d := by
  have h1 := div_add_div_le_div hk hd
  have h2 := div_le_div_add_div_add_one hk hd
  have hn := Nat.div_add_mod n d
  have hk' := Nat.div_add_mod k d
  have hm := Nat.div_add_mod (n - k) d
  have hn' := Nat.mod_lt n hd
  have hk'' := Nat.mod_lt k hd
  have hm' := Nat.mod_lt (n - k) hd
  rcases Nat.lt_or_ge (k / d + (n - k) / d) (n / d) with hlt | hge
  · have he : n / d = k / d + (n - k) / d + 1 := by omega
    have hA : d * (n / d) = d * (k / d) + d * ((n - k) / d) + d := by rw [he]; ring
    constructor
    · intro _
      omega
    · intro _
      omega
  · have he : n / d = k / d + (n - k) / d := by omega
    have hA : d * (n / d) = d * (k / d) + d * ((n - k) / d) := by rw [he]; ring
    constructor
    · intro h0
      omega
    · intro h0
      omega

/-- **The carry criterion**: `Φ_d ∣ [n,k]_X` in `ℚ[X]` if and only if `n mod d < k mod d`. -/
theorem cyclotomic_dvd_gaussianBinomial_iff {n k d : ℕ} (hk : k ≤ n) (hd : 0 < d) :
    cyclotomic d ℚ ∣ gaussianBinomial (X : ℚ[X]) n k ↔ n % d < k % d := by
  rw [gaussianBinomial_X_eq_prod_cyclotomic hk]
  constructor
  · intro hdvd
    by_contra hlt
    have he0 : n / d - k / d - (n - k) / d = 0 := by
      have := div_le_div_add_div_add_one hk hd
      have h1 := (cyclotomic_exponent_eq_one_iff hk hd).not.mpr hlt
      omega
    have hcop : IsCoprime (cyclotomic d ℚ)
        (∏ d' ∈ Icc 1 n, cyclotomic d' ℚ ^ (n / d' - k / d' - (n - k) / d')) := by
      refine IsCoprime.prod_right fun d' _ => ?_
      rcases eq_or_ne d' d with rfl | hne
      · rw [he0, pow_zero]
        exact isCoprime_one_right
      · exact (cyclotomic.isCoprime_rat hne.symm).pow_right
    have hunit : IsUnit (cyclotomic d ℚ) := hcop.isUnit_of_dvd' dvd_rfl hdvd
    have := degree_eq_zero_of_isUnit hunit
    have hpos := degree_cyclotomic_pos d ℚ hd
    rw [this] at hpos
    exact lt_irrefl _ hpos
  · intro hlt
    have hdn : d ≤ n := by
      by_contra h
      have h' : n < d := not_le.mp h
      rw [Nat.mod_eq_of_lt h', Nat.mod_eq_of_lt (by omega)] at hlt
      omega
    refine dvd_trans ?_ (Finset.dvd_prod_of_mem _ (Finset.mem_Icc.mpr ⟨hd, hdn⟩))
    rw [(cyclotomic_exponent_eq_one_iff hk hd).mpr hlt, pow_one]

variable {R : Type*} [CommRing R] [IsDomain R]

/-- **Primitive-root value of a Gaussian coefficient with multiple indices**:
`[an, bn]_ζ = \binom ab` for a primitive `n`-th root of unity `ζ`. -/
theorem gaussianBinomial_mul_isPrimitiveRoot {ζ : R} {n : ℕ} (hn : 0 < n)
    (hζ : IsPrimitiveRoot ζ n) (a b : ℕ) :
    gaussianBinomial ζ (a * n) (b * n) = (a.choose b : R) := by
  have h := gaussianBinomial_q_lucas hn hζ a b (b := 0) (s := 0) hn hn
  rw [add_zero, add_zero, gaussianBinomial_zero_zero, mul_one] at h
  exact h

end Fabius
