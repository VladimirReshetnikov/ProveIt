import FabiusFunction.GaussianBinomialUniversal
import FabiusFunction.GaussianBinomialPalindromic
import Mathlib.Algebra.Polynomial.Reverse

/-!
# Polynomial structure of universal Gaussian coefficients

For `k <= n`, the universal Gaussian coefficient `[n,k]_X` has exact degree
`k * (n - k)`, is monic, has constant coefficient one, and is fixed by
coefficient reversal in that degree.  In particular its coefficients form a
palindrome.

Every statement here is the `R := ℕ` instance of the corresponding
theorem of `GaussianBinomialPalindromic`, which proves the same facts
over an arbitrary commutative semiring by reflecting one q-Pascal
recurrence into the other.  This module keeps the `ℕ[X]`-specific names
for its callers.

## Main declarations

* `natDegree_gaussianBinomial_universal` gives the exact polynomial degree.
* `gaussianBinomial_universal_monic` gives leading coefficient one.
* `coeff_zero_gaussianBinomial_universal` gives constant coefficient one.
* `gaussianBinomial_universal_reflect` fixes the polynomial under reflection.
* `coeff_gaussianBinomial_universal_symm` states coefficient palindromicity.
-/

set_option autoImplicit false

namespace Fabius

open Polynomial

/-- For `k <= n`, the universal Gaussian coefficient `[n,k]_X` has exact
degree `k * (n - k)`. -/
theorem natDegree_gaussianBinomial_universal
    {n k : ℕ} (hk : k ≤ n) :
    (gaussianBinomial (X : ℕ[X]) n k).natDegree = k * (n - k) :=
  gaussianBinomial_natDegree hk

/-- For `k <= n`, the universal Gaussian coefficient `[n,k]_X` is monic. -/
theorem gaussianBinomial_universal_monic
    {n k : ℕ} (hk : k ≤ n) :
    (gaussianBinomial (X : ℕ[X]) n k).Monic :=
  gaussianBinomial_monic hk

/-- For `k <= n`, the universal Gaussian coefficient `[n,k]_X` has constant
coefficient one. -/
@[simp] theorem coeff_zero_gaussianBinomial_universal
    {n k : ℕ} (hk : k ≤ n) :
    (gaussianBinomial (X : ℕ[X]) n k).coeff 0 = 1 :=
  coeff_gaussianBinomial_zero hk

/-- For `k <= n`, reflecting the coefficients of `[n,k]_X` in its exact
degree fixes the polynomial. -/
theorem gaussianBinomial_universal_reflect
    {n k : ℕ} (hk : k ≤ n) :
    (gaussianBinomial (X : ℕ[X]) n k).reflect (k * (n - k)) =
      gaussianBinomial (X : ℕ[X]) n k :=
  reflect_gaussianBinomial hk

/-- For `k <= n`, the coefficients of `[n,k]_X` are palindromic across its
exact degree `k * (n - k)`. -/
theorem coeff_gaussianBinomial_universal_symm
    {n k d : ℕ} (hk : k ≤ n) (hd : d ≤ k * (n - k)) :
    (gaussianBinomial (X : ℕ[X]) n k).coeff d =
      (gaussianBinomial (X : ℕ[X]) n k).coeff (k * (n - k) - d) :=
  coeff_gaussianBinomial_reflect hk hd

end Fabius
