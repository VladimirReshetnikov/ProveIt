import FabiusFunction.IntegerZeroLocalFactorization
import FabiusFunction.SincProductShells

/-!
# The dyadic-boundary identity

The Fourier-decay volume's `lem:dyadic-boundary` relates the sinc product just
past a dyadic boundary to its value inside the previous shell: with `N = 2^k`
and `0 < z < N`,

`|Φ(N+z)| = |Φ(1/2 + z/(2N))| / |Φ(z/(2N))| · (z/(N+z))^(k+1) · |Φ(z)|`.

Both halves are already in the corpus and only need to be composed:

* `rvachevFourierProduct_two_pow_mul_add_factorization` at `q = 1` clears the
  first `k+1` sinc denominators at the center `2^k`, exposing the prefix
  product and the local zero factor `w^(k+1)`;
* `rvachevFourierProduct_two_pow_mul` at `k+1`, applied to `w/2^(k+1)`, says
  that same prefix product is `Φ(w)/Φ(w/2^(k+1))`, after reflecting the index.

The identity is stated first in division-free form, so it needs no hypothesis at
all — not even `w ≠ 0` or a nonvanishing denominator — and then in the volume's
quotient form under the nonvanishing that the volume's range `0 < z < N`
guarantees.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- The prefix product of the first `k+1` sinc factors is `Φ(w)/Φ(w/2^(k+1))`,
in division-free form. -/
theorem prod_complexSinc_prefix_mul_rvachevFourierProduct (k : ℕ) (w : ℂ) :
    (∏ h ∈ range (k + 1), complexSinc ((Real.pi : ℂ) * w / (2 : ℂ) ^ h)) *
        rvachevFourierProduct (w / (2 : ℂ) ^ (k + 1))
      = rvachevFourierProduct w := by
  have h2 : ((2 : ℂ) ^ (k + 1)) ≠ 0 := pow_ne_zero _ two_ne_zero
  have hshell := rvachevFourierProduct_two_pow_mul (k + 1) (w / (2 : ℂ) ^ (k + 1))
  rw [mul_div_cancel₀ w h2] at hshell
  have hreindex :
      (∏ j ∈ range (k + 1),
          complexSinc (Real.pi * ((2 : ℂ) ^ (j + 1) * (w / (2 : ℂ) ^ (k + 1)))))
        = ∏ h ∈ range (k + 1), complexSinc ((Real.pi : ℂ) * w / (2 : ℂ) ^ h) := by
    rw [← Finset.prod_range_reflect
      (fun h => complexSinc ((Real.pi : ℂ) * w / (2 : ℂ) ^ h)) (k + 1)]
    refine Finset.prod_congr rfl fun j hj => ?_
    have hjk : j ≤ k := Nat.le_of_lt_succ (mem_range.mp hj)
    congr 1
    have hpow : (2 : ℂ) ^ (j + 1) / (2 : ℂ) ^ (k + 1) = ((2 : ℂ) ^ (k - j))⁻¹ := by
      rw [eq_inv_iff_mul_eq_one₀ (pow_ne_zero _ (two_ne_zero (α := ℂ))), div_mul_eq_mul_div,
        ← pow_add, div_eq_one_iff_eq (pow_ne_zero _ (two_ne_zero (α := ℂ)))]
      congr 1
      omega
    have hsub : k + 1 - 1 - j = k - j := by omega
    rw [hsub]
    field_simp
    rw [mul_comm ((2 : ℂ) ^ (j + 1)) w, mul_div_assoc, mul_assoc]
    congr 1
    rw [div_div, ← hpow]
    field_simp
  rw [hreindex] at hshell
  exact hshell.symm

/-- **`lem:dyadic-boundary`, division-free.**  With `N = 2^k`, for every `w`,

`(N + w)^(k+1) · Φ(N + w) · Φ(w/2^(k+1)) = -w^(k+1) · Φ(w) · Φ(1/2 + w/2^(k+1))`.

No hypothesis is needed: both sides are entire in `w`. -/
theorem rvachevFourierProduct_dyadic_boundary (k : ℕ) (w : ℂ) :
    ((2 : ℂ) ^ k + w) ^ (k + 1) * rvachevFourierProduct ((2 : ℂ) ^ k + w) *
        rvachevFourierProduct (w / (2 : ℂ) ^ (k + 1))
      = -w ^ (k + 1) * rvachevFourierProduct w *
          rvachevFourierProduct (1 / 2 + w / (2 : ℂ) ^ (k + 1)) := by
  have hfac := rvachevFourierProduct_two_pow_mul_add_factorization k 1 w
  have hone : ((2 : ℂ) ^ k * ((1 : ℕ) : ℂ) + w) = (2 : ℂ) ^ k + w := by
    push_cast
    ring
  rw [hone] at hfac
  have hhalf : (((1 : ℕ) : ℂ) / 2 + w / (2 : ℂ) ^ (k + 1)) = 1 / 2 + w / (2 : ℂ) ^ (k + 1) := by
    push_cast
    ring
  rw [hhalf] at hfac
  have hprefix := prod_complexSinc_prefix_mul_rvachevFourierProduct k w
  calc ((2 : ℂ) ^ k + w) ^ (k + 1) * rvachevFourierProduct ((2 : ℂ) ^ k + w) *
        rvachevFourierProduct (w / (2 : ℂ) ^ (k + 1))
      = ((-1 : ℂ) ^ (1 : ℕ) * w ^ (k + 1) *
          (∏ h ∈ range (k + 1), complexSinc ((Real.pi : ℂ) * w / (2 : ℂ) ^ h)) *
          rvachevFourierProduct (1 / 2 + w / (2 : ℂ) ^ (k + 1))) *
          rvachevFourierProduct (w / (2 : ℂ) ^ (k + 1)) := by rw [hfac]
    _ = -w ^ (k + 1) *
          ((∏ h ∈ range (k + 1), complexSinc ((Real.pi : ℂ) * w / (2 : ℂ) ^ h)) *
            rvachevFourierProduct (w / (2 : ℂ) ^ (k + 1))) *
          rvachevFourierProduct (1 / 2 + w / (2 : ℂ) ^ (k + 1)) := by
        push_cast
        ring
    _ = -w ^ (k + 1) * rvachevFourierProduct w *
          rvachevFourierProduct (1 / 2 + w / (2 : ℂ) ^ (k + 1)) := by rw [hprefix]

end Fabius
