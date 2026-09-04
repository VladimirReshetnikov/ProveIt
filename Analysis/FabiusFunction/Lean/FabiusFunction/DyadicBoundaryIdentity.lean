import FabiusFunction.IntegerZeroLocalFactorization
import FabiusFunction.SincProductShells
import FabiusFunction.CentralLobePeakAtZero

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
    have hsub : k + 1 - 1 - j = k - j := by omega
    have hp : (2 : ℂ) ^ (j + 1) * (2 : ℂ) ^ (k - j) = (2 : ℂ) ^ (k + 1) := by
      rw [← pow_add]
      congr 1
      omega
    congr 1
    rw [hsub]
    field_simp
    linear_combination w * hp
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

/-! ### The volume's quotient form

On the range `0 < z < N` of the lemma the two left factors are nonzero, so the
division-free identity can be divided.  `Φ(z/(2N)) ≠ 0` because `|z/(2N)| < 1`,
where the central lobe has no zero. -/

/-- **`lem:dyadic-boundary` as printed.**  With `N = 2^k` and `0 < z < N`,

`|Φ(N+z)| = |Φ(1/2 + z/(2N))| / |Φ(z/(2N))| · (z/(N+z))^(k+1) · |Φ(z)|`. -/
theorem norm_rvachevFourierProduct_dyadic_boundary (k : ℕ) {z : ℝ}
    (hz0 : 0 < z) (hzN : z < 2 ^ k) :
    ‖rvachevFourierProduct (((2 : ℝ) ^ k + z : ℝ) : ℂ)‖
      = ‖rvachevFourierProduct ((1 / 2 + z / 2 ^ (k + 1) : ℝ) : ℂ)‖ /
          ‖rvachevFourierProduct ((z / 2 ^ (k + 1) : ℝ) : ℂ)‖ *
        (z / ((2 : ℝ) ^ k + z)) ^ (k + 1) *
        ‖rvachevFourierProduct ((z : ℝ) : ℂ)‖ := by
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hsum : (0 : ℝ) < 2 ^ k + z := by linarith
  -- the inner argument sits in the central lobe
  have hinner : |z / (2 : ℝ) ^ (k + 1)| < 1 := by
    rw [abs_of_nonneg (by positivity)]
    rw [div_lt_one (by positivity)]
    calc z < 2 ^ k := hzN
      _ ≤ 2 ^ (k + 1) := by
          apply pow_le_pow_right₀ (by norm_num)
          omega
  have hne : ‖rvachevFourierProduct ((z / (2 : ℝ) ^ (k + 1) : ℝ) : ℂ)‖ ≠ 0 :=
    ne_of_gt (norm_rvachevFourierProduct_pos hinner)
  -- the division-free identity, at the real point `z`
  have hid := rvachevFourierProduct_dyadic_boundary k ((z : ℝ) : ℂ)
  have hcast1 : (((2 : ℂ) ^ k + (z : ℂ))) = (((2 : ℝ) ^ k + z : ℝ) : ℂ) := by
    push_cast
    ring
  have hcast2 : ((z : ℂ) / (2 : ℂ) ^ (k + 1)) = ((z / (2 : ℝ) ^ (k + 1) : ℝ) : ℂ) := by
    push_cast
    ring
  have hcast3 : ((1 : ℂ) / 2 + (z : ℂ) / (2 : ℂ) ^ (k + 1))
      = ((1 / 2 + z / (2 : ℝ) ^ (k + 1) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hcast1, hcast2, hcast3] at hid
  -- take norms
  have hnorm := congrArg (fun c : ℂ => ‖c‖) hid
  simp only [norm_mul, norm_neg, norm_pow] at hnorm
  rw [Complex.norm_real, Complex.norm_real, abs_of_pos hsum, abs_of_pos hz0] at hnorm
  -- solve for the target
  field_simp at hnorm ⊢
  rw [div_pow]
  field_simp
  linear_combination hnorm

end Fabius
