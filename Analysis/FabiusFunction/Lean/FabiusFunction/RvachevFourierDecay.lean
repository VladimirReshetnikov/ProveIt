import FabiusFunction.BaselineDecay
import FabiusFunction.GlobalDecayEnvelope
import FabiusFunction.PeakRayEnvelope
import FabiusFunction.PhiZeroOrder
import FabiusFunction.RvachevProductContinuity
import FabiusFunction.SincCanonicalProduct
import FabiusFunction.ThueMorseLobeSign

/-!
# Public decay API for Rvachev's Fourier transform

The detailed Fourier-decay development is stated for the standalone sinc
product `rvachevFourierProduct`.  This module transfers its headline results
to the Fourier transform `rvachevFourier F` of any bounded Fabius solution.

The facade covers the canonical product, dyadic shell factorization, baseline
and global gauge bounds, the strict global peak at zero, the exact extremal
peak ray, positive and reflected negative side-lobe maxima, the central-lobe
maximum, the Thue--Morse lobe sign, and the exact real zero order.
Normalization, evenness, real-axis real-valuedness, and the zero set already
have direct `rvachevFourier` theorems in `FourierProduct`, so they are not
duplicated here.
-/

set_option autoImplicit false

open Filter Topology Real Set

namespace Fabius

/-! ## Product identification and canonical product -/

/-- The Fourier transform of a bounded Fabius solution, as a function on
`ℂ`, is the standalone Rvachev sinc product. -/
theorem rvachevFourier_eq_rvachevFourierProduct
    (F : BoundedFabius) (hF : IsFabius F) :
    rvachevFourier F = rvachevFourierProduct := by
  funext z
  exact rvachevFourier_eq_product F hF z

/-- The canonical product formula for the Fourier transform of a bounded
Fabius solution. -/
theorem rvachevFourier_eq_canonical
    (F : BoundedFabius) (hF : IsFabius F) (z : ℂ) :
    rvachevFourier F z =
      ∏' m : ℕ, (1 - z ^ 2 / ((m + 1 : ℕ) : ℂ) ^ 2) ^
        (padicValNat 2 (m + 1) + 1) :=
  (rvachevFourier_eq_product F hF z).trans
    (rvachevFourierProduct_eq_canonical z)

/-! ## Dyadic shells and baseline decay -/

/-- Dilating the Fourier variable by `2^k` extracts exactly the first `k`
sinc factors. -/
theorem rvachevFourier_two_pow_mul
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ) (z : ℂ) :
    rvachevFourier F ((2 : ℂ) ^ k * z) =
      (∏ j ∈ Finset.range k,
        complexSinc (Real.pi * ((2 : ℂ) ^ (j + 1) * z))) *
        rvachevFourier F z := by
  simpa only [rvachevFourier_eq_product F hF] using
    rvachevFourierProduct_two_pow_mul k z

/-- Total cross-multiplied real-axis shell identity for the actual Fourier
transform.  It includes both the zero ray `y = 0` and the empty shell
`k = 0`. -/
theorem norm_rvachevFourier_two_pow_mul_cross
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ) (y : ℝ) :
    ((2 : ℝ) ^ (k * (k + 1) / 2) * (Real.pi * |y|) ^ k) *
        ‖rvachevFourier F ((2 : ℂ) ^ k * (y : ℂ))‖ =
      (∏ j ∈ Finset.range k,
        |Real.sin ((2 : ℝ) ^ (j + 1) * Real.pi * y)|) *
        ‖rvachevFourier F (y : ℂ)‖ := by
  simpa only [rvachevFourier_eq_product F hF] using
    norm_rvachevFourierProduct_two_pow_mul_cross k y

/-- Exact real-axis modulus factorization along a nonzero dyadic ray. -/
theorem norm_rvachevFourier_two_pow_mul
    (F : BoundedFabius) (hF : IsFabius F)
    (k : ℕ) (y : ℝ) (hy : y ≠ 0) :
    ‖rvachevFourier F ((2 : ℂ) ^ k * (y : ℂ))‖ =
      (∏ j ∈ Finset.range k,
        |Real.sin ((2 : ℝ) ^ (j + 1) * Real.pi * y)|) /
          ((2 : ℝ) ^ (k * (k + 1) / 2) * (Real.pi * |y|) ^ k) *
        ‖rvachevFourier F (y : ℂ)‖ := by
  simpa only [rvachevFourier_eq_product F hF] using
    norm_rvachevFourierProduct_two_pow_mul k y hy

/-- Uniform Gelfond-type decay bound along every nonzero dyadic ray. -/
theorem norm_rvachevFourier_two_pow_mul_le
    (F : BoundedFabius) (hF : IsFabius F)
    (k : ℕ) (y : ℝ) (hy : y ≠ 0) :
    ‖rvachevFourier F ((2 : ℂ) ^ k * (y : ℂ))‖ ≤
      Real.sqrt (5 / 3) * (Real.sqrt 3 / 2) ^ k /
          ((2 : ℝ) ^ (k * (k + 1) / 2) * (Real.pi * |y|) ^ k) *
        ‖rvachevFourier F (y : ℂ)‖ := by
  simpa only [rvachevFourier_eq_product F hF] using
    norm_rvachevFourierProduct_two_pow_mul_le k y hy

/-- The modulus of the Fourier transform is at most one on the real axis. -/
theorem norm_rvachevFourier_le_one
    (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    ‖rvachevFourier F (x : ℂ)‖ ≤ 1 := by
  simpa only [rvachevFourier_eq_product F hF] using
    norm_rvachevFourierProduct_le_one x

/-- The real-axis Fourier modulus is strictly below one away from the
origin. -/
theorem norm_rvachevFourier_lt_one_of_ne_zero
    (F : BoundedFabius) (hF : IsFabius F) {x : ℝ} (hx : x ≠ 0) :
    ‖rvachevFourier F (x : ℂ)‖ < 1 := by
  simpa only [rvachevFourier_eq_product F hF] using
    norm_rvachevFourierProduct_lt_one_of_ne_zero hx

/-- The Fourier transform has unit norm on the real axis exactly at the
origin. -/
theorem norm_rvachevFourier_eq_one_iff
    (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    ‖rvachevFourier F (x : ℂ)‖ = 1 ↔ x = 0 := by
  simpa only [rvachevFourier_eq_product F hF] using
    norm_rvachevFourierProduct_eq_one_iff x

/-- Baseline inverse-frequency decay of the Fourier transform away from
zero. -/
theorem norm_rvachevFourier_le_inv
    (F : BoundedFabius) (hF : IsFabius F) {x : ℝ} (hx : x ≠ 0) :
    ‖rvachevFourier F (x : ℂ)‖ ≤ 1 / (Real.pi * |x|) := by
  simpa only [rvachevFourier_eq_product F hF] using
    norm_rvachevFourierProduct_le_inv hx

/-- Global `kappaInf`-gauge envelope for the actual Fourier transform on the
positive-frequency ray `x ≥ 1`. -/
theorem norm_rvachevFourier_le_decayGauge
    (F : BoundedFabius) (hF : IsFabius F) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x →
      ‖rvachevFourier F (x : ℂ)‖ ≤ C * decayGauge kappaInf x := by
  simpa only [rvachevFourier_eq_product F hF] using
    norm_rvachevFourierProduct_le_decayGauge

/-! ## Exact extremal peak ray -/

/-- Exact shell formula on the extremal dyadic ray through `2/3`. -/
theorem norm_rvachevFourier_two_pow_two_thirds
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ) :
    ‖rvachevFourier F ((2 : ℂ) ^ k * ((2 / 3 : ℝ) : ℂ))‖ =
      (Real.sqrt 3 / 2) ^ k /
          ((2 : ℝ) ^ (k * (k + 1) / 2) *
            (2 * Real.pi / 3) ^ k) *
        ‖rvachevFourier F (((2 / 3 : ℝ) : ℂ))‖ := by
  simpa only [rvachevFourier_eq_product F hF] using
    norm_rvachevFourierProduct_two_pow_two_thirds k

/-- Exact `kappaInf`-gauge envelope on the extremal dyadic ray through
`2/3`. -/
theorem norm_rvachevFourier_peak_ray_envelope
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ) :
    ‖rvachevFourier F ((2 : ℂ) ^ k * ((2 / 3 : ℝ) : ℂ))‖ =
      (‖rvachevFourier F (((2 / 3 : ℝ) : ℂ))‖ /
          decayGauge kappaInf (2 / 3 : ℝ)) *
        decayGauge kappaInf ((2 : ℝ) ^ k * (2 / 3)) := by
  simpa only [rvachevFourier_eq_product F hF] using
    norm_rvachevFourierProduct_peak_ray_envelope k

/-! ## Lobe maxima and signs -/

/-- Every positive side lobe `(m,m+1)`, with `m ≥ 1`, has a unique
maximizer of the Fourier modulus. -/
theorem existsUnique_isMaxOn_rvachevFourier_lobe
    (F : BoundedFabius) (hF : IsFabius F)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃! c, c ∈ Set.Ioo (m : ℝ) ((m : ℝ) + 1) ∧
      IsMaxOn (fun x : ℝ => ‖rvachevFourier F (x : ℂ)‖)
        (Set.Ioo (m : ℝ) ((m : ℝ) + 1)) c := by
  simpa only [rvachevFourier_eq_product F hF] using
    existsUnique_isMaxOn_lobe m hm

/-- Every reflected negative side lobe `(-(m+1),-m)`, with `m ≥ 1`, has a
unique maximizer of the Fourier modulus. -/
theorem existsUnique_isMaxOn_rvachevFourier_neg_lobe
    (F : BoundedFabius) (hF : IsFabius F)
    (m : ℕ) (hm : 1 ≤ m) :
    ∃! c, c ∈ Set.Ioo (-((m : ℝ) + 1)) (-(m : ℝ)) ∧
      IsMaxOn (fun x : ℝ => ‖rvachevFourier F (x : ℂ)‖)
        (Set.Ioo (-((m : ℝ) + 1)) (-(m : ℝ))) c := by
  simpa only [rvachevFourier_eq_product F hF] using
    existsUnique_isMaxOn_neg_lobe m hm

/-- The Fourier modulus attains a central-lobe maximum at the origin. -/
theorem isMaxOn_norm_rvachevFourier
    (F : BoundedFabius) (hF : IsFabius F) :
    IsMaxOn (fun x : ℝ => ‖rvachevFourier F (x : ℂ)‖)
      (Set.Ioo (-1 : ℝ) 1) 0 := by
  simpa only [rvachevFourier_eq_product F hF] using
    isMaxOn_norm_rvachevFourierProduct

/-- Every maximizer of the Fourier modulus on the central lobe is the
origin. -/
theorem isMaxOn_rvachevFourier_central_eq_zero
    (F : BoundedFabius) (hF : IsFabius F) {c : ℝ}
    (hc : c ∈ Set.Ioo (-1 : ℝ) 1)
    (hmax : IsMaxOn (fun x : ℝ => ‖rvachevFourier F (x : ℂ)‖)
      (Set.Ioo (-1 : ℝ) 1) c) :
    c = 0 := by
  apply isMaxOn_central_eq_zero hc
  simpa only [rvachevFourier_eq_product F hF] using hmax

/-- On the lobe `(m,m+1)`, the Fourier transform has the Thue--Morse
sign indexed by `m`. -/
theorem rvachevFourier_eq_thueMorse_sign_mul_norm
    (F : BoundedFabius) (hF : IsFabius F)
    {m : ℕ} {x : ℝ} (hx : x ∈ Set.Ioo (m : ℝ) ((m : ℝ) + 1)) :
    rvachevFourier F (x : ℂ) =
      (((thueMorseSign m : ℤ) : ℝ) *
        ‖rvachevFourier F (x : ℂ)‖ : ℝ) := by
  simpa only [rvachevFourier_eq_product F hF] using
    rvachevFourierProduct_eq_thueMorse_sign_mul_norm hx

/-- The Fourier transform is positive on each lobe whose index has even
binary weight. -/
theorem rvachevFourier_pos_of_even_weight
    (F : BoundedFabius) (hF : IsFabius F)
    {m : ℕ} {x : ℝ} (hx : x ∈ Set.Ioo (m : ℝ) ((m : ℝ) + 1))
    (hev : Even (binaryWeight m)) :
    0 < (rvachevFourier F (x : ℂ)).re := by
  simpa only [rvachevFourier_eq_product F hF] using
    rvachevFourierProduct_pos_of_even_weight hx hev

/-! ## Exact zero order at positive integers -/

/-- Logarithmic form of the exact zero order of the Fourier transform at a
positive integer `m`. -/
theorem tendsto_log_norm_rvachevFourier_sub_zero_order
    (F : BoundedFabius) (hF : IsFabius F)
    (m : ℕ) (hm : 1 ≤ m) :
    Tendsto (fun x : ℝ => Real.log ‖rvachevFourier F (x : ℂ)‖ -
      ((padicValNat 2 m + 1 : ℕ) : ℝ) * Real.log |x - (m : ℝ)|)
      (𝓝[≠] (m : ℝ))
      (𝓝 ((∑ p ∈ lobeExceptional (m : ℝ) \ lobeFiber m,
          Real.log (1 - (m : ℝ) ^ 2 / (lobeZero p) ^ 2) +
        ((padicValNat 2 m + 1 : ℕ) : ℝ) *
          (Real.log ((m : ℝ) + (m : ℝ)) - Real.log ((m : ℝ) ^ 2))) +
        ∑' p : {p : ℕ × ℕ // p ∉ lobeExceptional (m : ℝ)},
          Real.log (1 - (m : ℝ) ^ 2 / (lobeZero p.val) ^ 2))) := by
  simpa only [rvachevFourier_eq_product F hF] using
    tendsto_log_norm_sub_zero_order m hm

/-- Exact zero-order limit for the Fourier transform at a positive integer
`m`; the limiting constant is strictly positive because it is an
exponential. -/
theorem tendsto_norm_rvachevFourier_div_pow_zero_order
    (F : BoundedFabius) (hF : IsFabius F)
    (m : ℕ) (hm : 1 ≤ m) :
    Tendsto (fun x : ℝ => ‖rvachevFourier F (x : ℂ)‖ /
      |x - (m : ℝ)| ^ (padicValNat 2 m + 1))
      (𝓝[≠] (m : ℝ))
      (𝓝 (Real.exp ((∑ p ∈ lobeExceptional (m : ℝ) \ lobeFiber m,
          Real.log (1 - (m : ℝ) ^ 2 / (lobeZero p) ^ 2) +
        ((padicValNat 2 m + 1 : ℕ) : ℝ) *
          (Real.log ((m : ℝ) + (m : ℝ)) - Real.log ((m : ℝ) ^ 2))) +
        ∑' p : {p : ℕ × ℕ // p ∉ lobeExceptional (m : ℝ)},
          Real.log (1 - (m : ℝ) ^ 2 / (lobeZero p.val) ^ 2)))) := by
  simpa only [rvachevFourier_eq_product F hF] using
    tendsto_norm_div_pow_zero_order m hm

end Fabius
