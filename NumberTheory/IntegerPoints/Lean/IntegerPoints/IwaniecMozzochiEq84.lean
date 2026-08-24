import IntegerPoints.IwaniecMozzochiThetaRanges
import IntegerPoints.IwaniecMozzochiReductionEq75
import IntegerPoints.VanDerCorput

/-!
# The exact Section 8 phase reduction in Iwaniec--Mozzochi

This module records the algebraic and finite-support part of (8.4).  The
reciprocal phase is split into its constant, linear, and quadratic terms, and
the remaining factor is written in the corrected form from the source tex.
The reduction is exact: no asymptotic notation and no Taylor premise is hidden
in the definitions below.

The last analytic step of (8.4) is deliberately not asserted here.  It still
requires a uniform partial-summation estimate for

`sigma(n / N) * e(alpha*n + beta*n^2) * (e(t(n)) - 1)`

using the quadratic second-derivative bound and uniform bounds for the fixed
smooth weight.  The lemmas below expose precisely that remaining finite sum.
-/

open Real Finset

namespace LeanProofs.IntegerPoints

open IMReductionEq75

/-! ## The Section 8 model phase and its exact remainder -/

/-- The model value `beta = x h / (m + v)^3`.  Farey geometry identifies this
with `betaIM`. -/
noncomputable def section8Beta (x h m v : ℝ) : ℝ :=
  x * h / (m + v) ^ 3

/-- The model value `alpha = -x h/(m+v)^2 - 2v beta`. -/
noncomputable def section8Alpha (x h m v : ℝ) : ℝ :=
  -(x * h / (m + v) ^ 2) - 2 * v * section8Beta x h m v

/-- The exact error after extracting the constant, linear, and quadratic
terms from `x h/(m+n)`.  This phase-difference presentation makes its
derivative transparent; `section8Remainder_eq_corrected` gives the
cancellation-friendly displayed presentation from Section 8. -/
noncomputable def section8Remainder (x h m v n : ℝ) : ℝ :=
  x * h / (m + n) - x * h / m + x * h * n / (m + v) ^ 2 +
    2 * v * x * h * n / (m + v) ^ 3 - x * h * n ^ 2 / (m + v) ^ 3

/-- The derivative of `section8Remainder`, in the form used to prove the
paper's bound `|t'(n)| << x H N^2 M^-4`. -/
noncomputable def section8RemainderDeriv (x h m v n : ℝ) : ℝ :=
  -x * h / (m + n) ^ 2 + x * h / (m + v) ^ 2 +
    2 * v * x * h / (m + v) ^ 3 - 2 * x * h * n / (m + v) ^ 3

/-- The phase decomposition is an exact algebraic identity.  In particular,
it remains true with Lean's totalized division even at a pole; positivity is
only needed later for estimates and differentiation. -/
theorem section8_phase_decomposition (x h m v n : ℝ) :
    x * h / (m + n) = x * h / m + section8Alpha x h m v * n +
      section8Beta x h m v * n ^ 2 + section8Remainder x h m v n := by
  unfold section8Alpha section8Beta section8Remainder
  ring

/-- The corrected second presentation of `t(n)` in Section 8.  The printed
paper has `2m-v` in the preceding formula; the reciprocal identity forces
`2m+v`, and hence the coefficient `v^2(3m+v)` below. -/
theorem section8Remainder_eq_corrected
    {x h m v n : ℝ} (hm : m ≠ 0) (hmv : m + v ≠ 0) (hmn : m + n ≠ 0) :
    section8Remainder x h m v n =
      -(v ^ 2 * (3 * m + v) * x * h * n) / (m ^ 2 * (m + v) ^ 3) -
        ((m ^ 2 * n - 3 * m ^ 2 * v - 3 * m * v ^ 2 - v ^ 3) *
          x * h * n ^ 2) / (m ^ 2 * (m + n) * (m + v) ^ 3) := by
  unfold section8Remainder
  field_simp [hm, hmv, hmn] <;> ring

/-- A compact factorization of the exact remainder.  The factor
`m*n^2 - 3*m*n*v + 3*m*v^2 + v^3` is the numerator whose size must be
controlled on the support `4N <= n <= 8N`; this form makes the denominator
scale `m*(m+n)*(m+v)^3` explicit. -/
theorem section8Remainder_eq_factored
    {x h m v n : ℝ} (hm : m ≠ 0) (hmv : m + v ≠ 0) (hmn : m + n ≠ 0) :
    section8Remainder x h m v n =
      -(x * h * n * (m * n ^ 2 - 3 * m * n * v + 3 * m * v ^ 2 + v ^ 3)) /
        (m * (m + n) * (m + v) ^ 3) := by
  unfold section8Remainder
  field_simp [hm, hmv, hmn] <;> ring

/-- The derivative has a double zero at the Farey displacement `n = v`.
This exact factorization is the cancellation needed for the paper's
`|t'(n)| << x H N^2 M^-4` estimate. -/
theorem section8RemainderDeriv_eq_factored
    {x h m v n : ℝ} (hmv : m + v ≠ 0) (hmn : m + n ≠ 0) :
    section8RemainderDeriv x h m v n =
      -(x * h * (n - v) ^ 2 * (3 * m + 2 * n + v)) /
        ((m + n) ^ 2 * (m + v) ^ 3) := by
  unfold section8RemainderDeriv
  field_simp [hmv, hmn] <;> ring

/-- Exact differentiability of the Section 8 remainder away from its sole
moving pole `n = -m`. -/
theorem section8Remainder_hasDerivAt
    {x h m v n : ℝ} (hmn : m + n ≠ 0) :
    HasDerivAt (section8Remainder x h m v)
      (section8RemainderDeriv x h m v n) n := by
  unfold section8Remainder section8RemainderDeriv
  have hden : HasDerivAt (fun y : ℝ => m + y) 1 n :=
    (hasDerivAt_id n).const_add m
  have hrec := (hasDerivAt_const n (x * h)).div hden hmn
  have hlin₁ :
      HasDerivAt (fun y : ℝ => x * h / (m + v) ^ 2 * y)
        (x * h / (m + v) ^ 2) n := by
    simpa only [id_eq, mul_one] using
      (hasDerivAt_id n).const_mul (x * h / (m + v) ^ 2)
  have hlin₂ :
      HasDerivAt (fun y : ℝ => 2 * v * x * h / (m + v) ^ 3 * y)
        (2 * v * x * h / (m + v) ^ 3) n := by
    simpa only [id_eq, mul_one] using
      (hasDerivAt_id n).const_mul (2 * v * x * h / (m + v) ^ 3)
  have hquad :
      HasDerivAt (fun y : ℝ => x * h / (m + v) ^ 3 * y ^ 2)
        (x * h / (m + v) ^ 3 * (2 * n)) n := by
    simpa [Pi.pow_apply] using
      ((hasDerivAt_id n).pow 2).const_mul (x * h / (m + v) ^ 3)
  have hcombined := (((hrec.sub_const (x * h / m)).add hlin₁).add hlin₂).sub hquad
  refine (hcombined.congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards with y
    simp only [Pi.add_apply, Pi.sub_apply, Pi.div_apply]
    ring
  · ring

/-! ## Identification with the Farey parameters -/

/-- A positive square raised to the power `3/2` is the corresponding cube. -/
theorem section8_rpow_sq_three_halves {y : ℝ} (hy : 0 < y) :
    (y ^ 2) ^ ((3 : ℝ) / 2) = y ^ 3 := by
  rw [← Real.rpow_natCast y 2, ← Real.rpow_mul hy.le]
  norm_num

private theorem section8_rpow_half_cancel {x : ℝ} (hx : 0 < x) :
    x ^ (-(1 : ℝ) / 2) * x ^ ((3 : ℝ) / 2) = x := by
  calc
    x ^ (-(1 : ℝ) / 2) * x ^ ((3 : ℝ) / 2) =
        x ^ (-(1 : ℝ) / 2 + (3 : ℝ) / 2) :=
      (Real.rpow_add hx _ _).symm
    _ = x := by norm_num

/-- The real-power formula behind (8.1): if `q = x/y^2`, then
`x^-1/2 q^3/2 u = x u/y^3`. -/
theorem section8_beta_model_of_coefficient
    {x q y u : ℝ} (hx : 0 < x) (hy : 0 < y) (hq : q = x / y ^ 2) :
    x ^ (-(1 : ℝ) / 2) * q ^ ((3 : ℝ) / 2) * u = x * u / y ^ 3 := by
  subst q
  rw [Real.div_rpow hx.le (sq_nonneg y), section8_rpow_sq_three_halves hy]
  calc
    x ^ (-(1 : ℝ) / 2) * (x ^ ((3 : ℝ) / 2) / y ^ 3) * u =
        (x ^ (-(1 : ℝ) / 2) * x ^ ((3 : ℝ) / 2)) * u / y ^ 3 := by
      ring
    _ = x * u / y ^ 3 := by rw [section8_rpow_half_cancel hx]

/-- Farey geometry identifies the definition `betaIM` with the rational
model `x h/(m+v)^3`. -/
theorem betaIM_eq_section8Beta
    {x H M : ℝ} {a c h : ℕ}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c) :
    betaIM x a c h = section8Beta x h (fareyPoint x a c) (fareyFrac x a c) := by
  rcases fareyPoint_geometry hmain hfarey with
    ⟨hm, hv₀, _hv₁, _hsum, hcoefficient, _hmLower, _hmUpper⟩
  have hx₀ : 0 < x := zero_lt_one.trans_le hmain.1
  have hm₀ : 0 < (fareyPoint x a c : ℝ) := by exact_mod_cast hm
  have hmv₀ : 0 < (fareyPoint x a c : ℝ) + fareyFrac x a c := by
    positivity
  unfold betaIM section8Beta
  exact section8_beta_model_of_coefficient hx₀ hmv₀ hcoefficient.symm

/-- Farey geometry likewise identifies `alphaIM` with the model linear
coefficient. -/
theorem alphaIM_eq_section8Alpha
    {x H M : ℝ} {a c h : ℕ}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c) :
    alphaIM x a c h = section8Alpha x h (fareyPoint x a c) (fareyFrac x a c) := by
  rcases fareyPoint_geometry hmain hfarey with
    ⟨_hm, _hv₀, _hv₁, _hsum, hcoefficient, _hmLower, _hmUpper⟩
  have hbeta := betaIM_eq_section8Beta (h := h) hmain hfarey
  have hlinear :
      x * (h : ℝ) /
          ((fareyPoint x a c : ℝ) + fareyFrac x a c) ^ 2 =
        (a : ℝ) * h / c := by
    calc
      x * (h : ℝ) /
          ((fareyPoint x a c : ℝ) + fareyFrac x a c) ^ 2 =
          (x / ((fareyPoint x a c : ℝ) + fareyFrac x a c) ^ 2) * h := by
        ring
      _ = ((a : ℝ) / c) * h := by rw [hcoefficient]
      _ = (a : ℝ) * h / c := by ring
  unfold alphaIM section8Alpha
  rw [hbeta, hlinear]

/-- All denominators used in the Section 8 expansion are positive in the
declared main/Farey range, including `m+n` for every natural summation index. -/
theorem section8_farey_denominators
    {x H M : ℝ} {a c : ℕ}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c) :
    0 < (fareyPoint x a c : ℝ) ∧
      0 < (fareyPoint x a c : ℝ) + fareyFrac x a c ∧
      ∀ n : ℕ, 0 < (fareyPoint x a c : ℝ) + n := by
  rcases fareyPoint_geometry hmain hfarey with
    ⟨hm, hv₀, _hv₁, _hsum, _hcoefficient, _hmLower, _hmUpper⟩
  have hm₀ : 0 < (fareyPoint x a c : ℝ) := by exact_mod_cast hm
  exact ⟨hm₀, by positivity, fun n => by positivity⟩

/-- The integer Farey centre is itself comparable with `M`.  This is the
lower denominator bound used when estimating the factored remainder: since
`0 <= v < 1 <= m` and `M <= m+v`, one has `M/2 <= m`. -/
theorem half_M_le_fareyPoint
    {x H M : ℝ} {a c : ℕ}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c) :
    M / 2 ≤ (fareyPoint x a c : ℝ) := by
  rcases fareyPoint_geometry hmain hfarey with
    ⟨hm, _hv₀, hv₁, hsum, _hcoefficient, hmLower, _hmUpper⟩
  have hmOneNat : 1 ≤ fareyPoint x a c := hm
  have hmOne : (1 : ℝ) ≤ (fareyPoint x a c : ℝ) := by exact_mod_cast hmOneNat
  have hvle : fareyFrac x a c ≤ (fareyPoint x a c : ℝ) := hv₁.le.trans hmOne
  have hMsum : M ≤ (fareyPoint x a c : ℝ) + fareyFrac x a c := by
    rw [hsum]
    exact hmLower
  linarith

/-- The quadratic coefficient is strictly positive on the Fourier support. -/
theorem betaIM_pos_of_mem_intRange
    {x H M : ℝ} {a c h : ℕ}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c)
    (hh : h ∈ intRange H (4 * H)) :
    0 < betaIM x a c h := by
  have hx₀ : 0 < x := zero_lt_one.trans_le hmain.1
  have hH₀ : 0 < H := zero_lt_one.trans_le hmain.2.2.2.1
  have hh₀ : 0 < (h : ℝ) := hH₀.trans (mem_intRange_four_mul hH₀ hh).1
  have hden := (section8_farey_denominators hmain hfarey).2.1
  rw [betaIM_eq_section8Beta hmain hfarey]
  unfold section8Beta
  positivity

/-- The exact inverse-scale identity used both in (8.2) and in the quadratic
sum estimate following (8.3). -/
theorem section8_gscale_inv (x H M : ℝ) :
    x * H / M ^ 3 * shiftLength x M = (Gscale x H M)⁻¹ := by
  unfold Gscale
  rw [inv_div]
  ring

/-- The explicit upper half of (8.2).  It does not use the lower short-cell
condition: throughout the main/Farey range and the full Fourier block,
`beta*N <= 4`. -/
theorem betaIM_mul_shiftLength_le_four
    {x H M : ℝ} {a c h : ℕ}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c)
    (hh : h ∈ intRange H (4 * H)) :
    betaIM x a c h * shiftLength x M ≤ 4 := by
  have hmain' : InMainRange x H M := hmain
  rcases hmain with ⟨hx, hxM, _hMx, hH, _hHupper, _hHlower, _hHlower₂, _hMlower⟩
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  have hM₀ : 0 < M := (Real.rpow_pos_of_pos hx₀ theta0).trans hxM
  have hH₀ : 0 < H := zero_lt_one.trans_le hH
  have hN₀ : 0 < shiftLength x M := by
    unfold shiftLength
    exact mul_pos hM₀ (Real.rpow_pos_of_pos hx₀ _)
  rcases fareyPoint_geometry hmain' hfarey with
    ⟨_hm, _hv₀, _hv₁, hsum, _hcoefficient, hmLower, _hmUpper⟩
  have hhUpper := (mem_intRange_four_mul hH₀ hh).2
  have hnum : x * (h : ℝ) ≤ x * (4 * H) :=
    mul_le_mul_of_nonneg_left hhUpper hx₀.le
  have hden : M ^ 3 ≤
      ((fareyPoint x a c : ℝ) + fareyFrac x a c) ^ 3 :=
    by
      rw [hsum]
      exact pow_le_pow_left₀ hM₀.le hmLower 3
  have hbetaUpper :
      betaIM x a c h ≤ x * (4 * H) / M ^ 3 := by
    rw [betaIM_eq_section8Beta hmain' hfarey]
    unfold section8Beta
    exact div_le_div₀ (by positivity) hnum (by positivity) hden
  have hG₁ := (iwaniecMozzochi_eq66_holds x H M hmain').1
  have hGinv : (Gscale x H M)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hG₁
  calc
    betaIM x a c h * shiftLength x M ≤
        (x * (4 * H) / M ^ 3) * shiftLength x M :=
      mul_le_mul_of_nonneg_right hbetaUpper hN₀.le
    _ = 4 * (x * H / M ^ 3 * shiftLength x M) := by ring
    _ = 4 * (Gscale x H M)⁻¹ := by rw [section8_gscale_inv]
    _ ≤ 4 * 1 := mul_le_mul_of_nonneg_left hGinv (by norm_num)
    _ = 4 := by ring

/-- The model lower bound used to replace `beta^-1/2` by the paper's
`(xH)^-1/2 M^3/2` scale.  It is independent of the short-cell hypothesis. -/
theorem x_mul_H_div_eight_mul_M_cube_le_betaIM
    {x H M : ℝ} {a c h : ℕ}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c)
    (hh : h ∈ intRange H (4 * H)) :
    x * H / (8 * M ^ 3) ≤ betaIM x a c h := by
  have hmain' : InMainRange x H M := hmain
  rcases hmain with ⟨hx, hxM, _hMx, hH, _hHupper, _hHlower, _hHlower₂, _hMlower⟩
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  have hM₀ : 0 < M := (Real.rpow_pos_of_pos hx₀ theta0).trans hxM
  have hH₀ : 0 < H := zero_lt_one.trans_le hH
  rcases fareyPoint_geometry hmain' hfarey with
    ⟨_hm, _hv₀, _hv₁, hsum, _hcoefficient, _hmLower, hmUpper⟩
  have hhLower := (mem_intRange_four_mul hH₀ hh).1.le
  have hnum : x * H ≤ x * (h : ℝ) :=
    mul_le_mul_of_nonneg_left hhLower hx₀.le
  have hden :
      ((fareyPoint x a c : ℝ) + fareyFrac x a c) ^ 3 ≤ (2 * M) ^ 3 :=
    by
      rw [hsum]
      exact pow_le_pow_left₀ (by positivity) hmUpper 3
  rw [betaIM_eq_section8Beta hmain' hfarey]
  unfold section8Beta
  calc
    x * H / (8 * M ^ 3) = x * H / (2 * M) ^ 3 := by ring
    _ ≤ x * (h : ℝ) /
        ((fareyPoint x a c : ℝ) + fareyFrac x a c) ^ 3 :=
      div_le_div₀ (by positivity) hnum (by positivity) hden

/-- Exact reciprocal phase expansion with the parameters as they occur in
`iwaniecMozzochi_eq84`. -/
theorem section8_farey_phase_decomposition
    {x H M : ℝ} {a c h : ℕ} (n : ℕ)
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c) :
    (h : ℝ) * x / ((fareyPoint x a c : ℝ) + n) =
      x * h / fareyPoint x a c + alphaIM x a c h * n +
        betaIM x a c h * (n : ℝ) ^ 2 +
          section8Remainder x h (fareyPoint x a c) (fareyFrac x a c) n := by
  rw [betaIM_eq_section8Beta hmain hfarey,
    alphaIM_eq_section8Alpha hmain hfarey]
  convert section8_phase_decomposition x (h : ℝ) (fareyPoint x a c)
    (fareyFrac x a c) n using 1 <;> ring

/-- Exponentiating the exact phase split produces precisely the perturbation
factor removed by partial summation in the paper. -/
theorem section8_farey_phase_factorization
    {x H M : ℝ} {a c h : ℕ} (n : ℕ)
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c) :
    e ((h : ℝ) * x / ((fareyPoint x a c : ℝ) + n)) =
      e (x * h / fareyPoint x a c) *
        e (alphaIM x a c h * n + betaIM x a c h * (n : ℝ) ^ 2) *
          e (section8Remainder x h (fareyPoint x a c) (fareyFrac x a c) n) := by
  rw [section8_farey_phase_decomposition n hmain hfarey]
  calc
    e (x * (h : ℝ) / fareyPoint x a c + alphaIM x a c h * n +
          betaIM x a c h * (n : ℝ) ^ 2 +
          section8Remainder x h (fareyPoint x a c) (fareyFrac x a c) n) =
        e ((x * h / fareyPoint x a c) +
            (alphaIM x a c h * n + betaIM x a c h * (n : ℝ) ^ 2) +
              section8Remainder x h (fareyPoint x a c) (fareyFrac x a c) n) := by
      congr 1
      ring
    _ = e (x * h / fareyPoint x a c) *
          e (alphaIM x a c h * n + betaIM x a c h * (n : ℝ) ^ 2) *
          e (section8Remainder x h (fareyPoint x a c) (fareyFrac x a c) n) := by
      rw [KL.e_add, KL.e_add]

/-! ## The common finite support of the two theta sums -/

/-- A finite range containing the support of `n |-> sigma(n/N)` for a Section
8 weight. -/
noncomputable def section8WeightRange (N : ℝ) : Finset ℕ :=
  Finset.range (⌊8 * N⌋₊ + 1)

/-- Exact lower and upper bounds for an active Section 8 weight. -/
theorem section8_weight_support_bounds
    {sigma : ℝ → ℝ} {N : ℝ} {n : ℕ}
    (hsigma : IsSmoothWeight sigma 4 8) (hN : 0 < N)
    (hn : sigma ((n : ℝ) / N) ≠ 0) :
    4 * N ≤ (n : ℝ) ∧ (n : ℝ) ≤ 8 * N := by
  have hsupp := hsigma.2.2 ((n : ℝ) / N) hn
  exact ⟨(le_div_iff₀ hN).1 hsupp.1, (div_le_iff₀ hN).1 hsupp.2⟩

/-- The natural support is contained in `section8WeightRange`. -/
theorem section8_weight_support_subset
    {sigma : ℝ → ℝ} {N : ℝ}
    (hsigma : IsSmoothWeight sigma 4 8) (hN : 0 < N) :
    Function.support (fun n : ℕ => sigma ((n : ℝ) / N)) ⊆
      (section8WeightRange N : Set ℕ) := by
  intro n hn
  have hnUpper := (section8_weight_support_bounds hsigma hN hn).2
  have heightN : 0 ≤ 8 * N := by positivity
  have hnFloor : n ≤ ⌊8 * N⌋₊ := (Nat.le_floor_iff heightN).2 hnUpper
  have hnMem : n ∈ section8WeightRange N := by
    rw [section8WeightRange, Finset.mem_range]
    omega
  simpa only [Finset.mem_coe] using hnMem

/-- The selected shift length is positive throughout the main range. -/
theorem section8_shiftLength_pos
    {x H M : ℝ} (hmain : InMainRange x H M) :
    0 < shiftLength x M := by
  rcases hmain with ⟨hx, hxM, _hMx, _hH, _hHupper, _hHlower, _hHlower₂, _hMlower⟩
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  have hM₀ : 0 < M := (Real.rpow_pos_of_pos hx₀ theta0).trans hxM
  unfold shiftLength
  exact mul_pos hM₀ (Real.rpow_pos_of_pos hx₀ _)

/-- The Section 8 displacement scale never exceeds the Farey scale.  Together
with `half_M_le_fareyPoint`, this puts every supported `n` and every moving
denominator on a fixed multiple of `M`. -/
theorem section8_shiftLength_le_M
    {x H M : ℝ} (hmain : InMainRange x H M) :
    shiftLength x M ≤ M := by
  rcases hmain with ⟨hx, hxM, _hMx, _hH, _hHupper, _hHlower, _hHlower₂, _hMlower⟩
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  have hM₀ : 0 ≤ M := ((Real.rpow_pos_of_pos hx₀ theta0).trans hxM).le
  have hexponent : -(2 : ℝ) / 5 * (1 - theta0) ≤ 0 := by
    norm_num [theta0]
  unfold shiftLength
  calc
    M * x ^ (-(2 : ℝ) / 5 * (1 - theta0)) ≤ M * 1 :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_one_of_one_le_of_nonpos hx hexponent) hM₀
    _ = M := by ring

/-- In fact the shift length is at least one in the main range.  This is the
small-scale fact needed to handle the complementary (`2*beta > 1/4`) case of
the quadratic-sum estimate trivially. -/
theorem one_le_section8_shiftLength
    {x H M : ℝ} (hmain : InMainRange x H M) :
    1 ≤ shiftLength x M := by
  rcases hmain with ⟨hx, hxM, _hMx, hH, hHupper, _hHlower, _hHlower₂, _hMlower⟩
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  have hM₀ : 0 ≤ M :=
    ((Real.rpow_pos_of_pos hx₀ theta0).trans hxM).le
  have hrpow : x ^ (-theta0) ≤ x ^ (-(3 : ℝ) / 11) :=
    Real.rpow_le_rpow_of_exponent_le hx (by norm_num [theta0])
  have hshift : shiftLength x M = M * x ^ (-(3 : ℝ) / 11) := by
    unfold shiftLength
    congr 1
    norm_num [theta0]
  calc
    1 ≤ H := hH
    _ ≤ M * x ^ (-theta0) := hHupper
    _ ≤ M * x ^ (-(3 : ℝ) / 11) :=
      mul_le_mul_of_nonneg_left hrpow hM₀
    _ = shiftLength x M := hshift.symm

/-- A `Rsum` with a Section 8 weight is the indicated literal finite sum. -/
theorem Rsum_eq_sum_section8WeightRange
    {sigma : ℝ → ℝ} {x N : ℝ} {h m : ℕ}
    (hsigma : IsSmoothWeight sigma 4 8) (hN : 0 < N) :
    Rsum sigma x N h m =
      ∑ n ∈ section8WeightRange N,
        (sigma ((n : ℝ) / N) : ℂ) * e ((h : ℝ) * x / (m + n)) := by
  unfold Rsum
  apply finsum_eq_sum_of_support_subset
  intro n hn
  apply section8_weight_support_subset hsigma hN
  intro hzero
  apply hn
  simp [hzero]

/-- The incomplete theta sum with the same weight has exactly the same finite
support range. -/
theorem incompleteTheta_eq_sum_section8WeightRange
    {sigma : ℝ → ℝ} {N alpha beta : ℝ}
    (hsigma : IsSmoothWeight sigma 4 8) (hN : 0 < N) :
    incompleteTheta (fun t => sigma (t / N)) alpha beta =
      ∑ n ∈ section8WeightRange N,
        (sigma ((n : ℝ) / N) : ℂ) *
          e (alpha * n + beta * (n : ℝ) ^ 2) := by
  unfold incompleteTheta
  apply finsum_eq_sum_of_support_subset
  intro n hn
  apply section8_weight_support_subset hsigma hN
  intro hzero
  apply hn
  simp [hzero]

/-- On the effective support, both moving denominators are positive and the
paper's full support window is exactly `4N <= n <= 8N`. -/
theorem section8_effective_support_geometry
    {sigma : ℝ → ℝ} {x H M : ℝ} {a c : ℕ} {n : ℕ}
    (hsigma : IsSmoothWeight sigma 4 8)
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c)
    (hn : sigma ((n : ℝ) / shiftLength x M) ≠ 0) :
    0 < (fareyPoint x a c : ℝ) ∧
      M ≤ (fareyPoint x a c : ℝ) + fareyFrac x a c ∧
      (fareyPoint x a c : ℝ) + fareyFrac x a c ≤ 2 * M ∧
      0 < (fareyPoint x a c : ℝ) + n ∧
      4 * shiftLength x M ≤ (n : ℝ) ∧
      (n : ℝ) ≤ 8 * shiftLength x M := by
  rcases fareyPoint_geometry hmain hfarey with
    ⟨hm, _hv₀, _hv₁, hsum, _hcoefficient, hmLower, hmUpper⟩
  have hm₀ : 0 < (fareyPoint x a c : ℝ) := by exact_mod_cast hm
  have hsupport := section8_weight_support_bounds hsigma
    (section8_shiftLength_pos hmain) hn
  have hmLower' : M ≤ (fareyPoint x a c : ℝ) + fareyFrac x a c := by
    rw [hsum]
    exact hmLower
  have hmUpper' : (fareyPoint x a c : ℝ) + fareyFrac x a c ≤ 2 * M := by
    rw [hsum]
    exact hmUpper
  exact ⟨hm₀, hmLower', hmUpper', by positivity, hsupport⟩

/-! ## Exact reduction of (8.4) to the perturbation sum -/

/-- The original reciprocal sum equals the constant phase times the finite
quadratic sum with its exact remainder factor retained. -/
theorem Rsum_eq_section8_remainder_sum
    {sigma : ℝ → ℝ} {x H M : ℝ} {a c h : ℕ}
    (hsigma : IsSmoothWeight sigma 4 8)
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c) :
    Rsum sigma x (shiftLength x M) h (fareyPoint x a c) =
      e (x * h / fareyPoint x a c) *
        ∑ n ∈ section8WeightRange (shiftLength x M),
          (sigma ((n : ℝ) / shiftLength x M) : ℂ) *
            e (alphaIM x a c h * n + betaIM x a c h * (n : ℝ) ^ 2) *
              e (section8Remainder x h (fareyPoint x a c)
                (fareyFrac x a c) n) := by
  rw [Rsum_eq_sum_section8WeightRange hsigma (section8_shiftLength_pos hmain),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _hn => ?_
  rw [section8_farey_phase_factorization n hmain hfarey]
  ring

/-- This is the exact finite sum whose norm must be bounded by `C*x^(1/44)`
to finish (8.4).  It makes the dependency on the single fixed weight explicit
and introduces no stronger hypothesis than the target proposition. -/
theorem section8_error_eq_perturbation_sum
    {sigma : ℝ → ℝ} {x H M : ℝ} {a c h : ℕ}
    (hsigma : IsSmoothWeight sigma 4 8)
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c) :
    Rsum sigma x (shiftLength x M) h (fareyPoint x a c) -
        e (x * h / fareyPoint x a c) *
          incompleteTheta (fun t => sigma (t / shiftLength x M))
            (alphaIM x a c h) (betaIM x a c h) =
      e (x * h / fareyPoint x a c) *
        ∑ n ∈ section8WeightRange (shiftLength x M),
          (sigma ((n : ℝ) / shiftLength x M) : ℂ) *
            e (alphaIM x a c h * n + betaIM x a c h * (n : ℝ) ^ 2) *
              (e (section8Remainder x h (fareyPoint x a c)
                (fareyFrac x a c) n) - 1) := by
  rw [Rsum_eq_section8_remainder_sum hsigma hmain hfarey,
    incompleteTheta_eq_sum_section8WeightRange hsigma
      (section8_shiftLength_pos hmain)]
  calc
    e (x * (h : ℝ) / fareyPoint x a c) *
          (∑ n ∈ section8WeightRange (shiftLength x M),
            (sigma ((n : ℝ) / shiftLength x M) : ℂ) *
              e (alphaIM x a c h * n + betaIM x a c h * (n : ℝ) ^ 2) *
                e (section8Remainder x h (fareyPoint x a c)
                  (fareyFrac x a c) n)) -
        e (x * h / fareyPoint x a c) *
          (∑ n ∈ section8WeightRange (shiftLength x M),
            (sigma ((n : ℝ) / shiftLength x M) : ℂ) *
              e (alphaIM x a c h * n + betaIM x a c h * (n : ℝ) ^ 2)) =
      e (x * h / fareyPoint x a c) *
        ((∑ n ∈ section8WeightRange (shiftLength x M),
            (sigma ((n : ℝ) / shiftLength x M) : ℂ) *
              e (alphaIM x a c h * n + betaIM x a c h * (n : ℝ) ^ 2) *
                e (section8Remainder x h (fareyPoint x a c)
                  (fareyFrac x a c) n)) -
          ∑ n ∈ section8WeightRange (shiftLength x M),
            (sigma ((n : ℝ) / shiftLength x M) : ℂ) *
              e (alphaIM x a c h * n + betaIM x a c h * (n : ℝ) ^ 2)) := by
        ring
    _ = e (x * h / fareyPoint x a c) *
        ∑ n ∈ section8WeightRange (shiftLength x M),
          ((sigma ((n : ℝ) / shiftLength x M) : ℂ) *
              e (alphaIM x a c h * n + betaIM x a c h * (n : ℝ) ^ 2) *
                e (section8Remainder x h (fareyPoint x a c)
                  (fareyFrac x a c) n) -
            (sigma ((n : ℝ) / shiftLength x M) : ℂ) *
              e (alphaIM x a c h * n + betaIM x a c h * (n : ℝ) ^ 2)) := by
        rw [← Finset.sum_sub_distrib]
    _ = e (x * h / fareyPoint x a c) *
        ∑ n ∈ section8WeightRange (shiftLength x M),
          (sigma ((n : ℝ) / shiftLength x M) : ℂ) *
            e (alphaIM x a c h * n + betaIM x a c h * (n : ℝ) ^ 2) *
              (e (section8Remainder x h (fareyPoint x a c)
                (fareyFrac x a c) n) - 1) := by
        congr 1
        refine Finset.sum_congr rfl fun n _hn => ?_
        ring

/-! ## The quadratic cancellation input -/

/-- The real quadratic phase used in the incomplete theta sum. -/
noncomputable def section8QuadraticPhase (alpha beta t : ℝ) : ℝ :=
  alpha * t + beta * t ^ 2

theorem section8QuadraticPhase_contDiff_two (alpha beta : ℝ) :
    ContDiff ℝ 2 (section8QuadraticPhase alpha beta) := by
  unfold section8QuadraticPhase
  fun_prop

theorem section8QuadraticPhase_hasDerivAt (alpha beta t : ℝ) :
    HasDerivAt (section8QuadraticPhase alpha beta)
      (alpha + 2 * beta * t) t := by
  unfold section8QuadraticPhase
  have hlin : HasDerivAt (fun y : ℝ => alpha * y) alpha t := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id t).const_mul alpha
  have hquad : HasDerivAt (fun y : ℝ => beta * y ^ 2) (beta * (2 * t)) t := by
    simpa [Pi.pow_apply] using ((hasDerivAt_id t).pow 2).const_mul beta
  convert hlin.add hquad using 1 <;> (first | rfl | ring)

theorem section8QuadraticPhase_deriv (alpha beta t : ℝ) :
    deriv (section8QuadraticPhase alpha beta) t = alpha + 2 * beta * t :=
  (section8QuadraticPhase_hasDerivAt alpha beta t).deriv

/-- The second derivative is the constant `2*beta`, with no exceptional
points. -/
theorem section8QuadraticPhase_deriv_two (alpha beta t : ℝ) :
    deriv (deriv (section8QuadraticPhase alpha beta)) t = 2 * beta := by
  have hfun : deriv (section8QuadraticPhase alpha beta) =
      fun y : ℝ => alpha + 2 * beta * y := by
    funext y
    exact section8QuadraticPhase_deriv alpha beta y
  rw [hfun]
  simpa using ((hasDerivAt_const t alpha).add
    ((hasDerivAt_id t).const_mul (2 * beta))).deriv

/-- Direct bridge from the quadratic phase to the repository's
van-der-Corput second-derivative theorem.  This is the small-curvature case of
the incomplete quadratic-sum estimate cited after (8.3). -/
theorem section8_quadratic_sum_vdc
    (alpha beta : ℝ) (A B : ℕ) (hbeta : 0 < beta)
    (hsmall : 2 * beta ≤ 1 / 4) :
    ‖∑ n ∈ Finset.Ioc A B, e (section8QuadraticPhase alpha beta n)‖ ≤
      12 * ((B - A : ℕ) : ℝ) * Real.sqrt (2 * beta) +
        24 / Real.sqrt (2 * beta) := by
  have hvdc := VdC.second_derivative (section8QuadraticPhase alpha beta)
    (section8QuadraticPhase_contDiff_two alpha beta)
    A B (2 * beta) 1 (by positivity) hsmall (by norm_num) fun t _ht => by
      rw [section8QuadraticPhase_deriv_two]
      constructor
      · exact le_rfl
      · simpa only [one_mul] using (le_rfl : 2 * beta ≤ 2 * beta)
  simpa [mul_assoc] using hvdc

/-- The complementary large-curvature regime is reduced to interval length
by the triangle inequality.  Together with `beta*N <= 4` and `N >= 1`, this
is the elementary companion to `section8_quadratic_sum_vdc`. -/
theorem section8_quadratic_sum_trivial
    (alpha beta : ℝ) (A B : ℕ) :
    ‖∑ n ∈ Finset.Ioc A B, e (section8QuadraticPhase alpha beta n)‖ ≤
      ((B - A : ℕ) : ℝ) := by
  calc
    ‖∑ n ∈ Finset.Ioc A B, e (section8QuadraticPhase alpha beta n)‖ ≤
        ∑ n ∈ Finset.Ioc A B, ‖e (section8QuadraticPhase alpha beta n)‖ :=
      norm_sum_le _ _
    _ = ((Finset.Ioc A B).card : ℝ) := by simp [norm_e]
    _ = ((B - A : ℕ) : ℝ) := by rw [Nat.card_Ioc]

/-! ## The terminal exponent arithmetic -/

/-- The final exponent comparison in the paper has constant exactly one:
`M*x^(-7(1-theta)/10) <= x^(1/44)` follows immediately from `M<x^1/2`. -/
theorem section8_final_scale_le
    {x H M : ℝ} (hmain : InMainRange x H M) :
    M * x ^ (-(7 : ℝ) / 10 * (1 - theta0)) ≤ x ^ ((1 : ℝ) / 44) := by
  rcases hmain with ⟨hx, _hxM, hMx, _hH, _hHupper, _hHlower, _hHlower₂, _hMlower⟩
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  have hfactor : 0 ≤ x ^ (-(7 : ℝ) / 10 * (1 - theta0)) :=
    Real.rpow_nonneg hx₀.le _
  calc
    M * x ^ (-(7 : ℝ) / 10 * (1 - theta0)) ≤
        x ^ ((1 : ℝ) / 2) * x ^ (-(7 : ℝ) / 10 * (1 - theta0)) :=
      mul_le_mul_of_nonneg_right hMx.le hfactor
    _ = x ^ ((1 : ℝ) / 44) := by
      rw [← Real.rpow_add hx₀]
      congr 1
      norm_num [theta0]

end LeanProofs.IntegerPoints
