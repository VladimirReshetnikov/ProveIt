import FabiusFunction.QuarterSplineLocalPolynomial

/-!
# The two-sided quarter polynomial of the finite Fabius spline

`QuarterSplineLocalPolynomial` proves the exact spline identity throughout the
closed dyadic cell around `1/4`.  This module packages that semantic theorem in
the symmetric `|z| ≤ radius` language of the inverse-frontier report.

For the repository index `m + 2`, the cutoff in `fabiusUniformSpline` at
`x = 1/4 + z` is

`floor (2^m + 2^(m+2) z + 1/2)`.

It equals `2^m` on the left-closed, right-open cell and becomes `2^m + 1`
only at the right endpoint, where the added positive-degree term is zero.
The Thue--Morse moment extraction and this cutoff calculation are centralized
in `QuarterSplineLocalPolynomial`; no algebra is duplicated here.

The symmetric packaging makes three further facts transparent on the same
cell.  Reflection about `1/4` has exact difference `2z`, the centered second
difference is `8z^2`, and the spline is strictly increasing on the full cell.
The last statement uses the sharp quadratic threshold `radius <= 1/8`, met by
every report depth `n >= 3`.
-/

set_option autoImplicit false

open Set

namespace Fabius

noncomputable section

/-- A function has the report's quarter quadratic throughout a symmetric
closed cell. -/
def IsQuarterTwoSidedLocalPolynomial
    (P : ℝ → ℝ) (Q radius : ℝ) : Prop :=
  ∀ z, |z| ≤ radius →
    P (1 / 4 + z) = 5 / 72 + z + 4 * z ^ 2 - (4 / 9) * Q

/-- Interval form of the symmetric local-polynomial predicate.  This is often
more convenient when a point is already known to lie in the closed cell. -/
theorem IsQuarterTwoSidedLocalPolynomial.iff_forall_mem_Icc
    {P : ℝ → ℝ} {Q radius : ℝ} :
    IsQuarterTwoSidedLocalPolynomial P Q radius ↔
      ∀ z ∈ Icc (-radius) radius,
        P (1 / 4 + z) = 5 / 72 + z + 4 * z ^ 2 - (4 / 9) * Q := by
  constructor
  · intro hlocal z hz
    exact hlocal z (abs_le.mpr hz)
  · intro hlocal z hz
    exact hlocal z (abs_le.mp hz)

/-- The odd part of every two-sided quarter polynomial is exactly linear:

`P(1/4+z) - P(1/4-z) = 2z`.

The finite-depth correction and the quadratic term are both even, so they
cancel without any hypothesis on `Q`. -/
theorem IsQuarterTwoSidedLocalPolynomial.reflection
    {P : ℝ → ℝ} {Q radius z : ℝ}
    (hlocal : IsQuarterTwoSidedLocalPolynomial P Q radius)
    (hz : |z| ≤ radius) :
    P (1 / 4 + z) - P (1 / 4 - z) = 2 * z := by
  have hzneg : |-z| ≤ radius := by simpa only [abs_neg] using hz
  rw [hlocal z hz,
    show (1 / 4 : ℝ) - z = 1 / 4 + (-z) by ring,
    hlocal (-z) hzneg]
  ring

/-- The centered second difference is the universal quadratic `8 z^2`:

`P(1/4+z) + P(1/4-z) - 2 P(1/4) = 8 z^2`.

In particular it is independent of both the depth parameter `Q` and the cell
radius. -/
theorem IsQuarterTwoSidedLocalPolynomial.centralSecondDifference
    {P : ℝ → ℝ} {Q radius z : ℝ}
    (hlocal : IsQuarterTwoSidedLocalPolynomial P Q radius)
    (hz : |z| ≤ radius) :
    P (1 / 4 + z) + P (1 / 4 - z) - 2 * P (1 / 4) = 8 * z ^ 2 := by
  have hzneg : |-z| ≤ radius := by simpa only [abs_neg] using hz
  have hradius : 0 ≤ radius := (abs_nonneg z).trans hz
  have hzero : |(0 : ℝ)| ≤ radius := by simpa using hradius
  rw [hlocal z hz,
    show (1 / 4 : ℝ) - z = 1 / 4 + (-z) by ring,
    hlocal (-z) hzneg,
    show (1 / 4 : ℝ) = 1 / 4 + 0 by ring,
    hlocal 0 hzero]
  ring

/-- A two-sided quarter polynomial is strictly increasing on its full cell as
soon as the radius is at most the vertex distance `1/8`.  This threshold is
sharp for the quadratic: its derivative vanishes at the left endpoint when
`radius = 1/8`, but the function remains strictly increasing there. -/
theorem IsQuarterTwoSidedLocalPolynomial.strictMonoOn
    {P : ℝ → ℝ} {Q radius : ℝ}
    (hlocal : IsQuarterTwoSidedLocalPolynomial P Q radius)
    (hradius : radius ≤ 1 / 8) :
    StrictMonoOn P
      (Icc (1 / 4 - radius : ℝ) (1 / 4 + radius)) := by
  intro x hx y hy hxy
  let u : ℝ := x - 1 / 4
  let v : ℝ := y - 1 / 4
  have hu : u ∈ Icc (-radius) radius := by
    dsimp only [u]
    constructor <;> linarith [hx.1, hx.2]
  have hv : v ∈ Icc (-radius) radius := by
    dsimp only [v]
    constructor <;> linarith [hy.1, hy.2]
  have hxu : x = 1 / 4 + u := by dsimp only [u]; ring
  have hyv : y = 1 / 4 + v := by dsimp only [v]; ring
  rw [hxu, hyv, hlocal u (abs_le.mpr hu), hlocal v (abs_le.mpr hv)]
  have huv : 0 < v - u := by dsimp only [u, v]; linarith
  have hfactor : 0 < (v - u) * (1 + 4 * (u + v)) := by
    apply mul_pos huv
    nlinarith [hu.1, hradius]
  nlinarith

/-- The degree-`m+2` repository spline has the exact quarter quadratic on the
whole closed cell of radius `2^-(m+3)`. -/
theorem fabiusUniformSpline_isQuarterTwoSidedLocalPolynomial (m : ℕ) :
    IsQuarterTwoSidedLocalPolynomial (fabiusUniformSpline (m + 2))
      (((4 : ℝ) ^ (m + 3))⁻¹) (((2 : ℝ) ^ (m + 3))⁻¹) := by
  intro z hz
  exact fabiusUniformSpline_quarter_eq_quadratic m (abs_le.mp hz)

/-- For every report depth `n >= 3`, its finite approximant `P_n` has the
exact quarter quadratic on the whole closed cell `|z| <= 2^-n`. -/
theorem reportFiniteFabiusApproximant_isQuarterTwoSidedLocalPolynomial
    {n : ℕ} (hn : 3 ≤ n) :
    IsQuarterTwoSidedLocalPolynomial (reportFiniteFabiusApproximant n)
      (((4 : ℝ) ^ n)⁻¹) (((2 : ℝ) ^ n)⁻¹) := by
  intro z hz
  exact reportFiniteFabiusApproximant_quarter_eq_quadratic hn (abs_le.mp hz)

/-- Pointwise form of the report's two-sided quarter-cell identity. -/
theorem reportFiniteFabiusApproximant_quarter_twoSided
    (n : ℕ) (hn : 3 ≤ n) {z : ℝ}
    (hz : |z| ≤ ((2 : ℝ) ^ n)⁻¹) :
    reportFiniteFabiusApproximant n (1 / 4 + z) =
      5 / 72 + z + 4 * z ^ 2 - (4 / 9) * ((4 : ℝ) ^ n)⁻¹ :=
  reportFiniteFabiusApproximant_isQuarterTwoSidedLocalPolynomial hn z hz

/-- Exact antisymmetry of the finite spline about the quarter anchor, after
subtracting its affine part. -/
theorem reportFiniteFabiusApproximant_quarter_reflection
    (n : ℕ) (hn : 3 ≤ n) {z : ℝ}
    (hz : |z| ≤ ((2 : ℝ) ^ n)⁻¹) :
    reportFiniteFabiusApproximant n (1 / 4 + z) -
        reportFiniteFabiusApproximant n (1 / 4 - z) =
      2 * z :=
  (reportFiniteFabiusApproximant_isQuarterTwoSidedLocalPolynomial hn).reflection hz

/-- Exact centered second difference of the finite spline throughout the
quarter cell.  It is independent of the finite-depth correction. -/
theorem reportFiniteFabiusApproximant_quarter_centralSecondDifference
    (n : ℕ) (hn : 3 ≤ n) {z : ℝ}
    (hz : |z| ≤ ((2 : ℝ) ^ n)⁻¹) :
    reportFiniteFabiusApproximant n (1 / 4 + z) +
          reportFiniteFabiusApproximant n (1 / 4 - z) -
        2 * reportFiniteFabiusApproximant n (1 / 4) =
      8 * z ^ 2 :=
  (reportFiniteFabiusApproximant_isQuarterTwoSidedLocalPolynomial hn).centralSecondDifference hz

/-- For every report depth `n >= 3`, the finite spline is strictly increasing
on the *entire* closed quarter cell, not merely its nonnegative half. -/
theorem strictMonoOn_reportFiniteFabiusApproximant_quarter_twoSided
    (n : ℕ) (hn : 3 ≤ n) :
    StrictMonoOn (reportFiniteFabiusApproximant n)
      (Icc (1 / 4 - ((2 : ℝ) ^ n)⁻¹ : ℝ)
        (1 / 4 + ((2 : ℝ) ^ n)⁻¹)) := by
  apply
    (reportFiniteFabiusApproximant_isQuarterTwoSidedLocalPolynomial hn).strictMonoOn
  have hpow : (2 : ℝ) ^ 3 ≤ (2 : ℝ) ^ n :=
    pow_le_pow_right₀ (by norm_num) hn
  calc
    ((2 : ℝ) ^ n)⁻¹ ≤ ((2 : ℝ) ^ 3)⁻¹ :=
      (inv_le_inv₀ (by positivity) (by positivity)).2 hpow
    _ = 1 / 8 := by norm_num

/-- The two-sided predicate specializes to the original nonnegative local
predicate. -/
theorem IsQuarterTwoSidedLocalPolynomial.isQuarterLocalPolynomial
    {P : ℝ → ℝ} {Q radius : ℝ}
    (hlocal : IsQuarterTwoSidedLocalPolynomial P Q radius) :
    IsQuarterLocalPolynomial P Q radius := by
  intro z hz
  exact hlocal z (by simpa [abs_of_nonneg hz.1] using hz.2)

end

end Fabius
