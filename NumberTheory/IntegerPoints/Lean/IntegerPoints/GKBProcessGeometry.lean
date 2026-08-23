import IntegerPoints.GKLemma36
import IntegerPoints.GKLemma39Local

/-!
# Quantitative geometry for the Graham--Kolesnik B-process

This module turns the defining derivative estimates of `InGKClass` into the
fixed-scale hypotheses needed by Graham--Kolesnik Lemma 3.6.  For

`F = y N^(1-s)` and `L = y N^(-s)`,

the second, third, and fourth derivatives have respective scales
`F N^-2`, `F N^-3`, and `F N^-4`.  The constants below depend only on `s`.
The same estimates place the reversed endpoint derivatives
`alpha = f'(b)` and `beta = f'(a)` in a positive interval of size comparable
to `L`, with a ratio bounded solely in terms of `s`.  These are the geometric
facts used when Lemma 3.6 and the dyadic inverse-phase estimates are assembled
in the proof of the B-process.
-/

open Real Finset Set

namespace LeanProofs.IntegerPoints

namespace GKB

/-! ### Natural scales and fixed curvature constants -/

/-- The `F` parameter with respect to which the derivatives of a
Graham--Kolesnik phase have the scales required by Lemma 3.6. -/
noncomputable def phaseScale (N s y : ℝ) : ℝ := y * N ^ (1 - s)

/-- The natural first-derivative scale `L = y N^-s`. -/
noncomputable def dualScale (N s y : ℝ) : ℝ := y * N ^ (-s)

/-- Lower comparison constant for `-f''` on a dyadic interval. -/
noncomputable def curvatureLower (s : ℝ) : ℝ :=
  3 / 4 * s * (2 : ℝ) ^ (-s - 1)

/-- Upper comparison constant for `-f''` on a dyadic interval. -/
noncomputable def curvatureUpper (s : ℝ) : ℝ := 5 / 4 * s

/-- Uniform third-derivative constant. -/
noncomputable def curvatureThird (s : ℝ) : ℝ := 5 / 4 * s * (s + 1)

/-- Uniform fourth-derivative constant. -/
noncomputable def curvatureFourth (s : ℝ) : ℝ :=
  5 / 4 * s * (s + 1) * (s + 2)

/-- Lower endpoint-derivative constant. -/
noncomputable def endpointLower (s : ℝ) : ℝ :=
  3 / 4 * (2 : ℝ) ^ (-s)

/-- Upper endpoint-derivative constant. -/
noncomputable def endpointUpper : ℝ := 5 / 4

/-- A scale-independent upper bound for `beta / alpha`. -/
noncomputable def endpointRatio (s : ℝ) : ℝ :=
  5 / 3 * (2 : ℝ) ^ s

theorem phaseScale_pos {N s y : ℝ} (hN : 0 < N) (hy : 0 < y) :
    0 < phaseScale N s y := by
  unfold phaseScale
  positivity

theorem dualScale_pos {N s y : ℝ} (hN : 0 < N) (hy : 0 < y) :
    0 < dualScale N s y := by
  unfold dualScale
  positivity

theorem curvatureConstants_pos {s : ℝ} (hs : 0 < s) :
    0 < curvatureLower s ∧ 0 < curvatureUpper s ∧
      0 < curvatureThird s ∧ 0 < curvatureFourth s := by
  constructor
  · unfold curvatureLower
    positivity
  constructor
  · unfold curvatureUpper
    positivity
  constructor
  · unfold curvatureThird
    positivity
  · unfold curvatureFourth
    positivity

theorem endpointConstants_pos (s : ℝ) :
    0 < endpointLower s ∧ 0 < endpointUpper ∧ 0 < endpointRatio s := by
  constructor
  · unfold endpointLower
    positivity
  constructor
  · unfold endpointUpper
    norm_num
  · unfold endpointRatio
    positivity

/-- Multiplying `F` by an arbitrary real power of `N` combines the powers in
the expected way. -/
theorem phaseScale_mul_rpow {N s y r : ℝ} (hN : 0 < N) :
    phaseScale N s y * N ^ r = y * N ^ (1 - s + r) := by
  unfold phaseScale
  rw [mul_assoc, ← Real.rpow_add hN]

theorem phaseScale_mul_rpow_neg_two {N s y : ℝ} (hN : 0 < N) :
    phaseScale N s y * N ^ (-(2 : ℝ)) = y * N ^ (-s - 1) := by
  have he : 1 - s + (-(2 : ℝ)) = -s - 1 := by ring
  rw [phaseScale_mul_rpow hN, he]

theorem phaseScale_mul_rpow_neg_three {N s y : ℝ} (hN : 0 < N) :
    phaseScale N s y * N ^ (-(3 : ℝ)) = y * N ^ (-s - 2) := by
  have he : 1 - s + (-(3 : ℝ)) = -s - 2 := by ring
  rw [phaseScale_mul_rpow hN, he]

theorem phaseScale_mul_rpow_neg_four {N s y : ℝ} (hN : 0 < N) :
    phaseScale N s y * N ^ (-(4 : ℝ)) = y * N ^ (-s - 3) := by
  have he : 1 - s + (-(4 : ℝ)) = -s - 3 := by ring
  rw [phaseScale_mul_rpow hN, he]

/-- The combination `F N^-1` occurring inside the logarithmic error of
Lemma 3.6 is exactly the natural dual scale `L`. -/
theorem phaseScale_mul_inv {N s y : ℝ} (hN : 0 < N) :
    phaseScale N s y * N⁻¹ = dualScale N s y := by
  rw [← Real.rpow_neg_one]
  unfold dualScale
  have he : 1 - s + (-(1 : ℝ)) = -s := by ring
  rw [phaseScale_mul_rpow hN, he]

/-! ### Low-order class estimates in normalized form -/

/-- The order-one class estimate, written with `iteratedDeriv 2`. -/
theorem abs_iteratedDeriv_two_add_model_lt
    {N s y eps a b : ℝ} {P : ℕ} {f : ℝ → ℝ}
    (hP : 2 ≤ P) (hf : InGKClass N P s y eps a b f)
    {t : ℝ} (ht : t ∈ Icc a b) :
    |iteratedDeriv 2 f t + s * y * t ^ (-s - 1)| <
      eps * (s * y * t ^ (-s - 1)) := by
  rw [GK34.iteratedDeriv_two]
  exact GK39.abs_deriv_deriv_add_model_lt hP hf ht

/-- The order-two class estimate, with its rising coefficient expanded. -/
theorem abs_iteratedDeriv_three_sub_model_lt
    {N s y eps a b : ℝ} {P : ℕ} {f : ℝ → ℝ}
    (hP : 3 ≤ P) (hf : InGKClass N P s y eps a b f)
    {t : ℝ} (ht : t ∈ Icc a b) :
    |iteratedDeriv 3 f t -
        s * (s + 1) * y * t ^ (-s - 2)| <
      eps * (s * (s + 1) * y * t ^ (-s - 2)) := by
  have h := hf.2.2.2.2 2 (by omega) t ht
  norm_num [Finset.prod_range_succ] at h
  convert h using 1
  all_goals ring_nf

/-- The order-three class estimate, with its sign and rising coefficient
expanded. -/
theorem abs_iteratedDeriv_four_add_model_lt
    {N s y eps a b : ℝ} {P : ℕ} {f : ℝ → ℝ}
    (hP : 4 ≤ P) (hf : InGKClass N P s y eps a b f)
    {t : ℝ} (ht : t ∈ Icc a b) :
    |iteratedDeriv 4 f t +
        s * (s + 1) * (s + 2) * y * t ^ (-s - 3)| <
      eps * (s * (s + 1) * (s + 2) * y * t ^ (-s - 3)) := by
  have h := hf.2.2.2.2 3 (by omega) t ht
  norm_num [Finset.prod_range_succ] at h
  convert h using 1
  all_goals ring_nf

/-! The next three elementary inequalities isolate all uses of the numerical
restriction `eps ≤ 1/4`. -/

theorem neg_bounds_of_abs_add_model_lt {d M eps : ℝ}
    (hM : 0 ≤ M) (heps : eps ≤ 1 / 4)
    (h : |d + M| < eps * M) :
    3 / 4 * M ≤ -d ∧ -d ≤ 5 / 4 * M := by
  have hepsM : eps * M ≤ 1 / 4 * M :=
    mul_le_mul_of_nonneg_right heps hM
  have habs := abs_lt.mp h
  constructor <;> linarith

theorem abs_le_of_abs_sub_model_lt {d M eps : ℝ}
    (hM : 0 ≤ M) (heps : eps ≤ 1 / 4)
    (h : |d - M| < eps * M) :
    |d| ≤ 5 / 4 * M := by
  have hepsM : eps * M ≤ 1 / 4 * M :=
    mul_le_mul_of_nonneg_right heps hM
  have habs := abs_lt.mp h
  have hd : 0 ≤ d := by linarith
  rw [abs_of_nonneg hd]
  linarith

theorem abs_le_of_abs_add_model_lt {d M eps : ℝ}
    (hM : 0 ≤ M) (heps : eps ≤ 1 / 4)
    (h : |d + M| < eps * M) :
    |d| ≤ 5 / 4 * M := by
  have hepsM : eps * M ≤ 1 / 4 * M :=
    mul_le_mul_of_nonneg_right heps hM
  have habs := abs_lt.mp h
  have hd : d ≤ 0 := by linarith
  rw [abs_of_nonpos hd]
  linarith

/-! ### Curvature on the class interval -/

/-- The second derivative satisfies the two-sided scale comparison required
by Lemma 3.6. -/
theorem second_derivative_bounds
    {N s y eps a b : ℝ} {P : ℕ} {f : ℝ → ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y)
    (hP : 4 ≤ P) (heps : eps ≤ 1 / 4)
    (hf : InGKClass N P s y eps a b f) :
    ∀ t ∈ Icc a b,
      curvatureLower s * phaseScale N s y * N ^ (-(2 : ℝ)) ≤
          -iteratedDeriv 2 f t ∧
        -iteratedDeriv 2 f t ≤
          curvatureUpper s * phaseScale N s y * N ^ (-(2 : ℝ)) := by
  intro t ht
  have ht0 : 0 < t := GK39.point_pos hN hf ht
  have htN : N ≤ t := hf.1.trans ht.1
  have ht2N : t ≤ 2 * N := ht.2.trans hf.2.2.1
  have hpowLower : (2 * N) ^ (-s - 1) ≤ t ^ (-s - 1) :=
    Real.rpow_le_rpow_of_nonpos ht0 ht2N (by linarith)
  have hpowUpper : t ^ (-s - 1) ≤ N ^ (-s - 1) :=
    Real.rpow_le_rpow_of_nonpos hN htN (by linarith)
  have hmodel0 : 0 ≤ s * y * t ^ (-s - 1) := by positivity
  have hpoint := neg_bounds_of_abs_add_model_lt hmodel0 heps
    (abs_iteratedDeriv_two_add_model_lt (by omega) hf ht)
  have hmodelLower :
      s * y * (2 * N) ^ (-s - 1) ≤ s * y * t ^ (-s - 1) :=
    mul_le_mul_of_nonneg_left hpowLower (by positivity)
  have hmodelUpper :
      s * y * t ^ (-s - 1) ≤ s * y * N ^ (-s - 1) :=
    mul_le_mul_of_nonneg_left hpowUpper (by positivity)
  have hsplit : (2 * N) ^ (-s - 1) =
      (2 : ℝ) ^ (-s - 1) * N ^ (-s - 1) :=
    Real.mul_rpow (by norm_num) hN.le
  constructor
  · calc
      curvatureLower s * phaseScale N s y * N ^ (-(2 : ℝ)) =
          curvatureLower s * (phaseScale N s y * N ^ (-(2 : ℝ))) := by ring
      _ = curvatureLower s * (y * N ^ (-s - 1)) := by
        rw [phaseScale_mul_rpow_neg_two hN]
      _ = 3 / 4 * (s * y * (2 * N) ^ (-s - 1)) := by
        rw [hsplit]
        unfold curvatureLower
        ring
      _ ≤ 3 / 4 * (s * y * t ^ (-s - 1)) :=
        mul_le_mul_of_nonneg_left hmodelLower (by norm_num)
      _ ≤ -iteratedDeriv 2 f t := hpoint.1
  · calc
      -iteratedDeriv 2 f t ≤
          5 / 4 * (s * y * t ^ (-s - 1)) := hpoint.2
      _ ≤ 5 / 4 * (s * y * N ^ (-s - 1)) :=
        mul_le_mul_of_nonneg_left hmodelUpper (by norm_num)
      _ = curvatureUpper s * (y * N ^ (-s - 1)) := by
        unfold curvatureUpper
        ring
      _ = curvatureUpper s *
          (phaseScale N s y * N ^ (-(2 : ℝ))) := by
        rw [phaseScale_mul_rpow_neg_two hN]
      _ = curvatureUpper s * phaseScale N s y * N ^ (-(2 : ℝ)) := by ring

/-- The class third derivative has the `F N^-3` upper bound required by
Lemma 3.6. -/
theorem third_derivative_bound
    {N s y eps a b : ℝ} {P : ℕ} {f : ℝ → ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y)
    (hP : 4 ≤ P) (heps : eps ≤ 1 / 4)
    (hf : InGKClass N P s y eps a b f) :
    ∀ t ∈ Icc a b,
      |iteratedDeriv 3 f t| ≤
        curvatureThird s * phaseScale N s y * N ^ (-(3 : ℝ)) := by
  intro t ht
  have ht0 : 0 < t := GK39.point_pos hN hf ht
  have htN : N ≤ t := hf.1.trans ht.1
  have hpowUpper : t ^ (-s - 2) ≤ N ^ (-s - 2) :=
    Real.rpow_le_rpow_of_nonpos hN htN (by linarith)
  have hmodel0 : 0 ≤ s * (s + 1) * y * t ^ (-s - 2) := by
    positivity
  have hpoint := abs_le_of_abs_sub_model_lt hmodel0 heps
    (abs_iteratedDeriv_three_sub_model_lt (by omega) hf ht)
  have hmodelUpper :
      s * (s + 1) * y * t ^ (-s - 2) ≤
        s * (s + 1) * y * N ^ (-s - 2) :=
    mul_le_mul_of_nonneg_left hpowUpper (by positivity)
  calc
    |iteratedDeriv 3 f t| ≤
        5 / 4 * (s * (s + 1) * y * t ^ (-s - 2)) := hpoint
    _ ≤ 5 / 4 * (s * (s + 1) * y * N ^ (-s - 2)) :=
      mul_le_mul_of_nonneg_left hmodelUpper (by norm_num)
    _ = curvatureThird s * (y * N ^ (-s - 2)) := by
      unfold curvatureThird
      ring
    _ = curvatureThird s *
        (phaseScale N s y * N ^ (-(3 : ℝ))) := by
      rw [phaseScale_mul_rpow_neg_three hN]
    _ = curvatureThird s * phaseScale N s y * N ^ (-(3 : ℝ)) := by ring

/-- The class fourth derivative has the `F N^-4` upper bound required by
Lemma 3.6. -/
theorem fourth_derivative_bound
    {N s y eps a b : ℝ} {P : ℕ} {f : ℝ → ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y)
    (hP : 4 ≤ P) (heps : eps ≤ 1 / 4)
    (hf : InGKClass N P s y eps a b f) :
    ∀ t ∈ Icc a b,
      |iteratedDeriv 4 f t| ≤
        curvatureFourth s * phaseScale N s y * N ^ (-(4 : ℝ)) := by
  intro t ht
  have ht0 : 0 < t := GK39.point_pos hN hf ht
  have htN : N ≤ t := hf.1.trans ht.1
  have hpowUpper : t ^ (-s - 3) ≤ N ^ (-s - 3) :=
    Real.rpow_le_rpow_of_nonpos hN htN (by linarith)
  have hmodel0 :
      0 ≤ s * (s + 1) * (s + 2) * y * t ^ (-s - 3) := by
    positivity
  have hpoint := abs_le_of_abs_add_model_lt hmodel0 heps
    (abs_iteratedDeriv_four_add_model_lt (by omega) hf ht)
  have hmodelUpper :
      s * (s + 1) * (s + 2) * y * t ^ (-s - 3) ≤
        s * (s + 1) * (s + 2) * y * N ^ (-s - 3) :=
    mul_le_mul_of_nonneg_left hpowUpper (by positivity)
  calc
    |iteratedDeriv 4 f t| ≤
        5 / 4 * (s * (s + 1) * (s + 2) * y * t ^ (-s - 3)) := hpoint
    _ ≤ 5 / 4 *
        (s * (s + 1) * (s + 2) * y * N ^ (-s - 3)) :=
      mul_le_mul_of_nonneg_left hmodelUpper (by norm_num)
    _ = curvatureFourth s * (y * N ^ (-s - 3)) := by
      unfold curvatureFourth
      ring
    _ = curvatureFourth s *
        (phaseScale N s y * N ^ (-(4 : ℝ))) := by
      rw [phaseScale_mul_rpow_neg_four hN]
    _ = curvatureFourth s * phaseScale N s y * N ^ (-(4 : ℝ)) := by ring

/-- A class of order at least four has the regularity required by Lemma 3.6. -/
theorem contDiff_four
    {N s y eps a b : ℝ} {P : ℕ} {f : ℝ → ℝ}
    (hP : 4 ≤ P) (hf : InGKClass N P s y eps a b f) :
    ContDiff ℝ 4 f :=
  hf.2.2.2.1.of_le (by exact_mod_cast hP)

/-- The second derivative is strictly negative on the full class interval.
This proof needs only `eps ≤ 1/4`; positivity of `eps` is not an additional
hypothesis. -/
theorem second_derivative_neg
    {N s y eps a b : ℝ} {P : ℕ} {f : ℝ → ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y)
    (hP : 4 ≤ P) (heps : eps ≤ 1 / 4)
    (hf : InGKClass N P s y eps a b f) :
    ∀ t ∈ Icc a b, iteratedDeriv 2 f t < 0 := by
  intro t ht
  have hbound := (second_derivative_bounds hN hs hy hP heps hf t ht).1
  have hpositive :
      0 < curvatureLower s * phaseScale N s y * N ^ (-(2 : ℝ)) := by
    have hc := (curvatureConstants_pos hs).1
    have hF := phaseScale_pos (s := s) hN hy
    positivity
  linarith

/-- All interval, regularity, and derivative hypotheses supplied to Lemma 3.6,
with constants depending only on `s`, in one reusable package. -/
theorem lemma36_geometry
    {N s y eps a b : ℝ} {P : ℕ} {f : ℝ → ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y)
    (hP : 4 ≤ P) (heps : eps ≤ 1 / 4)
    (hf : InGKClass N P s y eps a b f) :
    0 < phaseScale N s y ∧
      N ≤ a ∧ a ≤ b ∧ b ≤ 2 * N ∧ ContDiff ℝ 4 f ∧
      (∀ t ∈ Icc a b,
        curvatureLower s * phaseScale N s y * N ^ (-(2 : ℝ)) ≤
            -iteratedDeriv 2 f t ∧
          -iteratedDeriv 2 f t ≤
            curvatureUpper s * phaseScale N s y * N ^ (-(2 : ℝ))) ∧
      (∀ t ∈ Icc a b, |iteratedDeriv 3 f t| ≤
        curvatureThird s * phaseScale N s y * N ^ (-(3 : ℝ))) ∧
      (∀ t ∈ Icc a b, |iteratedDeriv 4 f t| ≤
        curvatureFourth s * phaseScale N s y * N ^ (-(4 : ℝ))) := by
  exact ⟨phaseScale_pos hN hy, hf.1, hf.2.1, hf.2.2.1,
    contDiff_four hP hf, second_derivative_bounds hN hs hy hP heps hf,
    third_derivative_bound hN hs hy hP heps hf,
    fourth_derivative_bound hN hs hy hP heps hf⟩

/-! ### Endpoint derivatives and the stationary-frequency interval -/

/-- Every first derivative on the class interval lies between fixed multiples
of the natural scale `L`. -/
theorem derivative_bounds_of_mem_Icc
    {N s y eps a b : ℝ} {P : ℕ} {f : ℝ → ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y)
    (hP : 4 ≤ P) (heps : eps ≤ 1 / 4)
    (hf : InGKClass N P s y eps a b f)
    {t : ℝ} (ht : t ∈ Icc a b) :
    endpointLower s * dualScale N s y < deriv f t ∧
      deriv f t < endpointUpper * dualScale N s y := by
  have ht0 : 0 < t := GK39.point_pos hN hf ht
  have htN : N ≤ t := hf.1.trans ht.1
  have ht2N : t ≤ 2 * N := ht.2.trans hf.2.2.1
  have hpowLower : (2 * N) ^ (-s) ≤ t ^ (-s) :=
    Real.rpow_le_rpow_of_nonpos ht0 ht2N (by linarith)
  have hpowUpper : t ^ (-s) ≤ N ^ (-s) :=
    Real.rpow_le_rpow_of_nonpos hN htN (by linarith)
  have hmodel0 : 0 ≤ y * t ^ (-s) := by positivity
  have hmodelLower : y * (2 * N) ^ (-s) ≤ y * t ^ (-s) :=
    mul_le_mul_of_nonneg_left hpowLower hy.le
  have hmodelUpper : y * t ^ (-s) ≤ dualScale N s y := by
    unfold dualScale
    exact mul_le_mul_of_nonneg_left hpowUpper hy.le
  have hsplit : (2 * N) ^ (-s) =
      (2 : ℝ) ^ (-s) * N ^ (-s) :=
    Real.mul_rpow (by norm_num) hN.le
  have hscaledLower :
      (2 : ℝ) ^ (-s) * dualScale N s y ≤ y * t ^ (-s) := by
    rw [dualScale, ← mul_assoc, mul_comm ((2 : ℝ) ^ (-s)) y,
      mul_assoc, ← hsplit]
    exact hmodelLower
  have hepsModel : eps * (y * t ^ (-s)) ≤ 1 / 4 * (y * t ^ (-s)) :=
    mul_le_mul_of_nonneg_right heps hmodel0
  have happrox := abs_lt.mp
    (GK39.abs_deriv_sub_model_lt (by omega) hf ht)
  have hpointLower : 3 / 4 * (y * t ^ (-s)) < deriv f t := by
    linarith
  have hpointUpper : deriv f t < 5 / 4 * (y * t ^ (-s)) := by
    linarith
  constructor
  · calc
      endpointLower s * dualScale N s y =
          3 / 4 * ((2 : ℝ) ^ (-s) * dualScale N s y) := by
        unfold endpointLower
        ring
      _ ≤ 3 / 4 * (y * t ^ (-s)) :=
        mul_le_mul_of_nonneg_left hscaledLower (by norm_num)
      _ < deriv f t := hpointLower
  · calc
      deriv f t < 5 / 4 * (y * t ^ (-s)) := hpointUpper
      _ ≤ 5 / 4 * dualScale N s y :=
        mul_le_mul_of_nonneg_left hmodelUpper (by norm_num)
      _ = endpointUpper * dualScale N s y := by
        unfold endpointUpper
        rfl

/-- Quantitative endpoint geometry for `alpha = f'(b)` and `beta = f'(a)`.
In particular, both endpoints are positive and `alpha ≤ beta`. -/
theorem endpoint_derivative_bounds
    {N s y eps a b : ℝ} {P : ℕ} {f : ℝ → ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y)
    (hP : 4 ≤ P) (heps : eps ≤ 1 / 4)
    (hf : InGKClass N P s y eps a b f) :
    0 < dualScale N s y ∧
      endpointLower s * dualScale N s y < deriv f b ∧
      0 < deriv f b ∧ deriv f b ≤ deriv f a ∧
      deriv f a < endpointUpper * dualScale N s y := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hf.2.1⟩
  have hb : b ∈ Icc a b := ⟨hf.2.1, le_rfl⟩
  have haBounds := derivative_bounds_of_mem_Icc hN hs hy hP heps hf ha
  have hbBounds := derivative_bounds_of_mem_Icc hN hs hy hP heps hf hb
  have hLowerPos : 0 < endpointLower s * dualScale N s y := by
    have hc := (endpointConstants_pos s).1
    have hL := dualScale_pos (s := s) hN hy
    positivity
  have hf2 : ContDiff ℝ 2 f :=
    (contDiff_four hP hf).of_le (by norm_num)
  have hanti : AntitoneOn (deriv f) (Icc a b) :=
    GK36.deriv_antitoneOn hf2 fun t ht =>
      (second_derivative_neg hN hs hy hP heps hf t ht).le
  exact ⟨dualScale_pos hN hy, hbBounds.1,
    hLowerPos.trans hbBounds.1, hanti ha hb hf.2.1, haBounds.2⟩

/-- The derivative interval has length at most a fixed multiple of `L`. -/
theorem endpoint_span_bound
    {N s y eps a b : ℝ} {P : ℕ} {f : ℝ → ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y)
    (hP : 4 ≤ P) (heps : eps ≤ 1 / 4)
    (hf : InGKClass N P s y eps a b f) :
    0 ≤ deriv f a - deriv f b ∧
      deriv f a - deriv f b ≤ endpointUpper * dualScale N s y := by
  obtain ⟨_, _, hAlpha, hAlphaBeta, hBeta⟩ :=
    endpoint_derivative_bounds hN hs hy hP heps hf
  constructor <;> linarith

/-- The endpoint ratio is bounded by `(5/3) 2^s`.  Both the multiplicative
and quotient forms are recorded because they are used differently in dyadic
cover arguments. -/
theorem endpoint_ratio_bound
    {N s y eps a b : ℝ} {P : ℕ} {f : ℝ → ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y)
    (hP : 4 ≤ P) (heps : eps ≤ 1 / 4)
    (hf : InGKClass N P s y eps a b f) :
    deriv f a < endpointRatio s * deriv f b ∧
      deriv f a / deriv f b < endpointRatio s := by
  obtain ⟨hL, hAlphaLower, hAlpha, _, hBetaUpper⟩ :=
    endpoint_derivative_bounds hN hs hy hP heps hf
  have hRatioPos : 0 < endpointRatio s := (endpointConstants_pos s).2.2
  have hcancel : (2 : ℝ) ^ s * (2 : ℝ) ^ (-s) = 1 := by
    rw [← Real.rpow_add (by norm_num), add_neg_cancel, Real.rpow_zero]
  have hnormalize :
      endpointRatio s * (endpointLower s * dualScale N s y) =
        endpointUpper * dualScale N s y := by
    unfold endpointRatio endpointLower endpointUpper
    calc
      (5 / 3 * (2 : ℝ) ^ s) *
          ((3 / 4 * (2 : ℝ) ^ (-s)) * dualScale N s y) =
          5 / 4 * ((2 : ℝ) ^ s * (2 : ℝ) ^ (-s)) *
            dualScale N s y := by ring
      _ = 5 / 4 * dualScale N s y := by rw [hcancel]; ring
  have hmul : deriv f a < endpointRatio s * deriv f b := by
    calc
      deriv f a < endpointUpper * dualScale N s y := hBetaUpper
      _ = endpointRatio s *
          (endpointLower s * dualScale N s y) := hnormalize.symm
      _ < endpointRatio s * deriv f b :=
        mul_lt_mul_of_pos_left hAlphaLower hRatioPos
  exact ⟨hmul, (div_lt_iff₀ hAlpha).2 hmul⟩

/-- The stationary integer interval has at most `(5/4)L + 1` elements. -/
theorem stationary_card_bound
    {N s y eps a b : ℝ} {P : ℕ} {f : ℝ → ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y)
    (hP : 4 ≤ P) (heps : eps ≤ 1 / 4)
    (hf : InGKClass N P s y eps a b f) :
    ((Finset.Icc ⌈deriv f b⌉ ⌊deriv f a⌋).card : ℝ) ≤
      endpointUpper * dualScale N s y + 1 := by
  obtain ⟨_, _, hAlpha, hAlphaBeta, hBeta⟩ :=
    endpoint_derivative_bounds hN hs hy hP heps hf
  calc
    ((Finset.Icc ⌈deriv f b⌉ ⌊deriv f a⌋).card : ℝ) ≤
        deriv f a - deriv f b + 1 :=
      GK36.card_Icc_ceil_floor_le hAlphaBeta
    _ ≤ endpointUpper * dualScale N s y + 1 := by linarith

/-- Every stationary integer frequency is positive and lies below the same
fixed upper multiple of `L`. -/
theorem stationary_frequency_bounds
    {N s y eps a b : ℝ} {P : ℕ} {f : ℝ → ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y)
    (hP : 4 ≤ P) (heps : eps ≤ 1 / 4)
    (hf : InGKClass N P s y eps a b f)
    {nu : ℤ} (hnu : nu ∈ Finset.Icc ⌈deriv f b⌉ ⌊deriv f a⌋) :
    0 < (nu : ℝ) ∧ (nu : ℝ) < endpointUpper * dualScale N s y := by
  obtain ⟨_, _, hAlpha, _, hBeta⟩ :=
    endpoint_derivative_bounds hN hs hy hP heps hf
  have hnu' := Finset.mem_Icc.mp hnu
  have hceilNu : (⌈deriv f b⌉ : ℝ) ≤ (nu : ℝ) := by
    exact_mod_cast hnu'.1
  have hnuFloor : (nu : ℝ) ≤ (⌊deriv f a⌋ : ℝ) := by
    exact_mod_cast hnu'.2
  have hAlphaNu : deriv f b ≤ (nu : ℝ) :=
    (Int.le_ceil (deriv f b)).trans hceilNu
  have hNuBeta : (nu : ℝ) ≤ deriv f a :=
    hnuFloor.trans (Int.floor_le (deriv f a))
  constructor <;> linarith

end GKB

end LeanProofs.IntegerPoints
