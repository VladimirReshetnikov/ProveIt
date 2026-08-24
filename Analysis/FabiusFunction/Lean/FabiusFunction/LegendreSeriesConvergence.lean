import FabiusFunction.Differential
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Uniform convergence of Legendre series

This file supplies the analytic convergence layer for expansions in the
ordinary Legendre polynomials on `[-1, 1]`.  The starting point is the
self-adjoint Sturm--Liouville operator

`f ↦ -((1 - x²) f')'`.

The factor `1 - x²` makes both boundary terms vanish at `x = ±1`.
-/

set_option autoImplicit false

open scoped ContDiff Interval Polynomial
open Set MeasureTheory

namespace Fabius

/-- The Legendre Sturm--Liouville operator `-((1 - x²) f')'`. -/
noncomputable def legendreSturmLiouville (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  -deriv (fun y : ℝ ↦ (1 - y ^ 2) * deriv f y) x

private lemma contDiff_legendre_weight :
    ContDiff ℝ ∞ (fun x : ℝ ↦ 1 - x ^ 2) := by
  fun_prop

/-- The Legendre Sturm--Liouville operator preserves smoothness. -/
theorem ContDiff.legendreSturmLiouville {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (legendreSturmLiouville f) := by
  have hdf : ContDiff ℝ ∞ (deriv f) :=
    (contDiff_infty_iff_deriv.mp hf).2
  have hweighted : ContDiff ℝ ∞
      (fun x : ℝ ↦ (1 - x ^ 2) * deriv f x) :=
    contDiff_legendre_weight.mul hdf
  change ContDiff ℝ ∞
    (fun x : ℝ ↦ -deriv (fun y : ℝ ↦ (1 - y ^ 2) * deriv f y) x)
  exact (contDiff_infty_iff_deriv.mp hweighted).2.neg

private lemma legendre_weight_at_neg_one :
    (1 - (-1 : ℝ) ^ 2) = 0 := by norm_num

private lemma legendre_weight_at_one :
    (1 - (1 : ℝ) ^ 2) = 0 := by norm_num

/-- Green's identity for the Legendre Sturm--Liouville operator.

No endpoint flatness is needed: the boundary terms vanish because the weight
`1 - x²` itself is zero at both endpoints.
-/
theorem integral_mul_legendreSturmLiouville_eq
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    (∫ x in (-1 : ℝ)..1, f x * legendreSturmLiouville g x) =
      ∫ x in (-1 : ℝ)..1, legendreSturmLiouville f x * g x := by
  let w : ℝ → ℝ := fun x ↦ 1 - x ^ 2
  let vf : ℝ → ℝ := fun x ↦ w x * deriv f x
  let vg : ℝ → ℝ := fun x ↦ w x * deriv g x
  have hdf : ContDiff ℝ ∞ (deriv f) :=
    (contDiff_infty_iff_deriv.mp hf).2
  have hdg : ContDiff ℝ ∞ (deriv g) :=
    (contDiff_infty_iff_deriv.mp hg).2
  have hw : ContDiff ℝ ∞ w := by
    dsimp [w]
    exact contDiff_legendre_weight
  have hvf : ContDiff ℝ ∞ vf := by
    exact hw.mul hdf
  have hvg : ContDiff ℝ ∞ vg := by
    exact hw.mul hdg
  have hfDeriv : ∀ x ∈ [[(-1 : ℝ), 1]], HasDerivAt f (deriv f x) x := by
    intro x _hx
    exact (hf.differentiable (by simp) x).hasDerivAt
  have hgDeriv : ∀ x ∈ [[(-1 : ℝ), 1]], HasDerivAt g (deriv g x) x := by
    intro x _hx
    exact (hg.differentiable (by simp) x).hasDerivAt
  have hvfDeriv : ∀ x ∈ [[(-1 : ℝ), 1]], HasDerivAt vf (deriv vf x) x := by
    intro x _hx
    exact (hvf.differentiable (by simp) x).hasDerivAt
  have hvgDeriv : ∀ x ∈ [[(-1 : ℝ), 1]], HasDerivAt vg (deriv vg x) x := by
    intro x _hx
    exact (hvg.differentiable (by simp) x).hasDerivAt
  have hdfInt : IntervalIntegrable (deriv f) volume (-1 : ℝ) 1 :=
    hdf.continuous.intervalIntegrable _ _
  have hdgInt : IntervalIntegrable (deriv g) volume (-1 : ℝ) 1 :=
    hdg.continuous.intervalIntegrable _ _
  have hvfInt : IntervalIntegrable vf volume (-1 : ℝ) 1 :=
    hvf.continuous.intervalIntegrable _ _
  have hvgInt : IntervalIntegrable vg volume (-1 : ℝ) 1 :=
    hvg.continuous.intervalIntegrable _ _
  have hdvf : ContDiff ℝ ∞ (deriv vf) :=
    (contDiff_infty_iff_deriv.mp hvf).2
  have hdvg : ContDiff ℝ ∞ (deriv vg) :=
    (contDiff_infty_iff_deriv.mp hvg).2
  have hdvfInt : IntervalIntegrable (deriv vf) volume (-1 : ℝ) 1 :=
    hdvf.continuous.intervalIntegrable _ _
  have hdvgInt : IntervalIntegrable (deriv vg) volume (-1 : ℝ) 1 :=
    hdvg.continuous.intervalIntegrable _ _
  have hfirst := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hfDeriv hvgDeriv hdfInt hdvgInt
  have hsecond := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hvfDeriv hgDeriv hdvfInt hdgInt
  have hvfNeg : vf (-1) = 0 := by simp [vf, w]
  have hvfPos : vf 1 = 0 := by simp [vf, w]
  have hvgNeg : vg (-1) = 0 := by simp [vg, w]
  have hvgPos : vg 1 = 0 := by simp [vg, w]
  rw [hvgNeg, hvgPos, mul_zero, mul_zero, zero_sub] at hfirst
  rw [hvfNeg, hvfPos, zero_mul, zero_mul, zero_sub] at hsecond
  change (∫ x in (-1 : ℝ)..1, f x * (-deriv vg x)) =
    ∫ x in (-1 : ℝ)..1, (-deriv vf x) * g x
  simp_rw [mul_neg, neg_mul, intervalIntegral.integral_neg]
  have hfg : (∫ x in (-1 : ℝ)..1, deriv f x * vg x) =
      ∫ x in (-1 : ℝ)..1, vf x * deriv g x := by
    apply intervalIntegral.integral_congr
    intro x _hx
    simp only [vf, vg]
    ring
  rw [hfirst, hfg, hsecond]
  ring

/-! ## Decay of Legendre coefficients -/

/-- The normalized coefficient functional used for an eigenfunction of
Legendre degree `n`.  Specializing `p` to `P_n` gives the usual
Fourier--Legendre coefficient. -/
noncomputable def legendreSeriesCoefficientOf
    (f p : ℝ → ℝ) (n : ℕ) : ℝ :=
  ((2 * n + 1 : ℕ) : ℝ) / 2 *
    ∫ x in (-1 : ℝ)..1, f x * p x

/-- Moving a Legendre Sturm--Liouville eigenvalue across the integral. -/
theorem eigenvalue_mul_integral_eq_integral_legendreSturmLiouville
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (eigenvalue : ℝ)
    (heigen : ∀ x, legendreSturmLiouville g x = eigenvalue * g x) :
    eigenvalue * (∫ x in (-1 : ℝ)..1, f x * g x) =
      ∫ x in (-1 : ℝ)..1, legendreSturmLiouville f x * g x := by
  calc
    eigenvalue * (∫ x in (-1 : ℝ)..1, f x * g x) =
        ∫ x in (-1 : ℝ)..1, eigenvalue * (f x * g x) := by
          rw [intervalIntegral.integral_const_mul]
    _ = ∫ x in (-1 : ℝ)..1, f x * legendreSturmLiouville g x := by
      apply intervalIntegral.integral_congr
      intro x _hx
      change eigenvalue * (f x * g x) =
        f x * legendreSturmLiouville g x
      rw [heigen]
      ring
    _ = ∫ x in (-1 : ℝ)..1, legendreSturmLiouville f x * g x :=
      integral_mul_legendreSturmLiouville_eq hf hg

/-- Applying Green's identity twice transfers two powers of a
Sturm--Liouville eigenvalue from the Legendre polynomial to the function. -/
theorem eigenvalue_sq_mul_integral_eq_integral_legendreSturmLiouville_sq
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (eigenvalue : ℝ)
    (heigen : ∀ x, legendreSturmLiouville g x = eigenvalue * g x) :
    eigenvalue ^ 2 * (∫ x in (-1 : ℝ)..1, f x * g x) =
      ∫ x in (-1 : ℝ)..1,
        legendreSturmLiouville (legendreSturmLiouville f) x * g x := by
  have hfirst := eigenvalue_mul_integral_eq_integral_legendreSturmLiouville
    hf hg eigenvalue heigen
  have hLf := ContDiff.legendreSturmLiouville hf
  have hsecond := eigenvalue_mul_integral_eq_integral_legendreSturmLiouville
    hLf hg eigenvalue heigen
  calc
    eigenvalue ^ 2 * (∫ x in (-1 : ℝ)..1, f x * g x) =
        eigenvalue * (eigenvalue * (∫ x in (-1 : ℝ)..1, f x * g x)) := by ring
    _ = eigenvalue *
        (∫ x in (-1 : ℝ)..1, legendreSturmLiouville f x * g x) := by
      rw [hfirst]
    _ = ∫ x in (-1 : ℝ)..1,
        legendreSturmLiouville (legendreSturmLiouville f) x * g x := hsecond

/-- Two integrations by parts give the cubic decay estimate needed for
absolute convergence of a Legendre series.  The hypotheses isolate the three
standard facts about `P_m`: smoothness, the Sturm--Liouville eigenvalue
`m(m+1)`, and `|P_m| ≤ 1` on `[-1,1]`. -/
theorem pow_three_mul_abs_legendreSeriesCoefficientOf_le
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (m : ℕ) (hm : 1 ≤ m) (B : ℝ) (hB : 0 ≤ B)
    (heigen : ∀ x,
      legendreSturmLiouville g x =
        ((m : ℝ) * (m + 1 : ℝ)) * g x)
    (hgBound : ∀ x ∈ Icc (-1 : ℝ) 1, |g x| ≤ 1)
    (hLfBound : ∀ x ∈ Icc (-1 : ℝ) 1,
      |legendreSturmLiouville (legendreSturmLiouville f) x| ≤ B) :
    (m : ℝ) ^ 3 * |legendreSeriesCoefficientOf f g m| ≤ 3 * B := by
  let eigenvalue : ℝ := (m : ℝ) * (m + 1 : ℝ)
  let I : ℝ := ∫ x in (-1 : ℝ)..1, f x * g x
  let J : ℝ := ∫ x in (-1 : ℝ)..1,
    legendreSturmLiouville (legendreSturmLiouville f) x * g x
  have htransfer : eigenvalue ^ 2 * I = J := by
    dsimp [eigenvalue, I, J]
    exact eigenvalue_sq_mul_integral_eq_integral_legendreSturmLiouville_sq
      hf hg ((m : ℝ) * (m + 1 : ℝ)) heigen
  have hJBound : |J| ≤ 2 * B := by
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (-1 : ℝ)) (b := 1) (C := B)
      (f := fun x : ℝ ↦
        legendreSturmLiouville (legendreSturmLiouville f) x * g x)
      (fun x hx ↦ by
        have hxmem : x ∈ Icc (-1 : ℝ) 1 := by
          norm_num [min_def, max_def] at hx
          exact ⟨hx.1.le, hx.2⟩
        rw [Real.norm_eq_abs, abs_mul]
        simpa using mul_le_mul (hLfBound x hxmem) (hgBound x hxmem)
          (abs_nonneg _) hB)
    norm_num at hbound ⊢
    simpa [J, mul_assoc, mul_comm] using hbound
  have hmReal : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have heigen_nonneg : 0 ≤ eigenvalue := by
    dsimp [eigenvalue]
    positivity
  have hscaled : eigenvalue ^ 2 * |I| ≤ 2 * B := by
    have habs := congrArg abs htransfer
    have habsEq : eigenvalue ^ 2 * |I| = |J| := by
      rw [← habs]
      rw [abs_mul, abs_pow, abs_of_nonneg heigen_nonneg]
    rw [habsEq]
    exact hJBound
  have heigen_ge : (m : ℝ) ^ 4 ≤ eigenvalue ^ 2 := by
    have haux : 0 ≤ (m : ℝ) ^ 2 * (2 * (m : ℝ) + 1) := by positivity
    dsimp [eigenvalue]
    nlinarith
  have hm4 : (m : ℝ) ^ 4 * |I| ≤ 2 * B :=
    (mul_le_mul_of_nonneg_right heigen_ge (abs_nonneg I)).trans hscaled
  have hdegree : (((2 * m + 1 : ℕ) : ℝ)) ≤ 3 * (m : ℝ) := by
    push_cast
    nlinarith
  have hcoefficientAbs :
      |legendreSeriesCoefficientOf f g m| =
        (((2 * m + 1 : ℕ) : ℝ) / 2) * |I| := by
    rw [legendreSeriesCoefficientOf]
    change |(((2 * m + 1 : ℕ) : ℝ) / 2) * I| = _
    rw [abs_mul, abs_of_nonneg (by positivity)]
  rw [hcoefficientAbs]
  have hfactorNonneg :
      0 ≤ ((m : ℝ) ^ 3 / 2) * |I| := by positivity
  calc
    (m : ℝ) ^ 3 * ((((2 * m + 1 : ℕ) : ℝ) / 2) * |I|) =
        (((2 * m + 1 : ℕ) : ℝ)) * (((m : ℝ) ^ 3 / 2) * |I|) := by ring
    _ ≤ (3 * (m : ℝ)) * (((m : ℝ) ^ 3 / 2) * |I|) :=
      mul_le_mul_of_nonneg_right hdegree hfactorNonneg
    _ = (3 / 2 : ℝ) * ((m : ℝ) ^ 4 * |I|) := by ring
    _ ≤ (3 / 2 : ℝ) * (2 * B) :=
      mul_le_mul_of_nonneg_left hm4 (by norm_num)
    _ = 3 * B := by ring

/-! ## Uniform summation from summable coefficients -/

/-- Restrict a globally continuous real function to the Legendre interval. -/
def continuousMapOnLegendreInterval (f : ℝ → ℝ) (hf : Continuous f) :
    C(Icc (-1 : ℝ) 1, ℝ) :=
  ⟨fun x ↦ f x, hf.comp continuous_subtype_val⟩

@[simp]
theorem continuousMapOnLegendreInterval_apply
    (f : ℝ → ℝ) (hf : Continuous f) (x : Icc (-1 : ℝ) 1) :
    continuousMapOnLegendreInterval f hf x = f x :=
  rfl

/-- A summable scalar coefficient sequence times functions bounded by one on
`[-1,1]` is summable in the uniform norm on that interval. -/
theorem summable_continuousMapOnLegendreInterval_smul
    (p : ℕ → ℝ → ℝ) (hp : ∀ n, Continuous (p n))
    (hpBound : ∀ n x, x ∈ Icc (-1 : ℝ) 1 → |p n x| ≤ 1)
    (a : ℕ → ℝ) (ha : Summable fun n ↦ |a n|) :
    Summable fun n ↦
      a n • continuousMapOnLegendreInterval (p n) (hp n) := by
  apply Summable.of_norm_bounded ha
  intro n
  rw [norm_smul, Real.norm_eq_abs]
  have hpNorm : ‖continuousMapOnLegendreInterval (p n) (hp n)‖ ≤ 1 := by
    rw [ContinuousMap.norm_le _ zero_le_one]
    intro x
    simpa [Real.norm_eq_abs] using hpBound n x x.property
  calc
    |a n| * ‖continuousMapOnLegendreInterval (p n) (hp n)‖ ≤ |a n| * 1 :=
      mul_le_mul_of_nonneg_left hpNorm (abs_nonneg _)
    _ = |a n| := mul_one _

/-- Uniform `HasSum` on `[-1,1]`, packaged in the Banach space of continuous
maps.  Evaluation gives the corresponding pointwise `HasSum` theorem. -/
theorem hasSum_continuousMapOnLegendreInterval_smul
    (p : ℕ → ℝ → ℝ) (hp : ∀ n, Continuous (p n))
    (hpBound : ∀ n x, x ∈ Icc (-1 : ℝ) 1 → |p n x| ≤ 1)
    (a : ℕ → ℝ) (ha : Summable fun n ↦ |a n|) :
    HasSum (fun n ↦
      a n • continuousMapOnLegendreInterval (p n) (hp n))
      (∑' n, a n • continuousMapOnLegendreInterval (p n) (hp n)) :=
  (summable_continuousMapOnLegendreInterval_smul p hp hpBound a ha).hasSum

/-- Pointwise evaluation of the uniformly convergent series supplied by
`hasSum_continuousMapOnLegendreInterval_smul`. -/
theorem hasSum_eval_continuousMapOnLegendreInterval_smul
    (p : ℕ → ℝ → ℝ) (hp : ∀ n, Continuous (p n))
    (hpBound : ∀ n x, x ∈ Icc (-1 : ℝ) 1 → |p n x| ≤ 1)
    (a : ℕ → ℝ) (ha : Summable fun n ↦ |a n|)
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    HasSum (fun n ↦ a n * p n x)
      ((∑' n, a n • continuousMapOnLegendreInterval (p n) (hp n)) ⟨x, hx⟩) := by
  simpa only [ContinuousMap.smul_apply, smul_eq_mul,
    continuousMapOnLegendreInterval_apply] using
      ContinuousMap.hasSum_apply
        (hasSum_continuousMapOnLegendreInterval_smul p hp hpBound a ha) ⟨x, hx⟩

/-- A cubic tail bound is enough for absolute summability.  The shifted form
avoids a spurious denominator at index zero. -/
theorem summable_abs_of_cubic_tail_bound
    (a : ℕ → ℝ) (C : ℝ)
    (hbound : ∀ n : ℕ,
      |a (n + 1)| ≤ C * ((((n + 1 : ℕ) : ℝ) ^ 3)⁻¹)) :
    Summable fun n ↦ |a n| := by
  have hpSeries : Summable fun n : ℕ ↦ (((n : ℝ) ^ 3)⁻¹) :=
    Real.summable_nat_pow_inv.mpr (by norm_num)
  have hpSeriesShift : Summable fun n : ℕ ↦ ((((n + 1 : ℕ) : ℝ) ^ 3)⁻¹) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff (f := fun n : ℕ ↦ (((n : ℝ) ^ 3)⁻¹)) 1).mpr hpSeries
  have hmajor : Summable fun n : ℕ ↦
      C * ((((n + 1 : ℕ) : ℝ) ^ 3)⁻¹) :=
    hpSeriesShift.mul_left C
  have htail : Summable fun n : ℕ ↦ |a (n + 1)| :=
    Summable.of_nonneg_of_le (fun n ↦ abs_nonneg (a (n + 1))) hbound hmajor
  exact (summable_nat_add_iff (f := fun n : ℕ ↦ |a n|) 1).mp htail

/-- Smoothness of `f`, together with the standard eigenvalue and interval
bound for a sequence of Legendre eigenfunctions, implies absolute summability
of all normalized coefficients. -/
theorem summable_abs_legendreSeriesCoefficientOf
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (p : ℕ → ℝ → ℝ) (hpSmooth : ∀ n, ContDiff ℝ ∞ (p n))
    (hpEigen : ∀ n x,
      legendreSturmLiouville (p n) x =
        ((n : ℝ) * (n + 1 : ℝ)) * p n x)
    (hpBound : ∀ n x, x ∈ Icc (-1 : ℝ) 1 → |p n x| ≤ 1) :
    Summable fun n ↦ |legendreSeriesCoefficientOf f (p n) n| := by
  let L2f : ℝ → ℝ := legendreSturmLiouville (legendreSturmLiouville f)
  have hL2smooth : ContDiff ℝ ∞ L2f :=
    ContDiff.legendreSturmLiouville (ContDiff.legendreSturmLiouville hf)
  let L2fMap : C(Icc (-1 : ℝ) 1, ℝ) :=
    continuousMapOnLegendreInterval L2f hL2smooth.continuous
  let B : ℝ := ‖L2fMap‖
  have hB : 0 ≤ B := norm_nonneg _
  have hL2bound : ∀ x ∈ Icc (-1 : ℝ) 1, |L2f x| ≤ B := by
    intro x hx
    simpa [L2fMap, B, Real.norm_eq_abs] using
      ContinuousMap.norm_coe_le_norm L2fMap ⟨x, hx⟩
  apply summable_abs_of_cubic_tail_bound
    (fun n ↦ legendreSeriesCoefficientOf f (p n) n) (3 * B)
  intro n
  let m : ℕ := n + 1
  have hm : 1 ≤ m := by omega
  have hdecay := pow_three_mul_abs_legendreSeriesCoefficientOf_le
    hf (hpSmooth m) m hm B hB (hpEigen m) (hpBound m) (by
      intro x hx
      exact hL2bound x hx)
  have hpowPos : 0 < ((m : ℝ) ^ 3) := by positivity
  apply (le_mul_inv_iff₀ hpowPos).2
  simpa [m, mul_comm, mul_left_comm, mul_assoc] using hdecay

/-- The full Fourier--Legendre series of a smooth function converges
absolutely in the uniform norm, assuming the standard Sturm eigenvalue and
unit interval bound for the polynomial sequence. -/
theorem hasSum_legendreSeriesCoefficientOf_uniform
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (p : ℕ → ℝ → ℝ) (hpSmooth : ∀ n, ContDiff ℝ ∞ (p n))
    (hpEigen : ∀ n x,
      legendreSturmLiouville (p n) x =
        ((n : ℝ) * (n + 1 : ℝ)) * p n x)
    (hpBound : ∀ n x, x ∈ Icc (-1 : ℝ) 1 → |p n x| ≤ 1) :
    HasSum (fun n ↦
      legendreSeriesCoefficientOf f (p n) n •
        continuousMapOnLegendreInterval (p n) (hpSmooth n).continuous)
      (∑' n,
        legendreSeriesCoefficientOf f (p n) n •
          continuousMapOnLegendreInterval (p n) (hpSmooth n).continuous) := by
  exact hasSum_continuousMapOnLegendreInterval_smul p
    (fun n ↦ (hpSmooth n).continuous) hpBound
    (fun n ↦ legendreSeriesCoefficientOf f (p n) n)
    (summable_abs_legendreSeriesCoefficientOf f hf p hpSmooth hpEigen hpBound)

/-- Pointwise form of the preceding uniform `HasSum`, valid throughout the
closed Legendre interval and hence at both endpoints. -/
theorem hasSum_legendreSeriesCoefficientOf_pointwise
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (p : ℕ → ℝ → ℝ) (hpSmooth : ∀ n, ContDiff ℝ ∞ (p n))
    (hpEigen : ∀ n x,
      legendreSturmLiouville (p n) x =
        ((n : ℝ) * (n + 1 : ℝ)) * p n x)
    (hpBound : ∀ n x, x ∈ Icc (-1 : ℝ) 1 → |p n x| ≤ 1)
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    HasSum (fun n ↦ legendreSeriesCoefficientOf f (p n) n * p n x)
      ((∑' n,
        legendreSeriesCoefficientOf f (p n) n •
          continuousMapOnLegendreInterval (p n) (hpSmooth n).continuous) ⟨x, hx⟩) := by
  exact hasSum_eval_continuousMapOnLegendreInterval_smul p
    (fun n ↦ (hpSmooth n).continuous) hpBound
    (fun n ↦ legendreSeriesCoefficientOf f (p n) n)
    (summable_abs_legendreSeriesCoefficientOf f hf p hpSmooth hpEigen hpBound) x hx

/-! ## Uniqueness from polynomial orthogonality -/

/-- A continuous function on the Legendre interval which is orthogonal to
every polynomial vanishes there.  This is the density step in the usual proof
that an absolutely and uniformly convergent Fourier--Legendre series has the
original function as its sum. -/
theorem eq_zero_on_legendreInterval_of_integral_mul_polynomial_eq_zero
    (h : ℝ → ℝ) (hh : ContinuousOn h (Icc (-1 : ℝ) 1))
    (horth : ∀ p : ℝ[X],
      (∫ x in (-1 : ℝ)..1, h x * p.eval x) = 0) :
    ∀ x ∈ Icc (-1 : ℝ) 1, h x = 0 := by
  let hMap : C(Icc (-1 : ℝ) 1, ℝ) :=
    ⟨fun x ↦ h x, continuousOn_iff_continuous_restrict.mp hh⟩
  let A : ℝ := ∫ x in (-1 : ℝ)..1, h x ^ 2
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact intervalIntegral.integral_nonneg (by norm_num) fun x _hx ↦ sq_nonneg (h x)
  have hA_zero : A = 0 := by
    apply le_antisymm _ hA_nonneg
    by_contra hnot
    have hA_pos : 0 < A := lt_of_not_ge hnot
    let M : ℝ := ‖hMap‖
    have hM_nonneg : 0 ≤ M := norm_nonneg _
    let ε : ℝ := A / (4 * (M + 1))
    have hden_pos : 0 < 4 * (M + 1) := by positivity
    have hε_pos : 0 < ε := div_pos hA_pos hden_pos
    obtain ⟨p, hp⟩ :=
      exists_polynomial_near_of_continuousOn (-1 : ℝ) 1 h hh ε hε_pos
    have hsquareInt : IntervalIntegrable (fun x : ℝ ↦ h x ^ 2) volume (-1) 1 :=
      (hh.pow 2).intervalIntegrable_of_Icc (by norm_num)
    have hpContinuous : Continuous fun x : ℝ ↦ p.eval x := by
      fun_prop
    have hpolyInt : IntervalIntegrable (fun x : ℝ ↦ h x * p.eval x) volume (-1) 1 :=
      (hh.mul hpContinuous.continuousOn).intervalIntegrable_of_Icc (by norm_num)
    have hrewrite :
        (∫ x in (-1 : ℝ)..1, h x * (h x - p.eval x)) = A := by
      rw [show (∫ x in (-1 : ℝ)..1, h x * (h x - p.eval x)) =
          ∫ x in (-1 : ℝ)..1, h x ^ 2 - h x * p.eval x by
        apply intervalIntegral.integral_congr
        intro x _hx
        ring]
      rw [intervalIntegral.integral_sub hsquareInt hpolyInt, horth p, sub_zero]
    have hintegralBound :
        ‖∫ x in (-1 : ℝ)..1, h x * (h x - p.eval x)‖ ≤ M * ε * 2 := by
      have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (-1 : ℝ)) (b := 1) (C := M * ε)
        (f := fun x : ℝ ↦ h x * (h x - p.eval x)) (fun x hx ↦ by
          have hxmem : x ∈ Icc (-1 : ℝ) 1 := by
            norm_num [min_def, max_def] at hx
            exact ⟨hx.1.le, hx.2⟩
          have hh_le : |h x| ≤ M := by
            simpa [hMap, M, Real.norm_eq_abs] using
              ContinuousMap.norm_coe_le_norm hMap ⟨x, hxmem⟩
          have hdiff_le : |h x - p.eval x| ≤ ε := by
            rw [abs_sub_comm]
            exact (hp x hxmem).le
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul hh_le hdiff_le (abs_nonneg _) hM_nonneg)
      norm_num at hbound ⊢
      simpa [mul_assoc] using hbound
    have hsmall : M * ε * 2 < A := by
      have heq : M * ε * 2 = (2 * M * A) / (4 * (M + 1)) := by
        dsimp [ε]
        ring
      rw [heq, div_lt_iff₀ hden_pos]
      nlinarith
    have hnormA : ‖A‖ = A := Real.norm_of_nonneg hA_nonneg
    rw [hrewrite, hnormA] at hintegralBound
    exact (not_lt_of_ge hintegralBound) hsmall
  intro x hx
  by_contra hxne
  have hsq_pos : 0 < h x ^ 2 := sq_pos_of_ne_zero hxne
  have hpositive : 0 < A := by
    dsimp [A]
    have hzeroContinuous : ContinuousOn (fun _x : ℝ ↦ (0 : ℝ)) (Icc (-1 : ℝ) 1) :=
      continuous_const.continuousOn
    have hsquareContinuous : ContinuousOn (fun y : ℝ ↦ h y ^ 2) (Icc (-1 : ℝ) 1) :=
      hh.pow 2
    have hlt := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      (by norm_num : (-1 : ℝ) < 1) hzeroContinuous hsquareContinuous
      (fun y _hy ↦ sq_nonneg (h y)) ⟨x, hx, hsq_pos⟩
    simpa using hlt
  exact hxne (by nlinarith [hA_zero, hpositive])

end Fabius
