import FabiusFunction.Differential
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.PSeries
import Mathlib.Algebra.Polynomial.Sequence
import Mathlib.MeasureTheory.Integral.DominatedConvergence
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
The Green identity is also iterated to transfer an arbitrary power of a
Legendre eigenvalue from an eigenfunction onto the function being expanded.
-/

set_option autoImplicit false

open scoped ContDiff Interval Polynomial
open Set MeasureTheory

namespace Fabius

open Polynomial

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

/-- Every iterate of the Legendre Sturm--Liouville operator preserves
smoothness. -/
theorem ContDiff.iterate_legendreSturmLiouville {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    ContDiff ℝ ∞ ((Fabius.legendreSturmLiouville^[k]) f) := by
  induction k with
  | zero => simpa
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact ContDiff.legendreSturmLiouville ih

/-- Sonin's energy estimate: a polynomial solution of Legendre's differential
equation whose endpoint values have square one is bounded by one on
`[-1,1]`.  The energy is antitone on `[-1,0]` and monotone on `[0,1]`. -/
theorem abs_eval_le_one_of_legendre_ode
    (p : ℝ[X]) (n : ℕ) (hn : 0 < n)
    (hODE : ∀ x : ℝ,
      (1 - x ^ 2) * (derivative (derivative p)).eval x -
          2 * x * (derivative p).eval x +
          ((n : ℝ) * (n + 1 : ℝ)) * p.eval x = 0)
    (hleft : (p.eval (-1)) ^ 2 = 1)
    (hright : (p.eval 1) ^ 2 = 1)
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    |p.eval x| ≤ 1 := by
  let y : ℝ → ℝ := fun z ↦ p.eval z
  let dy : ℝ → ℝ := fun z ↦ (derivative p).eval z
  let ddy : ℝ → ℝ := fun z ↦ (derivative (derivative p)).eval z
  let eigenvalue : ℝ := (n : ℝ) * (n + 1 : ℝ)
  let weight : ℝ → ℝ := fun z ↦ (1 - z ^ 2) / eigenvalue
  let energy : ℝ → ℝ := y ^ 2 + weight * dy ^ 2
  let energy' : ℝ → ℝ := fun z ↦
    (2 * z) / eigenvalue * dy z ^ 2
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have heigenvalue : 0 < eigenvalue := by
    dsimp [eigenvalue]
    positivity
  have henergyDeriv (z : ℝ) : HasDerivAt energy (energy' z) z := by
    have hy : HasDerivAt y (dy z) z := by
      dsimp [y, dy]
      exact p.hasDerivAt z
    have hdy : HasDerivAt dy (ddy z) z := by
      dsimp [dy, ddy]
      exact (derivative p).hasDerivAt z
    have hweight : HasDerivAt weight (-2 * z / eigenvalue) z := by
      dsimp [weight]
      have hbase : HasDerivAt (fun w : ℝ ↦ 1 - w ^ 2) (-2 * z) z := by
        simpa using ((hasDerivAt_pow 2 z).const_sub 1)
      exact hbase.div_const eigenvalue
    have hraw := (hy.pow 2).add (hweight.mul (hdy.pow 2))
    change HasDerivAt energy
      (2 * y z ^ 1 * dy z +
        (-2 * z / eigenvalue * dy z ^ 2 +
          weight z * (2 * dy z ^ 1 * ddy z))) z at hraw
    have hderivEq :
        2 * y z ^ 1 * dy z +
            (-2 * z / eigenvalue * dy z ^ 2 +
              weight z * (2 * dy z ^ 1 * ddy z)) =
          energy' z := by
      dsimp [y, dy, ddy, weight, energy', eigenvalue]
      field_simp [ne_of_gt heigenvalue]
      linear_combination (derivative p).eval z * hODE z
    rw [hderivEq] at hraw
    exact hraw
  have henergyContinuous : Continuous energy := by
    rw [continuous_iff_continuousAt]
    exact fun z ↦ (henergyDeriv z).continuousAt
  have hanti : AntitoneOn energy (Icc (-1 : ℝ) 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos
      (D := Icc (-1 : ℝ) 0) (f' := energy') (convex_Icc (-1) 0)
      henergyContinuous.continuousOn
      (fun z _hz ↦ (henergyDeriv z).hasDerivWithinAt)
    intro z hz
    have hzle : z ≤ 0 := by
      have hz' : z ∈ Ioo (-1 : ℝ) 0 := by
        simpa only [interior_Icc] using hz
      exact hz'.2.le
    dsimp [energy']
    exact mul_nonpos_of_nonpos_of_nonneg
      (div_nonpos_of_nonpos_of_nonneg (by linarith) heigenvalue.le)
      (sq_nonneg _)
  have hmono : MonotoneOn energy (Icc (0 : ℝ) 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg
      (D := Icc (0 : ℝ) 1) (f' := energy') (convex_Icc 0 1)
      henergyContinuous.continuousOn
      (fun z _hz ↦ (henergyDeriv z).hasDerivWithinAt)
    intro z hz
    have hzge : 0 ≤ z := by
      have hz' : z ∈ Ioo (0 : ℝ) 1 := by
        simpa only [interior_Icc] using hz
      exact hz'.1.le
    dsimp [energy']
    positivity
  have henergyLeft : energy (-1) = 1 := by
    dsimp [energy, weight]
    rw [hleft]
    norm_num
  have henergyRight : energy 1 = 1 := by
    dsimp [energy, weight]
    rw [hright]
    norm_num
  have henergyLe : energy x ≤ 1 := by
    rcases le_total x 0 with hx0 | h0x
    · have hxLeft : x ∈ Icc (-1 : ℝ) 0 := ⟨hx.1, hx0⟩
      have hbound := hanti (show (-1 : ℝ) ∈ Icc (-1 : ℝ) 0 by norm_num)
        hxLeft hx.1
      rwa [henergyLeft] at hbound
    · have hxRight : x ∈ Icc (0 : ℝ) 1 := ⟨h0x, hx.2⟩
      have hbound := hmono hxRight (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
        hx.2
      rwa [henergyRight] at hbound
  have hweightNonneg : 0 ≤ (1 - x ^ 2) / eigenvalue * dy x ^ 2 := by
    have hxSq : x ^ 2 ≤ 1 := by
      rw [sq_le_one_iff_abs_le_one]
      exact abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
    exact mul_nonneg (div_nonneg (sub_nonneg.mpr hxSq) heigenvalue.le) (sq_nonneg _)
  rw [← sq_le_one_iff_abs_le_one]
  calc
    (p.eval x) ^ 2 = y x ^ 2 := rfl
    _ ≤ energy x := by
      dsimp [energy, weight]
      linarith
    _ ≤ 1 := henergyLe

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

/-- Iterating Green's identity transfers any natural power of a
Sturm--Liouville eigenvalue from the eigenfunction to the other factor. -/
theorem eigenvalue_pow_mul_integral_eq_integral_iterate_legendreSturmLiouville
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (eigenvalue : ℝ)
    (heigen : ∀ x, legendreSturmLiouville g x = eigenvalue * g x)
    (k : ℕ) :
    eigenvalue ^ k * (∫ x in (-1 : ℝ)..1, f x * g x) =
      ∫ x in (-1 : ℝ)..1,
        (legendreSturmLiouville^[k]) f x * g x := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        eigenvalue ^ (k + 1) * (∫ x in (-1 : ℝ)..1, f x * g x) =
            eigenvalue *
              (eigenvalue ^ k * (∫ x in (-1 : ℝ)..1, f x * g x)) := by
                rw [pow_succ]
                ring
        _ = eigenvalue *
            (∫ x in (-1 : ℝ)..1,
              (legendreSturmLiouville^[k]) f x * g x) := by rw [ih]
        _ = ∫ x in (-1 : ℝ)..1,
            legendreSturmLiouville ((legendreSturmLiouville^[k]) f) x * g x :=
          eigenvalue_mul_integral_eq_integral_legendreSturmLiouville
            (ContDiff.iterate_legendreSturmLiouville hf k) hg eigenvalue heigen
        _ = ∫ x in (-1 : ℝ)..1,
            (legendreSturmLiouville^[k + 1]) f x * g x := by
          rw [Function.iterate_succ_apply']

/-- Applying Green's identity twice transfers two powers of a
Sturm--Liouville eigenvalue from the Legendre polynomial to the function. -/
theorem eigenvalue_sq_mul_integral_eq_integral_legendreSturmLiouville_sq
    {f g : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (eigenvalue : ℝ)
    (heigen : ∀ x, legendreSturmLiouville g x = eigenvalue * g x) :
    eigenvalue ^ 2 * (∫ x in (-1 : ℝ)..1, f x * g x) =
      ∫ x in (-1 : ℝ)..1,
        legendreSturmLiouville (legendreSturmLiouville f) x * g x := by
  simpa [Function.iterate_succ_apply'] using
    eigenvalue_pow_mul_integral_eq_integral_iterate_legendreSturmLiouville
      hf hg eigenvalue heigen 2

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

/-- The bundled restriction to `Icc (-1) 1` evaluates through the
underlying function.  Used to turn `ContinuousMap.hasSum_apply` into
pointwise statements in
`hasSum_eval_continuousMapOnLegendreInterval_smul` and in
`hasSum_legendrePolynomialSeries_eq_uniform`. -/
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

/-! ## Identification of the uniform sum -/

/-- Abstract Fourier--Legendre completeness theorem.

Once a polynomial sequence has degree `n`, the standard orthogonality and
norm, the Sturm eigenvalue, and the unit bound on `[-1,1]`, its normalized
series for a smooth function has that function as its pointwise sum.  The
proof first uses dominated convergence to identify every coefficient of the
uniform sum, then `Polynomial.Sequence.span` and Weierstrass density to prove
equality.
-/
theorem hasSum_legendrePolynomialSeries_eq
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (P : ℕ → ℝ[X])
    (hdegree : ∀ n, (P n).degree = n)
    (hpSmooth : ∀ n, ContDiff ℝ ∞ (fun x : ℝ ↦ (P n).eval x))
    (hpEigen : ∀ n x,
      legendreSturmLiouville (fun y : ℝ ↦ (P n).eval y) x =
        ((n : ℝ) * (n + 1 : ℝ)) * (P n).eval x)
    (hpBound : ∀ n x, x ∈ Icc (-1 : ℝ) 1 → |(P n).eval x| ≤ 1)
    (horthogonal : ∀ m n, m ≠ n →
      (∫ x in (-1 : ℝ)..1, (P m).eval x * (P n).eval x) = 0)
    (hnorm : ∀ n,
      (∫ x in (-1 : ℝ)..1, (P n).eval x ^ 2) =
        2 / (((2 * n + 1 : ℕ) : ℝ)))
    (x : ℝ) (hx : x ∈ Icc (-1 : ℝ) 1) :
    HasSum (fun n ↦
      legendreSeriesCoefficientOf f (fun y : ℝ ↦ (P n).eval y) n *
        (P n).eval x) (f x) := by
  let p : ℕ → ℝ → ℝ := fun n y ↦ (P n).eval y
  let a : ℕ → ℝ := fun n ↦ legendreSeriesCoefficientOf f (p n) n
  have hpSmooth' : ∀ n, ContDiff ℝ ∞ (p n) := by
    intro n
    simpa [p] using hpSmooth n
  have hpEigen' : ∀ n y,
      legendreSturmLiouville (p n) y =
        ((n : ℝ) * (n + 1 : ℝ)) * p n y := by
    intro n y
    simpa [p] using hpEigen n y
  have hpBound' : ∀ n y, y ∈ Icc (-1 : ℝ) 1 → |p n y| ≤ 1 := by
    intro n y hy
    simpa [p] using hpBound n y hy
  have ha : Summable fun n ↦ |a n| := by
    simpa [a] using
      summable_abs_legendreSeriesCoefficientOf f hf p hpSmooth' hpEigen' hpBound'
  let S : C(Icc (-1 : ℝ) 1, ℝ) :=
    ∑' n, a n • continuousMapOnLegendreInterval (p n) (hpSmooth' n).continuous
  let s : ℝ → ℝ := fun y ↦ ∑' n, a n * p n y
  have hs_eq_S (y : ℝ) (hy : y ∈ Icc (-1 : ℝ) 1) : s y = S ⟨y, hy⟩ := by
    have hsum := hasSum_eval_continuousMapOnLegendreInterval_smul
      p (fun n ↦ (hpSmooth' n).continuous) hpBound' a ha y hy
    exact hsum.tsum_eq
  have hsContinuousOn : ContinuousOn s (Icc (-1 : ℝ) 1) := by
    rw [continuousOn_iff_continuous_restrict]
    have heq : Set.restrict (Icc (-1 : ℝ) 1) s = S := by
      funext y
      exact hs_eq_S y y.property
    rw [heq]
    exact S.continuous
  have hsIntegralCoefficient : ∀ r : ℕ,
      (∫ y in (-1 : ℝ)..1, s y * p r y) =
        ∫ y in (-1 : ℝ)..1, f y * p r y := by
    intro r
    let term : ℕ → C(ℝ, ℝ) := fun n ↦
      ⟨fun y ↦ a n * p n y * p r y, by
        dsimp [p]
        fun_prop⟩
    let K : TopologicalSpace.Compacts ℝ := ⟨uIcc (-1 : ℝ) 1, isCompact_uIcc⟩
    have htermNorm : ∀ n, ‖(term n).restrict K‖ ≤ |a n| := by
      intro n
      rw [ContinuousMap.norm_le _ (abs_nonneg (a n))]
      intro y
      have hymem : (y : ℝ) ∈ Icc (-1 : ℝ) 1 := by
        have hy := y.property
        norm_num [K, min_def, max_def] at hy
        exact hy
      change ‖a n * p n y * p r y‖ ≤ |a n|
      rw [Real.norm_eq_abs, abs_mul, abs_mul]
      calc
        |a n| * |p n y| * |p r y| ≤ |a n| * 1 * 1 := by
          gcongr
          · exact hpBound' n y hymem
          · exact hpBound' r y hymem
        _ = |a n| := by ring
    have htermSummable : Summable fun n ↦ ‖(term n).restrict K‖ :=
      Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) htermNorm ha
    have hint := intervalIntegral.hasSum_intervalIntegral_of_summable_norm
      (a := (-1 : ℝ)) (b := 1) htermSummable
    have htarget :
        (∫ y in (-1 : ℝ)..1, ∑' n, term n y) =
          ∫ y in (-1 : ℝ)..1, s y * p r y := by
      apply intervalIntegral.integral_congr
      intro y _hy
      change (∑' n, a n * p n y * p r y) = s y * p r y
      simpa [s] using
        (tsum_mul_right (f := fun n ↦ a n * p n y) (a := p r y))
    rw [htarget] at hint
    have hsingle : HasSum (fun n ↦ ∫ y in (-1 : ℝ)..1, term n y)
        (∫ y in (-1 : ℝ)..1, f y * p r y) := by
      convert hasSum_ite_eq r (∫ y in (-1 : ℝ)..1, f y * p r y) using 1
      funext n
      by_cases hnr : n = r
      · subst n
        rw [if_pos rfl]
        change (∫ y in (-1 : ℝ)..1, a r * p r y * p r y) = _
        have hfactor :
            (∫ y in (-1 : ℝ)..1, a r * p r y * p r y) =
              a r * ∫ y in (-1 : ℝ)..1, p r y ^ 2 := by
          calc
            _ = ∫ y in (-1 : ℝ)..1, a r * (p r y ^ 2) := by
              apply intervalIntegral.integral_congr
              intro y _hy
              ring
            _ = _ := intervalIntegral.integral_const_mul (a r) (fun y ↦ p r y ^ 2)
        rw [hfactor]
        rw [show (∫ y in (-1 : ℝ)..1, p r y ^ 2) =
            2 / (((2 * r + 1 : ℕ) : ℝ)) by simpa [p] using hnorm r]
        dsimp [a, legendreSeriesCoefficientOf]
        have hden : (((2 * r + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
        field_simp
      · rw [if_neg hnr]
        change (∫ y in (-1 : ℝ)..1, a n * p n y * p r y) = 0
        have hfactor :
            (∫ y in (-1 : ℝ)..1, a n * p n y * p r y) =
              a n * ∫ y in (-1 : ℝ)..1, p n y * p r y := by
          calc
            _ = ∫ y in (-1 : ℝ)..1, a n * (p n y * p r y) := by
              apply intervalIntegral.integral_congr
              intro y _hy
              ring
            _ = _ := intervalIntegral.integral_const_mul (a n) (fun y ↦ p n y * p r y)
        rw [hfactor]
        have hortho : (∫ y in (-1 : ℝ)..1, p n y * p r y) = 0 := by
          simpa [p] using horthogonal n r hnr
        rw [hortho, mul_zero]
    exact HasSum.unique hint hsingle
  have hdiffContinuous : ContinuousOn (fun y ↦ f y - s y) (Icc (-1 : ℝ) 1) :=
    hf.continuous.continuousOn.sub hsContinuousOn
  have hdiffOrthogonal : ∀ n,
      (∫ y in (-1 : ℝ)..1, (f y - s y) * (P n).eval y) = 0 := by
    intro n
    have hfInt : IntervalIntegrable (fun y : ℝ ↦ f y * p n y) volume (-1) 1 :=
      (hf.continuous.mul (hpSmooth' n).continuous).intervalIntegrable _ _
    have hsInt : IntervalIntegrable (fun y : ℝ ↦ s y * p n y) volume (-1) 1 :=
      (hsContinuousOn.mul (hpSmooth' n).continuous.continuousOn)
        |>.intervalIntegrable_of_Icc (by norm_num)
    rw [show (∫ y in (-1 : ℝ)..1, (f y - s y) * (P n).eval y) =
        (∫ y in (-1 : ℝ)..1, f y * p n y) -
          ∫ y in (-1 : ℝ)..1, s y * p n y by
      rw [← intervalIntegral.integral_sub hfInt hsInt]
      apply intervalIntegral.integral_congr
      intro y _hy
      simp only [p]
      ring]
    rw [hsIntegralCoefficient n, sub_self]
  let T : ℝ[X] →ₗ[ℝ] ℝ := {
    toFun := fun q ↦ ∫ y in (-1 : ℝ)..1, (f y - s y) * q.eval y
    map_add' := by
      intro q₁ q₂
      have hq₁ : IntervalIntegrable
          (fun y : ℝ ↦ (f y - s y) * q₁.eval y) volume (-1) 1 := by
        have hq₁Continuous : Continuous fun y : ℝ ↦ q₁.eval y := by fun_prop
        apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
        exact hdiffContinuous.mul hq₁Continuous.continuousOn
      have hq₂ : IntervalIntegrable
          (fun y : ℝ ↦ (f y - s y) * q₂.eval y) volume (-1) 1 := by
        have hq₂Continuous : Continuous fun y : ℝ ↦ q₂.eval y := by fun_prop
        apply ContinuousOn.intervalIntegrable_of_Icc (by norm_num)
        exact hdiffContinuous.mul hq₂Continuous.continuousOn
      rw [← intervalIntegral.integral_add hq₁ hq₂]
      apply intervalIntegral.integral_congr
      intro y _hy
      simp only [Polynomial.eval_add]
      ring
    map_smul' := by
      intro c q
      rw [RingHom.id_apply]
      rw [show (∫ y in (-1 : ℝ)..1, (f y - s y) * (c • q).eval y) =
          ∫ y in (-1 : ℝ)..1, c * ((f y - s y) * q.eval y) by
        apply intervalIntegral.integral_congr
        intro y _hy
        simp only [Polynomial.eval_smul, smul_eq_mul]
        ring]
      rw [intervalIntegral.integral_const_mul]
      simp only [smul_eq_mul]
  }
  let sequence : Polynomial.Sequence ℝ := {
    elems' := P
    degree_eq' := hdegree
  }
  have hleadingUnit : ∀ n, IsUnit (sequence n).leadingCoeff := by
    intro n
    rw [isUnit_iff_ne_zero]
    exact Polynomial.leadingCoeff_ne_zero.mpr (sequence.ne_zero n)
  have hspan : Submodule.span ℝ (Set.range P) = ⊤ := by
    simpa [sequence] using sequence.span hleadingUnit
  have hTzero : ∀ q : ℝ[X], T q = 0 := by
    intro q
    have hrange : Set.range P ⊆ T.ker := by
      rintro q ⟨n, rfl⟩
      change T (P n) = 0
      exact hdiffOrthogonal n
    have hle : Submodule.span ℝ (Set.range P) ≤ T.ker :=
      Submodule.span_le.mpr hrange
    rw [hspan] at hle
    exact LinearMap.mem_ker.mp (hle trivial)
  have hdiffZero := eq_zero_on_legendreInterval_of_integral_mul_polynomial_eq_zero
    (fun y ↦ f y - s y) hdiffContinuous (by
      intro q
      exact hTzero q)
  have hsx : s x = f x := by
    have := hdiffZero x hx
    linarith
  have hpoint := hasSum_eval_continuousMapOnLegendreInterval_smul
    p (fun n ↦ (hpSmooth' n).continuous) hpBound' a ha x hx
  rw [← hs_eq_S x hx, hsx] at hpoint
  simpa [a, p] using hpoint

/-- Uniform form of `hasSum_legendrePolynomialSeries_eq`.  The target is the
restriction of `f` to the closed Legendre interval, so this is convergence in
the supremum norm and in particular includes both endpoints. -/
theorem hasSum_legendrePolynomialSeries_eq_uniform
    (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (P : ℕ → ℝ[X])
    (hdegree : ∀ n, (P n).degree = n)
    (hpSmooth : ∀ n, ContDiff ℝ ∞ (fun x : ℝ ↦ (P n).eval x))
    (hpEigen : ∀ n x,
      legendreSturmLiouville (fun y : ℝ ↦ (P n).eval y) x =
        ((n : ℝ) * (n + 1 : ℝ)) * (P n).eval x)
    (hpBound : ∀ n x, x ∈ Icc (-1 : ℝ) 1 → |(P n).eval x| ≤ 1)
    (horthogonal : ∀ m n, m ≠ n →
      (∫ x in (-1 : ℝ)..1, (P m).eval x * (P n).eval x) = 0)
    (hnorm : ∀ n,
      (∫ x in (-1 : ℝ)..1, (P n).eval x ^ 2) =
        2 / (((2 * n + 1 : ℕ) : ℝ))) :
    HasSum (fun n ↦
      legendreSeriesCoefficientOf f (fun y : ℝ ↦ (P n).eval y) n •
        continuousMapOnLegendreInterval
          (fun y : ℝ ↦ (P n).eval y) (hpSmooth n).continuous)
      (continuousMapOnLegendreInterval f hf.continuous) := by
  let p : ℕ → ℝ → ℝ := fun n y ↦ (P n).eval y
  have hpSmooth' : ∀ n, ContDiff ℝ ∞ (p n) := by
    intro n
    simpa [p] using hpSmooth n
  have hpEigen' : ∀ n y,
      legendreSturmLiouville (p n) y =
        ((n : ℝ) * (n + 1 : ℝ)) * p n y := by
    intro n y
    simpa [p] using hpEigen n y
  have hpBound' : ∀ n y, y ∈ Icc (-1 : ℝ) 1 → |p n y| ≤ 1 := by
    intro n y hy
    simpa [p] using hpBound n y hy
  have huniform := hasSum_legendreSeriesCoefficientOf_uniform
    f hf p hpSmooth' hpEigen' hpBound'
  have htarget :
      (∑' n,
        legendreSeriesCoefficientOf f (p n) n •
          continuousMapOnLegendreInterval (p n) (hpSmooth' n).continuous) =
        continuousMapOnLegendreInterval f hf.continuous := by
    apply ContinuousMap.ext
    intro x
    have heval := ContinuousMap.hasSum_apply huniform x
    have hpoint := hasSum_legendrePolynomialSeries_eq f hf P hdegree hpSmooth hpEigen
      hpBound horthogonal hnorm x x.property
    have heval' : HasSum (fun n ↦
        legendreSeriesCoefficientOf f (p n) n * p n x)
        ((∑' n,
          legendreSeriesCoefficientOf f (p n) n •
            continuousMapOnLegendreInterval (p n) (hpSmooth' n).continuous) x) := by
      simpa only [ContinuousMap.smul_apply, smul_eq_mul,
        continuousMapOnLegendreInterval_apply] using heval
    have hpoint' : HasSum (fun n ↦
        legendreSeriesCoefficientOf f (p n) n * p n x) (f x) := by
      simpa [p] using hpoint
    exact HasSum.unique heval' hpoint'
  rw [htarget] at huniform
  simpa [p] using huniform

end Fabius
