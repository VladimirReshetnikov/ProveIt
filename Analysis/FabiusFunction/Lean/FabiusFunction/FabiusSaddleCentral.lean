import FabiusFunction.FabiusSaddleTail
import FabiusFunction.FabiusComplexMGF
import FabiusFunction.NegativeLaplaceDerivativeBounds

/-!
# Corrected central estimate for the Fabius saddle integral

On the central arc of the Fabius saddle the rescaled kernel `K` has the
exponential representation

`K v = exp (-v ^ 2 / 2) * exp ((a * v + c * v ^ 3) * I + R v)`,

with linear and cubic coefficients `a`, `c` of size `b ^ (-1 / 2)` and a
Taylor remainder `R v` of size `(v ^ 2 + v ^ 4) / b`.  Comparing `K` with the
bare Gaussian is not accurate enough at this precision: the odd first-order
term has absolute integral of size `b ^ (-1 / 2)`, which swamps the target
`O (1 / b)`.  It is therefore kept in the reference,

`oddCorrection a c v = exp (-v ^ 2 / 2) * ((a * v + c * v ^ 3) * I)`,

whose signed integral vanishes by oddness, and this module bounds the `L¹`
distance from `K` to `standardGaussian + oddCorrection a c` on the arc.  The
retained phase is purely imaginary, so a second-order exponential estimate
lets it enter only through its square, and that is exactly why coefficients
of size `b ^ (-1 / 2)` end up contributing only `O (1 / b)`.

Nothing here is specific to the Fabius function: the kernel, the remainder,
the central set and the index filter are all arbitrary, and the coefficient
sizes enter as the square-root-free hypotheses `b * a ^ 2 ≤ Clinear ^ 2` and
`b * c ^ 2 ≤ Ccubic ^ 2`.  That is the point of the separation.
`FabiusFunction.FabiusSaddleCentralLambert` discharges those hypotheses from
the dyadic Lambert Taylor data, `FabiusFunction.FabiusSaddleReferenceTail`
supplies the matching estimate over the complement `(Icc (-A) A)ᶜ`, and
`FabiusFunction.QuantitativeSaddle` turns central plus tail into normalized
Gaussian mass.

## Main results

* `oddPhase` and `oddCorrection` -- the retained imaginary
  linear-plus-cubic phase and its Gaussian-weighted form, together with the
  oddness, norm and integrability lemmas the reference needs.
* `centralMajorant` -- the arc-independent integrable majorant
  `exp (-v ^ 2 / 2) * ((2 * Clinear ^ 2 + 2 * Cquadratic) * v ^ 2 +
  2 * Cquartic * v ^ 4 + 2 * Ccubic ^ 2 * v ^ 6)`.
* `norm_exp_add_sub_one_sub_le` -- the complex estimate
  `‖exp (u + w) - (1 + u)‖ ≤ ‖u‖ ^ 2 + 2 * ‖w‖` for purely imaginary `u`,
  valid for `‖u‖ ≤ 1` and `‖w‖ ≤ 1`.
* `norm_sub_gaussian_add_oddCorrection_le` -- the pointwise corrected-kernel
  bound, by `centralMajorant` divided by `b`.
* `integral_norm_sub_gaussian_add_oddCorrection_le` -- its integrated form
  over an arbitrary measurable central set, bounded by the whole-line
  integral of `centralMajorant` divided by `b`.
* `central_corrected_error_isBigO` and
  `standardRadius_central_corrected_error_isBigO` -- the filter forms
  `=O[l] (fun i => (b i)⁻¹)`, the second specialized to the standard radius
  `fabiusSaddleCentralRadius b = sqrt (32 * log b)`.
* `normalized_integral_sub_one_isBigO_of_standardRadius_taylor` -- central
  Taylor control plus a corrected complementary tail gives the normalized
  saddle integral `(sqrt (2 * pi))⁻¹ * ∫ K = 1 + O (1 / b)`.

The remaining declarations are Gaussian-moment and coefficient plumbing for
those statements.

## Conventions

`QuantitativeSaddle.standardGaussian` is `exp (-v ^ 2 / 2)` carrying no
`1 / sqrt (2 * pi)`; that normalization is applied once, in the last theorem.
The smallness hypotheses `‖oddPhase a c v‖ ≤ 1` and `‖R v‖ ≤ 1` are what the
Mathlib exponential estimates require, they do not follow from the size
hypotheses, and callers must discharge them on the arc they use.  Every
constant is sufficient rather than sharp; they come from
`(x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2` and the crude `‖exp w - 1‖ ≤ 2 * ‖w‖`.
-/

set_option autoImplicit false

open Filter Set MeasureTheory Asymptotics
open scoped Topology

namespace Fabius

namespace SaddleCentral

/-- The imaginary linear-plus-cubic term in the scaled saddle exponent. -/
noncomputable def oddPhase (a c v : ℝ) : ℂ :=
  ((a * v + c * v ^ 3 : ℝ) : ℂ) * Complex.I

/-- The odd correction which must be retained before taking the central
`L¹` error. -/
noncomputable def oddCorrection (a c v : ℝ) : ℂ :=
  QuantitativeSaddle.standardGaussian v * oddPhase a c v

lemma oddPhase_neg (a c v : ℝ) : oddPhase a c (-v) = -oddPhase a c v := by
  simp [oddPhase]
  ring

@[simp] lemma oddPhase_re (a c v : ℝ) : (oddPhase a c v).re = 0 := by
  simp [oddPhase, Complex.mul_re, pow_succ]

lemma norm_oddPhase (a c v : ℝ) : ‖oddPhase a c v‖ = |a * v + c * v ^ 3| := by
  simp only [oddPhase, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs]

lemma oddCorrection_odd (a c : ℝ) : Function.Odd (oddCorrection a c) := by
  intro v
  rw [oddCorrection, oddCorrection, oddPhase_neg]
  simp only [QuantitativeSaddle.standardGaussian]
  rw [neg_sq]
  ring

lemma integrable_gaussian_mul_pow (n : ℕ) :
    Integrable (fun v : ℝ => Real.exp (-(v ^ 2) / 2) * v ^ n) := by
  have hs : (-1 : ℝ) < (n : ℝ) := by
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have h := integrable_rpow_mul_exp_neg_mul_sq
    (b := (1 / 2 : ℝ)) (s := (n : ℝ)) (by norm_num)
    hs
  convert h using 1
  funext v
  rw [Real.rpow_natCast]
  ring_nf

lemma integrable_oddCorrection (a c : ℝ) : Integrable (oddCorrection a c) := by
  have hreal : Integrable
      (fun v : ℝ => Real.exp (-(v ^ 2) / 2) * (a * v + c * v ^ 3)) := by
    have hsum := (integrable_gaussian_mul_pow 1).mul_const a |>.add
      ((integrable_gaussian_mul_pow 3).mul_const c)
    refine hsum.congr ?_
    filter_upwards with v
    simp only [Pi.add_apply, pow_one]
    ring
  have hcomplex := hreal.ofReal.mul_const Complex.I
  refine hcomplex.congr ?_
  filter_upwards with v
  change
    ((Real.exp (-(v ^ 2) / 2) * (a * v + c * v ^ 3) : ℝ) : ℂ) * Complex.I =
      (Real.exp (-(v ^ 2) / 2) : ℂ) *
        (((a * v + c * v ^ 3 : ℝ) : ℂ) * Complex.I)
  rw [Complex.ofReal_mul]
  ring

/-- A second-order estimate for the exponential after separating a purely
imaginary first-order term from a small remainder. -/
lemma norm_exp_add_sub_one_sub_le
    (u w : ℂ) (huRe : u.re = 0) (hu : ‖u‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    ‖Complex.exp (u + w) - (1 + u)‖ ≤ ‖u‖ ^ 2 + 2 * ‖w‖ := by
  have hexpu : ‖Complex.exp u‖ = 1 := by
    rw [Complex.norm_exp, huRe, Real.exp_zero]
  have hwexp := Complex.norm_exp_sub_one_le hw
  have huexp := Complex.norm_exp_sub_one_sub_id_le hu
  calc
    ‖Complex.exp (u + w) - (1 + u)‖ =
        ‖Complex.exp u * (Complex.exp w - 1) +
          (Complex.exp u - 1 - u)‖ := by
            rw [Complex.exp_add]
            congr 1
            ring
    _ ≤ ‖Complex.exp u * (Complex.exp w - 1)‖ +
          ‖Complex.exp u - 1 - u‖ := norm_add_le _ _
    _ = ‖Complex.exp w - 1‖ + ‖Complex.exp u - 1 - u‖ := by
          rw [norm_mul, hexpu, one_mul]
    _ ≤ 2 * ‖w‖ + ‖u‖ ^ 2 := add_le_add hwexp huexp
    _ = ‖u‖ ^ 2 + 2 * ‖w‖ := by ring

/-- A fixed integrable majorant for the error left after removing a bounded
linear-plus-cubic odd term and a quadratic-plus-quartic remainder. -/
noncomputable def centralMajorant
    (Clinear Ccubic Cquadratic Cquartic v : ℝ) : ℝ :=
  Real.exp (-(v ^ 2) / 2) *
    ((2 * Clinear ^ 2 + 2 * Cquadratic) * v ^ 2 +
      2 * Cquartic * v ^ 4 + 2 * Ccubic ^ 2 * v ^ 6)

lemma centralMajorant_nonneg
    (Clinear Ccubic Cquadratic Cquartic v : ℝ)
    (hCquadratic : 0 ≤ Cquadratic) (hCquartic : 0 ≤ Cquartic) :
    0 ≤ centralMajorant Clinear Ccubic Cquadratic Cquartic v := by
  unfold centralMajorant
  have hv2 : 0 ≤ v ^ 2 := sq_nonneg v
  have hv4 : 0 ≤ v ^ 4 := by positivity
  have hv6 : 0 ≤ v ^ 6 := by positivity
  have hlin : 0 ≤ 2 * Clinear ^ 2 + 2 * Cquadratic := by positivity
  positivity

lemma integrable_centralMajorant
    (Clinear Ccubic Cquadratic Cquartic : ℝ) :
    Integrable (centralMajorant Clinear Ccubic Cquadratic Cquartic) := by
  have h2 := (integrable_gaussian_mul_pow 2).mul_const
    (2 * Clinear ^ 2 + 2 * Cquadratic)
  have h4 := (integrable_gaussian_mul_pow 4).mul_const (2 * Cquartic)
  have h6 := (integrable_gaussian_mul_pow 6).mul_const (2 * Ccubic ^ 2)
  refine (h2.add h4 |>.add h6).congr ?_
  filter_upwards with v
  simp only [Pi.add_apply, centralMajorant]
  ring

lemma oddPhase_sq_le_div
    (b a c Clinear Ccubic v : ℝ) (hb : 0 < b)
    (ha : b * a ^ 2 ≤ Clinear ^ 2)
    (hc : b * c ^ 2 ≤ Ccubic ^ 2) :
    ‖oddPhase a c v‖ ^ 2 ≤
      (2 * Clinear ^ 2 * v ^ 2 + 2 * Ccubic ^ 2 * v ^ 6) / b := by
  have hax : b * (a * v) ^ 2 ≤ Clinear ^ 2 * v ^ 2 := by
    calc
      b * (a * v) ^ 2 = (b * a ^ 2) * v ^ 2 := by ring
      _ ≤ Clinear ^ 2 * v ^ 2 :=
        mul_le_mul_of_nonneg_right ha (sq_nonneg v)
  have hcx : b * (c * v ^ 3) ^ 2 ≤ Ccubic ^ 2 * v ^ 6 := by
    calc
      b * (c * v ^ 3) ^ 2 = (b * c ^ 2) * (v ^ 3) ^ 2 := by ring
      _ ≤ Ccubic ^ 2 * (v ^ 3) ^ 2 :=
        mul_le_mul_of_nonneg_right hc (sq_nonneg (v ^ 3))
      _ = Ccubic ^ 2 * v ^ 6 := by ring
  have hsumSq : (a * v + c * v ^ 3) ^ 2 ≤
      2 * (a * v) ^ 2 + 2 * (c * v ^ 3) ^ 2 := by
    nlinarith [sq_nonneg (a * v - c * v ^ 3)]
  have hscaled : b * (a * v + c * v ^ 3) ^ 2 ≤
      2 * Clinear ^ 2 * v ^ 2 + 2 * Ccubic ^ 2 * v ^ 6 := by
    have := mul_le_mul_of_nonneg_left hsumSq hb.le
    nlinarith
  rw [norm_oddPhase, sq_abs]
  apply (le_div_iff₀ hb).2
  simpa only [mul_comm] using hscaled

/-- Pointwise corrected-kernel estimate.  This is the analytic core of the
central saddle argument: bounded linear and cubic coefficients contribute
only through their square after their odd first-order part is retained. -/
theorem norm_sub_gaussian_add_oddCorrection_le
    (K R : ℝ → ℂ)
    (b a c Clinear Ccubic Cquadratic Cquartic v : ℝ)
    (hb : 0 < b)
    (ha : b * a ^ 2 ≤ Clinear ^ 2)
    (hc : b * c ^ 2 ≤ Ccubic ^ 2)
    (hrepresentation :
      K v = QuantitativeSaddle.standardGaussian v *
        Complex.exp (oddPhase a c v + R v))
    (hphaseSmall : ‖oddPhase a c v‖ ≤ 1)
    (hremainderSmall : ‖R v‖ ≤ 1)
    (hremainder :
      ‖R v‖ ≤ (Cquadratic * v ^ 2 + Cquartic * v ^ 4) / b) :
    ‖K v - (QuantitativeSaddle.standardGaussian v + oddCorrection a c v)‖ ≤
      centralMajorant Clinear Ccubic Cquadratic Cquartic v / b := by
  have hGaussianNorm : ‖QuantitativeSaddle.standardGaussian v‖ =
      Real.exp (-(v ^ 2) / 2) := by
    simp only [QuantitativeSaddle.standardGaussian, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hphase := oddPhase_sq_le_div b a c Clinear Ccubic v hb ha hc
  have hexp := norm_exp_add_sub_one_sub_le
    (oddPhase a c v) (R v) (oddPhase_re a c v) hphaseSmall hremainderSmall
  have hinside :
      ‖oddPhase a c v‖ ^ 2 + 2 * ‖R v‖ ≤
        ((2 * Clinear ^ 2 + 2 * Cquadratic) * v ^ 2 +
          2 * Cquartic * v ^ 4 + 2 * Ccubic ^ 2 * v ^ 6) / b := by
    calc
      ‖oddPhase a c v‖ ^ 2 + 2 * ‖R v‖ ≤
          (2 * Clinear ^ 2 * v ^ 2 + 2 * Ccubic ^ 2 * v ^ 6) / b +
            2 * ((Cquadratic * v ^ 2 + Cquartic * v ^ 4) / b) :=
        add_le_add hphase (mul_le_mul_of_nonneg_left hremainder (by norm_num))
      _ = ((2 * Clinear ^ 2 + 2 * Cquadratic) * v ^ 2 +
          2 * Cquartic * v ^ 4 + 2 * Ccubic ^ 2 * v ^ 6) / b := by ring
  calc
    ‖K v - (QuantitativeSaddle.standardGaussian v + oddCorrection a c v)‖ =
        ‖QuantitativeSaddle.standardGaussian v *
          (Complex.exp (oddPhase a c v + R v) - (1 + oddPhase a c v))‖ := by
      rw [hrepresentation]
      simp only [oddCorrection]
      congr 1
      ring
    _ = Real.exp (-(v ^ 2) / 2) *
        ‖Complex.exp (oddPhase a c v + R v) - (1 + oddPhase a c v)‖ := by
      rw [norm_mul, hGaussianNorm]
    _ ≤ Real.exp (-(v ^ 2) / 2) *
        (‖oddPhase a c v‖ ^ 2 + 2 * ‖R v‖) := by
      exact mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
    _ ≤ Real.exp (-(v ^ 2) / 2) *
        (((2 * Clinear ^ 2 + 2 * Cquadratic) * v ^ 2 +
          2 * Cquartic * v ^ 4 + 2 * Ccubic ^ 2 * v ^ 6) / b) := by
      exact mul_le_mul_of_nonneg_left hinside (Real.exp_pos _).le
    _ = centralMajorant Clinear Ccubic Cquadratic Cquartic v / b := by
      unfold centralMajorant
      ring

/-- Integrated central-arc estimate with a constant independent of the arc.
The right side is the full Gaussian-polynomial moment divided by `b`. -/
theorem integral_norm_sub_gaussian_add_oddCorrection_le
    (K R : ℝ → ℂ) (central : Set ℝ)
    (b a c Clinear Ccubic Cquadratic Cquartic : ℝ)
    (hb : 0 < b)
    (ha : b * a ^ 2 ≤ Clinear ^ 2)
    (hc : b * c ^ 2 ≤ Ccubic ^ 2)
    (hCquadratic : 0 ≤ Cquadratic) (hCquartic : 0 ≤ Cquartic)
    (hcentralMeas : MeasurableSet central)
    (hK : IntegrableOn K central)
    (hrepresentation : ∀ v ∈ central,
      K v = QuantitativeSaddle.standardGaussian v *
        Complex.exp (oddPhase a c v + R v))
    (hphaseSmall : ∀ v ∈ central, ‖oddPhase a c v‖ ≤ 1)
    (hremainderSmall : ∀ v ∈ central, ‖R v‖ ≤ 1)
    (hremainder : ∀ v ∈ central,
      ‖R v‖ ≤ (Cquadratic * v ^ 2 + Cquartic * v ^ 4) / b) :
    (∫ v in central,
      ‖K v - (QuantitativeSaddle.standardGaussian v + oddCorrection a c v)‖) ≤
      (∫ v : ℝ, centralMajorant Clinear Ccubic Cquadratic Cquartic v) / b := by
  let reference : ℝ → ℂ := fun v =>
    QuantitativeSaddle.standardGaussian v + oddCorrection a c v
  have hreference : Integrable reference :=
    QuantitativeSaddle.integrable_standardGaussian.add
      (integrable_oddCorrection a c)
  have hleft : IntegrableOn (fun v => ‖K v - reference v‖) central :=
    (hK.sub hreference.integrableOn).norm
  let majorant : ℝ → ℝ :=
    centralMajorant Clinear Ccubic Cquadratic Cquartic
  have hmajorant : Integrable majorant :=
    integrable_centralMajorant Clinear Ccubic Cquadratic Cquartic
  have hmajorantDiv : IntegrableOn (fun v => majorant v / b) central :=
    (hmajorant.div_const b).integrableOn
  have hpointwise : ∀ v ∈ central,
      ‖K v - reference v‖ ≤ majorant v / b := by
    intro v hv
    exact norm_sub_gaussian_add_oddCorrection_le K R
      b a c Clinear Ccubic Cquadratic Cquartic v hb ha hc
      (hrepresentation v hv) (hphaseSmall v hv) (hremainderSmall v hv)
      (hremainder v hv)
  have hcentralBound :
      (∫ v in central, ‖K v - reference v‖) ≤
        (∫ v in central, majorant v) / b := by
    have hmono := setIntegral_mono_on hleft hmajorantDiv hcentralMeas hpointwise
    rw [integral_div] at hmono
    exact hmono
  have hmajorantNonneg : ∀ v, 0 ≤ majorant v := fun v =>
    centralMajorant_nonneg Clinear Ccubic Cquadratic Cquartic v
      hCquadratic hCquartic
  have hrestrict :
      (∫ v in central, majorant v) ≤ ∫ v : ℝ, majorant v :=
    integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall hmajorantNonneg) hmajorant
  change (∫ v in central, ‖K v - reference v‖) ≤ _
  exact hcentralBound.trans
    ((div_le_div_iff_of_pos_right hb).2 hrestrict)

/-- Filter form of the corrected central estimate.  The two scaled
coefficient hypotheses say precisely that the linear and cubic coefficients
are `O(b⁻¹/²)`; the remainder hypothesis allows `O(v²/b + v⁴/b)`. -/
theorem central_corrected_error_isBigO
    {α : Type*} (l : Filter α)
    (K R : α → ℝ → ℂ) (central : α → Set ℝ)
    (b a c : α → ℝ)
    (Clinear Ccubic Cquadratic Cquartic : ℝ)
    (hCquadratic : 0 ≤ Cquadratic) (hCquartic : 0 ≤ Cquartic)
    (hb : ∀ᶠ i in l, 0 < b i)
    (ha : ∀ᶠ i in l, b i * (a i) ^ 2 ≤ Clinear ^ 2)
    (hc : ∀ᶠ i in l, b i * (c i) ^ 2 ≤ Ccubic ^ 2)
    (hcentralMeas : ∀ᶠ i in l, MeasurableSet (central i))
    (hK : ∀ᶠ i in l, IntegrableOn (K i) (central i))
    (hrepresentation : ∀ᶠ i in l, ∀ v ∈ central i,
      K i v = QuantitativeSaddle.standardGaussian v *
        Complex.exp (oddPhase (a i) (c i) v + R i v))
    (hphaseSmall : ∀ᶠ i in l, ∀ v ∈ central i,
      ‖oddPhase (a i) (c i) v‖ ≤ 1)
    (hremainderSmall : ∀ᶠ i in l, ∀ v ∈ central i, ‖R i v‖ ≤ 1)
    (hremainder : ∀ᶠ i in l, ∀ v ∈ central i,
      ‖R i v‖ ≤
        (Cquadratic * v ^ 2 + Cquartic * v ^ 4) / b i) :
    (fun i => ∫ v in central i,
      ‖K i v - (QuantitativeSaddle.standardGaussian v +
        oddCorrection (a i) (c i) v)‖) =O[l]
      (fun i => (b i)⁻¹) := by
  let M : ℝ := ∫ v : ℝ,
    centralMajorant Clinear Ccubic Cquadratic Cquartic v
  apply IsBigO.of_bound M
  filter_upwards [hb, ha, hc, hcentralMeas, hK, hrepresentation,
    hphaseSmall, hremainderSmall, hremainder] with
    i hbi hai hci hmeas hKi hrep hphase hremSmall hrem
  have hbound := integral_norm_sub_gaussian_add_oddCorrection_le
    (K i) (R i) (central i) (b i) (a i) (c i)
    Clinear Ccubic Cquadratic Cquartic hbi hai hci
    hCquadratic hCquartic hmeas hKi hrep hphase hremSmall hrem
  have hleftNonneg : 0 ≤ ∫ v in central i,
      ‖K i v - (QuantitativeSaddle.standardGaussian v +
        oddCorrection (a i) (c i) v)‖ :=
    integral_nonneg fun _ => norm_nonneg _
  have hinvNorm : ‖(b i)⁻¹‖ = (b i)⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hbi)]
  rw [Real.norm_eq_abs, abs_of_nonneg hleftNonneg, hinvNorm]
  simpa only [M, div_eq_mul_inv] using hbound

/-- The corrected central estimate on the standardized Fabius radius
`√(32 log b)`.  Smallness of the Taylor terms is kept explicit, so it can be
discharged separately from Lambert-phase asymptotics. -/
theorem standardRadius_central_corrected_error_isBigO
    {α : Type*} (l : Filter α)
    (K R : α → ℝ → ℂ) (b a c : α → ℝ)
    (Clinear Ccubic Cquadratic Cquartic : ℝ)
    (hCquadratic : 0 ≤ Cquadratic) (hCquartic : 0 ≤ Cquartic)
    (hb : ∀ᶠ i in l, 0 < b i)
    (ha : ∀ᶠ i in l, b i * (a i) ^ 2 ≤ Clinear ^ 2)
    (hc : ∀ᶠ i in l, b i * (c i) ^ 2 ≤ Ccubic ^ 2)
    (hK : ∀ᶠ i in l, Integrable (K i))
    (hrepresentation : ∀ᶠ i in l,
      ∀ v ∈ Icc (-(fabiusSaddleCentralRadius (b i)))
        (fabiusSaddleCentralRadius (b i)),
      K i v = QuantitativeSaddle.standardGaussian v *
        Complex.exp (oddPhase (a i) (c i) v + R i v))
    (hphaseSmall : ∀ᶠ i in l,
      ∀ v ∈ Icc (-(fabiusSaddleCentralRadius (b i)))
        (fabiusSaddleCentralRadius (b i)),
      ‖oddPhase (a i) (c i) v‖ ≤ 1)
    (hremainderSmall : ∀ᶠ i in l,
      ∀ v ∈ Icc (-(fabiusSaddleCentralRadius (b i)))
        (fabiusSaddleCentralRadius (b i)),
      ‖R i v‖ ≤ 1)
    (hremainder : ∀ᶠ i in l,
      ∀ v ∈ Icc (-(fabiusSaddleCentralRadius (b i)))
        (fabiusSaddleCentralRadius (b i)),
      ‖R i v‖ ≤
        (Cquadratic * v ^ 2 + Cquartic * v ^ 4) / b i) :
    (fun i => ∫ v in Icc (-(fabiusSaddleCentralRadius (b i)))
        (fabiusSaddleCentralRadius (b i)),
      ‖K i v - (QuantitativeSaddle.standardGaussian v +
        oddCorrection (a i) (c i) v)‖) =O[l]
      (fun i => (b i)⁻¹) := by
  apply central_corrected_error_isBigO l K R
    (fun i => Icc (-(fabiusSaddleCentralRadius (b i)))
      (fabiusSaddleCentralRadius (b i))) b a c
    Clinear Ccubic Cquadratic Cquartic hCquadratic hCquartic
    hb ha hc
  · exact Filter.Eventually.of_forall fun _ => measurableSet_Icc
  · filter_upwards [hK] with i hKi
    exact hKi.integrableOn
  · exact hrepresentation
  · exact hphaseSmall
  · exact hremainderSmall
  · exact hremainder

/-- Central Taylor control plus a corrected complementary-tail bound gives
the normalized saddle integral `1 + O(1/b)`.  This is the direct interface to
`QuantitativeSaddle.normalized_integral_sub_one_isBigO_of_central_tail_odd_correction`. -/
theorem normalized_integral_sub_one_isBigO_of_standardRadius_taylor
    {α : Type*} (l : Filter α)
    (K R : α → ℝ → ℂ) (b a c : α → ℝ)
    (Clinear Ccubic Cquadratic Cquartic Ctail : ℝ)
    (hCquadratic : 0 ≤ Cquadratic) (hCquartic : 0 ≤ Cquartic)
    (hb : ∀ᶠ i in l, 0 < b i)
    (ha : ∀ᶠ i in l, b i * (a i) ^ 2 ≤ Clinear ^ 2)
    (hc : ∀ᶠ i in l, b i * (c i) ^ 2 ≤ Ccubic ^ 2)
    (hK : ∀ᶠ i in l, Integrable (K i))
    (hrepresentation : ∀ᶠ i in l,
      ∀ v ∈ Icc (-(fabiusSaddleCentralRadius (b i)))
        (fabiusSaddleCentralRadius (b i)),
      K i v = QuantitativeSaddle.standardGaussian v *
        Complex.exp (oddPhase (a i) (c i) v + R i v))
    (hphaseSmall : ∀ᶠ i in l,
      ∀ v ∈ Icc (-(fabiusSaddleCentralRadius (b i)))
        (fabiusSaddleCentralRadius (b i)),
      ‖oddPhase (a i) (c i) v‖ ≤ 1)
    (hremainderSmall : ∀ᶠ i in l,
      ∀ v ∈ Icc (-(fabiusSaddleCentralRadius (b i)))
        (fabiusSaddleCentralRadius (b i)),
      ‖R i v‖ ≤ 1)
    (hremainder : ∀ᶠ i in l,
      ∀ v ∈ Icc (-(fabiusSaddleCentralRadius (b i)))
        (fabiusSaddleCentralRadius (b i)),
      ‖R i v‖ ≤
        (Cquadratic * v ^ 2 + Cquartic * v ^ 4) / b i)
    (htail : ∀ᶠ i in l,
      (∫ v in (Icc (-(fabiusSaddleCentralRadius (b i)))
          (fabiusSaddleCentralRadius (b i)))ᶜ,
        ‖K i v - (QuantitativeSaddle.standardGaussian v +
          oddCorrection (a i) (c i) v)‖) ≤ Ctail * (b i)⁻¹) :
    (fun i =>
      (Real.sqrt (2 * Real.pi) : ℂ)⁻¹ * (∫ v : ℝ, K i v) - 1) =O[l]
        (fun i => (b i)⁻¹) := by
  let central : α → Set ℝ := fun i =>
    Icc (-(fabiusSaddleCentralRadius (b i)))
      (fabiusSaddleCentralRadius (b i))
  let J : α → ℝ → ℂ := fun i => oddCorrection (a i) (c i)
  let M : ℝ := ∫ v : ℝ,
    centralMajorant Clinear Ccubic Cquadratic Cquartic v
  apply QuantitativeSaddle.normalized_integral_sub_one_isBigO_of_central_tail_odd_correction
    l b K J central M Ctail hb hK
  · exact Filter.Eventually.of_forall fun i => integrable_oddCorrection (a i) (c i)
  · exact Filter.Eventually.of_forall fun i => oddCorrection_odd (a i) (c i)
  · exact Filter.Eventually.of_forall fun _ => measurableSet_Icc
  · filter_upwards [hb, ha, hc, hK, hrepresentation, hphaseSmall,
      hremainderSmall, hremainder] with
      i hbi hai hci hKi hrep hphase hremSmall hrem
    have hbound := integral_norm_sub_gaussian_add_oddCorrection_le
      (K i) (R i) (central i) (b i) (a i) (c i)
      Clinear Ccubic Cquadratic Cquartic hbi hai hci
      hCquadratic hCquartic measurableSet_Icc hKi.integrableOn
      hrep hphase hremSmall hrem
    simpa only [central, J, M, div_eq_mul_inv] using hbound
  · simpa only [central, J] using htail

end SaddleCentral

end Fabius
