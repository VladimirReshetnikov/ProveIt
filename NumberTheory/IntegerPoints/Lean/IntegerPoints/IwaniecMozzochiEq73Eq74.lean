import IntegerPoints.IwaniecMozzochiReductionEq75
import IntegerPoints.GKLemma32
import IntegerPoints.Lemma9Tools
import IntegerPoints.PoissonIntegrals

/-!
# Iwaniec--Mozzochi (7.3)--(7.4): analytic foundations

The estimates (7.3) and (7.4) are oscillatory-integral estimates for a
piecewise-affine compactly supported weight and a reciprocal phase.  The paper
states both estimates without supplying their proofs.  The existing unweighted
second-derivative test handles the constant middle piece in (7.4) once the two
unit ramps are separated.  The genuinely missing analytic estimate is the
twice-integrated nonstationary-phase bound needed for the `c^2/k^2` half of
(7.3).

This file records the common formal input to those two arguments:

* the exact reciprocal presentation of `rPhase` and its first three
  derivatives;
* a version of integration by parts whose differentiability assumptions are
  local to the interval (the global assumptions of `PS.parts_phase` cannot
  hold across the pole `l = -m`);
* the four affine pieces, support, and range of the trapezoid;
* the exact decomposition into its two unit ramps and constant middle piece;
  and
* the integral-valued pole-separation consequence used on that support.

No estimate is claimed here merely from a strengthened analytic hypothesis.
The remaining proof of `iwaniecMozzochi_eq73_eq74` must establish the uniform
phase geometry from `InMainRange` and `InFareySet`, then prove the two missing
oscillatory-integral inequalities with absolute constants.
-/

open Real Set intervalIntegral MeasureTheory

namespace LeanProofs.IntegerPoints

namespace IwaniecMozzochiEq73Eq74

/-! ## Exact reciprocal phase and its derivatives -/

/-- The cancellation-friendly form of (7.1):
`r(l) = xh/(m+l) - xh/m + xh l/(m+v)^2`.

It agrees with `rPhase` away from the three denominators occurring in the two
presentations.  Writing the phase this way makes all derivatives transparent.
-/
noncomputable def section7ReciprocalPhase (x h m v l : ℝ) : ℝ :=
  x * h / (m + l) - x * h / m + (x * h / (m + v) ^ 2) * l

/-- The first derivative of the reciprocal phase. -/
noncomputable def section7ReciprocalPhaseDeriv (x h m v l : ℝ) : ℝ :=
  x * h / (m + v) ^ 2 - x * h / (m + l) ^ 2

/-- The second derivative of the reciprocal phase. -/
noncomputable def section7ReciprocalPhaseDeriv2 (x h m v l : ℝ) : ℝ :=
  2 * x * h / (m + l) ^ 3

/-- The third derivative of the reciprocal phase. -/
noncomputable def section7ReciprocalPhaseDeriv3 (x h m v l : ℝ) : ℝ :=
  -(6 * x * h) / (m + l) ^ 4

/-- The Fourier phase in (7.2)--(7.4), with the frequency represented by a
real parameter.  Applications use `k : ℤ` coerced to `ℝ`. -/
noncomputable def section7FourierPhase
    (x h m v c k l : ℝ) : ℝ :=
  section7ReciprocalPhase x h m v l + (k / c) * l

/-- The first derivative of `section7FourierPhase`. -/
noncomputable def section7FourierPhaseDeriv
    (x h m v c k l : ℝ) : ℝ :=
  section7ReciprocalPhaseDeriv x h m v l + k / c

/-- The paper's polynomial-over-reciprocal definition of `rPhase` is exactly
the cancellation-friendly reciprocal presentation away from its pole. -/
theorem rPhase_eq_section7ReciprocalPhase
    {x h m v l : ℝ} (hm : m ≠ 0) (hmv : m + v ≠ 0) (hml : m + l ≠ 0) :
    rPhase x h m v l = section7ReciprocalPhase x h m v l := by
  unfold rPhase section7ReciprocalPhase
  field_simp [hm, hmv, hml] <;> ring

/-- The phase occurring in `trapezoidIntegral` agrees with the reciprocal
Fourier phase on the pole-free region. -/
theorem rPhase_add_linear_eq_section7FourierPhase
    {x h m v c k l : ℝ} (hm : m ≠ 0) (hmv : m + v ≠ 0) (hml : m + l ≠ 0) :
    rPhase x h m v l + k * l / c =
      section7FourierPhase x h m v c k l := by
  rw [rPhase_eq_section7ReciprocalPhase hm hmv hml]
  unfold section7FourierPhase
  ring

/-- Exact first derivative of the reciprocal presentation. -/
theorem section7ReciprocalPhase_hasDerivAt
    {x h m v l : ℝ} (hml : m + l ≠ 0) :
    HasDerivAt (section7ReciprocalPhase x h m v)
      (section7ReciprocalPhaseDeriv x h m v l) l := by
  unfold section7ReciprocalPhase section7ReciprocalPhaseDeriv
  have hden : HasDerivAt (fun y : ℝ => m + y) 1 l :=
    (hasDerivAt_id l).const_add m
  have hmain :=
    (((hasDerivAt_const l (x * h)).div hden hml).sub_const (x * h / m)).add
      ((hasDerivAt_id l).const_mul (x * h / (m + v) ^ 2))
  convert! hmain using 1 <;> field_simp [hml] <;> ring

/-- Exact second derivative of the reciprocal presentation. -/
theorem section7ReciprocalPhaseDeriv_hasDerivAt
    {x h m v l : ℝ} (hml : m + l ≠ 0) :
    HasDerivAt (section7ReciprocalPhaseDeriv x h m v)
      (section7ReciprocalPhaseDeriv2 x h m v l) l := by
  unfold section7ReciprocalPhaseDeriv section7ReciprocalPhaseDeriv2
  have hden : HasDerivAt (fun y : ℝ => m + y) 1 l :=
    (hasDerivAt_id l).const_add m
  have hquot := (hasDerivAt_const l (x * h)).div (hden.pow 2)
    (pow_ne_zero 2 hml)
  convert! (hasDerivAt_const l (x * h / (m + v) ^ 2)).sub hquot using 1 <;>
    simp only [Pi.pow_apply] <;> field_simp [hml] <;> ring

/-- Exact third derivative of the reciprocal presentation. -/
theorem section7ReciprocalPhaseDeriv2_hasDerivAt
    {x h m v l : ℝ} (hml : m + l ≠ 0) :
    HasDerivAt (section7ReciprocalPhaseDeriv2 x h m v)
      (section7ReciprocalPhaseDeriv3 x h m v l) l := by
  unfold section7ReciprocalPhaseDeriv2 section7ReciprocalPhaseDeriv3
  have hden : HasDerivAt (fun y : ℝ => m + y) 1 l :=
    (hasDerivAt_id l).const_add m
  have hquot := (hasDerivAt_const l (2 * x * h)).div (hden.pow 3)
    (pow_ne_zero 3 hml)
  convert! hquot using 1 <;> simp only [Pi.pow_apply] <;>
    field_simp [hml] <;> ring

/-- Exact first derivative of the complete Fourier phase. -/
theorem section7FourierPhase_hasDerivAt
    {x h m v c k l : ℝ} (hml : m + l ≠ 0) :
    HasDerivAt (section7FourierPhase x h m v c k)
      (section7FourierPhaseDeriv x h m v c k l) l := by
  unfold section7FourierPhase section7FourierPhaseDeriv
  convert! (section7ReciprocalPhase_hasDerivAt
      (x := x) (h := h) (m := m) (v := v) hml).add
      (hasDerivAt_const_mul (x := l) (k / c)) using 1

/-- Exact second derivative of the complete Fourier phase. -/
theorem section7FourierPhaseDeriv_hasDerivAt
    {x h m v c k l : ℝ} (hml : m + l ≠ 0) :
    HasDerivAt (section7FourierPhaseDeriv x h m v c k)
      (section7ReciprocalPhaseDeriv2 x h m v l) l := by
  unfold section7FourierPhaseDeriv
  simpa using (section7ReciprocalPhaseDeriv_hasDerivAt hml).add_const (k / c)

/-- Exact third derivative of the complete Fourier phase. -/
theorem section7FourierPhaseDeriv2_hasDerivAt
    {x h m v l : ℝ} (hml : m + l ≠ 0) :
    HasDerivAt (section7ReciprocalPhaseDeriv2 x h m v)
      (section7ReciprocalPhaseDeriv3 x h m v l) l :=
  section7ReciprocalPhaseDeriv2_hasDerivAt hml

/-- The reciprocal Fourier phase is `C^3` on the correct side of its pole. -/
theorem section7FourierPhase_contDiffOn_three
    (x h m v c k : ℝ) :
    ContDiffOn ℝ 3 (section7FourierPhase x h m v c k) (Ioi (-m)) := by
  unfold section7FourierPhase section7ReciprocalPhase
  fun_prop (disch := first | positivity | grind [Set.mem_Ioi])

/-! ## A global smooth extension for the existing van der Corput API -/

/-- A globally smooth version of the reciprocal Fourier phase.  The positive
smooth denominator `L9.hfun` equals its argument above `1/2`, so this extension
agrees with the original phase throughout the effective trapezoid support. -/
noncomputable def section7SmoothFourierPhase
    (x h m v c k l : ℝ) : ℝ :=
  L9.ftest (x * h) (m + l) - x * h / m +
    (x * h / (m + v) ^ 2) * l + (k / c) * l

/-- The smooth extension is globally `C^3`; in particular it meets the global
regularity hypothesis of `gk_lemma32_holds`. -/
theorem section7SmoothFourierPhase_contDiff_three
    (x h m v c k : ℝ) :
    ContDiff ℝ 3 (section7SmoothFourierPhase x h m v c k) := by
  unfold section7SmoothFourierPhase
  exact ((((L9.ftest_contDiff_nat (x * h) 3).comp
      (contDiff_const.add contDiff_id)).sub contDiff_const).add
        (contDiff_const.mul contDiff_id)).add
      (contDiff_const.mul contDiff_id)

/-- Pointwise agreement of the smooth and reciprocal phases on the safe side
of the cutoff. -/
theorem section7SmoothFourierPhase_eq
    {x h m v c k l : ℝ} (hl : 1 / 2 ≤ m + l) :
    section7SmoothFourierPhase x h m v c k l =
      section7FourierPhase x h m v c k l := by
  unfold section7SmoothFourierPhase section7FourierPhase
    section7ReciprocalPhase L9.ftest
  rw [L9.hfun_eq hl]

/-- Local agreement near every point strictly above the smooth cutoff. -/
theorem section7SmoothFourierPhase_eventuallyEq
    {x h m v c k l : ℝ} (hl : 1 / 2 < m + l) :
    section7SmoothFourierPhase x h m v c k =ᶠ[nhds l]
      section7FourierPhase x h m v c k := by
  have hcont : ContinuousAt (fun y : ℝ => m + y) l :=
    continuousAt_const.add continuousAt_id
  have hevent : ∀ᶠ y in nhds l, 1 / 2 < m + y :=
    hcont.eventually (Ioi_mem_nhds hl)
  filter_upwards [hevent] with y hy
  exact section7SmoothFourierPhase_eq hy.le

/-- The second iterated derivative of the reciprocal Fourier phase on its
pole-free region. -/
theorem section7FourierPhase_iteratedDeriv_two
    {x h m v c k l : ℝ} (hml : m + l ≠ 0) :
    iteratedDeriv 2 (section7FourierPhase x h m v c k) l =
      section7ReciprocalPhaseDeriv2 x h m v l := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hcont : ContinuousAt (fun y : ℝ => m + y) l :=
    continuousAt_const.add continuousAt_id
  have hevent : ∀ᶠ y in nhds l, m + y ≠ 0 :=
    hcont.eventually_ne hml
  have hderiv : deriv (section7FourierPhase x h m v c k) =ᶠ[nhds l]
      section7FourierPhaseDeriv x h m v c k := by
    filter_upwards [hevent] with y hy
    exact (section7FourierPhase_hasDerivAt hy).deriv
  rw [hderiv.deriv_eq]
  exact (section7FourierPhaseDeriv_hasDerivAt hml).deriv

/-- On the actual phase region, the global smooth extension has the expected
positive second derivative `2xh/(m+l)^3`. -/
theorem section7SmoothFourierPhase_iteratedDeriv_two
    {x h m v c k l : ℝ} (hl : 1 / 2 < m + l) :
    iteratedDeriv 2 (section7SmoothFourierPhase x h m v c k) l =
      section7ReciprocalPhaseDeriv2 x h m v l := by
  rw [(section7SmoothFourierPhase_eventuallyEq hl).iteratedDeriv_eq 2]
  exact section7FourierPhase_iteratedDeriv_two (by linarith)

/-- The already-proved Graham--Kolesnik second-derivative test applies to the
reciprocal phase after passing through the smooth extension.  This theorem is
the exact analytic reduction needed on the constant middle piece of the
trapezoid; the two remaining hypotheses are purely phase geometry. -/
theorem exists_section7_unweighted_second_derivative_bound :
    ∃ C : ℝ, ∀ (x h m v c k p q lam₂ : ℝ),
      p ≤ q → 0 < lam₂ →
      (∀ y ∈ Icc p q, 1 / 2 < m + y) →
      (∀ y ∈ Icc p q,
        lam₂ ≤ |section7ReciprocalPhaseDeriv2 x h m v y|) →
      ‖∫ y in p..q, e (section7FourierPhase x h m v c k y)‖ ≤
        C * lam₂ ^ (-(1 : ℝ) / 2) := by
  obtain ⟨C, hC⟩ := gk_lemma32_holds
  refine ⟨C, ?_⟩
  intro x h m v c k p q lam₂ hpq hlam₂ hsafe hcurv
  have hsmooth : ContDiff ℝ 2 (section7SmoothFourierPhase x h m v c k) :=
    (section7SmoothFourierPhase_contDiff_three x h m v c k).of_le (by norm_num)
  have hbound := hC p q lam₂ (section7SmoothFourierPhase x h m v c k)
    hpq hlam₂ hsmooth (fun y hy => by
      rw [section7SmoothFourierPhase_iteratedDeriv_two (hsafe y hy)]
      exact hcurv y hy)
  have heq :
      (∫ y in p..q, e (section7FourierPhase x h m v c k y)) =
        ∫ y in p..q, e (section7SmoothFourierPhase x h m v c k y) := by
    apply integral_congr
    intro y hy
    have hy' : y ∈ Icc p q := by
      simpa [uIcc_of_le hpq] using hy
    exact congrArg e (section7SmoothFourierPhase_eq (hsafe y hy').le).symm
  rw [heq]
  exact hbound

/-! ## Integration by parts local to a pole-free interval -/

/-- Local form of `PS.parts_phase`.

The original lemma assumes both derivative identities on all of `ℝ`.  That
is unnecessarily strong for interval integration and rules out the reciprocal
phase, whose pole lies outside the interval of integration. -/
theorem parts_phase_on
    {phi phi' phi'' : ℝ → ℝ} {p q : ℝ} (hpq : p ≤ q)
    (hphi : ∀ y ∈ Icc p q, HasDerivAt phi (phi' y) y)
    (hphi' : ∀ y ∈ Icc p q, HasDerivAt phi' (phi'' y) y)
    (hphi'c : ContinuousOn phi' (Icc p q))
    (hphi''c : ContinuousOn phi'' (Icc p q))
    (hne : ∀ y ∈ Icc p q, phi' y ≠ 0) :
    ∫ y in p..q, e (phi y) =
      e (phi q) * ((1 / phi' q : ℝ) : ℂ) / (2 * π * Complex.I) -
        e (phi p) * ((1 / phi' p : ℝ) : ℂ) / (2 * π * Complex.I) +
        (1 / (2 * π * Complex.I)) *
          ∫ y in p..q, e (phi y) * ((phi'' y / (phi' y) ^ 2 : ℝ) : ℂ) := by
  have hI : (2 * π * Complex.I : ℂ) ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  have hIcc : uIcc p q = Icc p q := uIcc_of_le hpq
  have hu : ∀ y ∈ uIcc p q,
      HasDerivAt (fun y => ((1 / phi' y : ℝ) : ℂ) / (2 * π * Complex.I))
        (((-phi'' y / (phi' y) ^ 2 : ℝ) : ℂ) / (2 * π * Complex.I)) y := by
    intro y hy
    rw [hIcc] at hy
    have h1 : HasDerivAt (fun y => (phi' y)⁻¹)
        (-phi'' y / (phi' y) ^ 2) y := (hphi' y hy).inv (hne y hy)
    have h2 := h1.ofReal_comp.div_const (2 * π * Complex.I)
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
    simp only [one_div]
  have hv : ∀ y ∈ uIcc p q,
      HasDerivAt (fun y => e (phi y))
        (2 * π * Complex.I * phi' y * e (phi y)) y := by
    intro y hy
    rw [hIcc] at hy
    exact PS.hasDerivAt_e_comp (hphi y hy)
  have hcont1 : ContinuousOn
      (fun y => ((-phi'' y / (phi' y) ^ 2 : ℝ) : ℂ) /
        (2 * π * Complex.I)) (uIcc p q) := by
    rw [hIcc]
    apply ContinuousOn.div_const
    apply Complex.continuous_ofReal.comp_continuousOn
    apply ContinuousOn.div hphi''c.neg (hphi'c.pow 2)
    intro y hy
    exact pow_ne_zero 2 (hne y hy)
  have hphic : ContinuousOn phi (Icc p q) := by
    intro y hy
    exact (hphi y hy).continuousAt.continuousWithinAt
  have hec : ContinuousOn (fun y => e (phi y)) (Icc p q) := by
    unfold e
    exact Complex.continuous_exp.comp_continuousOn
      (continuousOn_const.mul
        (Complex.continuous_ofReal.comp_continuousOn hphic))
  have hcont2 : ContinuousOn
      (fun y => 2 * π * Complex.I * phi' y * e (phi y)) (uIcc p q) := by
    rw [hIcc]
    exact (continuousOn_const.mul
      (Complex.continuous_ofReal.comp_continuousOn hphi'c)).mul hec
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    hcont1.intervalIntegrable hcont2.intervalIntegrable
  have hleft : ∫ y in p..q,
      ((1 / phi' y : ℝ) : ℂ) / (2 * π * Complex.I) *
        (2 * π * Complex.I * phi' y * e (phi y)) =
      ∫ y in p..q, e (phi y) := by
    apply integral_congr
    intro y hy
    rw [hIcc] at hy
    simp only
    have hy0 : (phi' y : ℂ) ≠ 0 := by exact_mod_cast hne y hy
    push_cast
    field_simp
  have hright : ∫ y in p..q,
      ((-phi'' y / (phi' y) ^ 2 : ℝ) : ℂ) / (2 * π * Complex.I) * e (phi y) =
      -((1 / (2 * π * Complex.I)) *
        ∫ y in p..q, e (phi y) * ((phi'' y / (phi' y) ^ 2 : ℝ) : ℂ)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_neg]
    apply integral_congr
    intro y _
    simp only
    push_cast
    ring
  rw [hleft, hright] at hparts
  rw [hparts]
  ring

/-- Integration by parts for the reciprocal Fourier phase on any interval
lying strictly to the right of its pole. -/
theorem section7FourierPhase_parts
    {x h m v c k p q : ℝ} (hpq : p ≤ q) (hpole : -m < p)
    (hne : ∀ y ∈ Icc p q, section7FourierPhaseDeriv x h m v c k y ≠ 0) :
    ∫ y in p..q, e (section7FourierPhase x h m v c k y) =
      e (section7FourierPhase x h m v c k q) *
          ((1 / section7FourierPhaseDeriv x h m v c k q : ℝ) : ℂ) /
            (2 * π * Complex.I) -
        e (section7FourierPhase x h m v c k p) *
          ((1 / section7FourierPhaseDeriv x h m v c k p : ℝ) : ℂ) /
            (2 * π * Complex.I) +
        (1 / (2 * π * Complex.I)) *
          ∫ y in p..q, e (section7FourierPhase x h m v c k y) *
            ((section7ReciprocalPhaseDeriv2 x h m v y /
              (section7FourierPhaseDeriv x h m v c k y) ^ 2 : ℝ) : ℂ) := by
  apply parts_phase_on hpq
  · intro y hy
    apply section7FourierPhase_hasDerivAt
    have : -m < y := hpole.trans_le hy.1
    linarith
  · intro y hy
    apply section7FourierPhaseDeriv_hasDerivAt
    have : -m < y := hpole.trans_le hy.1
    linarith
  · intro y hy
    exact (section7FourierPhaseDeriv_hasDerivAt (by
      have : -m < y := hpole.trans_le hy.1
      linarith)).continuousAt.continuousWithinAt
  · intro y hy
    exact (section7FourierPhaseDeriv2_hasDerivAt (by
      have : -m < y := hpole.trans_le hy.1
      linarith)).continuousAt.continuousWithinAt
  · exact hne

/-! ## Elementary facts about the trapezoid -/

theorem section7_trapezoid_eq_zero_of_le
    {L₁ L₂ l : ℝ} (hl : l ≤ L₁ - 1) :
    trapezoid L₁ L₂ l = 0 := by
  unfold trapezoid
  rw [max_eq_left]
  linarith [min_le_left (l - L₁) (min (L₂ - l) 0)]

theorem section7_trapezoid_eq_zero_of_ge
    {L₁ L₂ l : ℝ} (hl : L₂ + 1 ≤ l) :
    trapezoid L₁ L₂ l = 0 := by
  unfold trapezoid
  rw [max_eq_left]
  have hmin : min (l - L₁) (min (L₂ - l) 0) ≤ L₂ - l :=
    (min_le_right _ _).trans (min_le_left _ _)
  linarith

theorem section7_trapezoid_eq_leftRamp
    {L₁ L₂ l : ℝ} (h12 : L₁ < L₂)
    (hl0 : L₁ - 1 ≤ l) (hl1 : l ≤ L₁) :
    trapezoid L₁ L₂ l = l - (L₁ - 1) := by
  unfold trapezoid
  rw [min_eq_right (by linarith : 0 ≤ L₂ - l)]
  rw [min_eq_left (by linarith : l - L₁ ≤ 0)]
  rw [max_eq_right (by linarith : 0 ≤ 1 + (l - L₁))]
  ring

theorem section7_trapezoid_eq_one
    {L₁ L₂ l : ℝ} (hl1 : L₁ ≤ l) (hl2 : l ≤ L₂) :
    trapezoid L₁ L₂ l = 1 := by
  unfold trapezoid
  rw [min_eq_right (by linarith : 0 ≤ L₂ - l)]
  rw [min_eq_right (by linarith : 0 ≤ l - L₁)]
  simp

theorem section7_trapezoid_eq_rightRamp
    {L₁ L₂ l : ℝ} (h12 : L₁ < L₂)
    (hl2 : L₂ ≤ l) (hl3 : l ≤ L₂ + 1) :
    trapezoid L₁ L₂ l = (L₂ + 1) - l := by
  unfold trapezoid
  rw [min_eq_left (by linarith : L₂ - l ≤ 0)]
  rw [min_eq_right (by linarith : L₂ - l ≤ l - L₁)]
  rw [max_eq_right (by linarith : 0 ≤ 1 + (L₂ - l))]
  ring

theorem section7_trapezoid_nonneg (L₁ L₂ l : ℝ) :
    0 ≤ trapezoid L₁ L₂ l := by
  unfold trapezoid
  exact le_max_left _ _

theorem section7_trapezoid_le_one (L₁ L₂ l : ℝ) :
    trapezoid L₁ L₂ l ≤ 1 := by
  unfold trapezoid
  apply max_le zero_le_one
  have hmin : min (l - L₁) (min (L₂ - l) 0) ≤ 0 :=
    (min_le_right _ _).trans (min_le_right _ _)
  linarith

theorem section7_continuous_trapezoid (L₁ L₂ : ℝ) :
    Continuous (trapezoid L₁ L₂) := by
  unfold trapezoid
  fun_prop

/-- A nonzero trapezoid value lies strictly inside its padded support. -/
theorem section7_trapezoid_ne_zero_support
    {L₁ L₂ l : ℝ} (homega : trapezoid L₁ L₂ l ≠ 0) :
    L₁ - 1 < l ∧ l < L₂ + 1 := by
  constructor
  · by_contra h
    exact homega (section7_trapezoid_eq_zero_of_le (le_of_not_gt h))
  · by_contra h
    exact homega (section7_trapezoid_eq_zero_of_ge (le_of_not_gt h))

/-! ## Pole separation on the integral support -/

/-- Because `m` and `L₁` are integral, strict pole separation leaves at
least one full unit between the pole and the left endpoint of the support. -/
theorem section7_one_le_pole_distance
    {m : ℕ} {L₁ : ℤ} (hpole : -(m : ℝ) < (L₁ : ℝ) - 1) :
    1 ≤ (m : ℝ) + (L₁ : ℝ) - 1 := by
  have hpoleZ : -(m : ℤ) < L₁ - 1 := by
    exact_mod_cast hpole
  have hZ : (1 : ℤ) ≤ (m : ℤ) + L₁ - 1 := by omega
  exact_mod_cast hZ

/-- Every point where the trapezoid is nonzero is more than one unit to the
right of the pole.  Thus all reciprocal derivatives above are legitimate on
the effective support of `trapezoidIntegral`. -/
theorem section7_one_lt_denominator_of_trapezoid_ne_zero
    {m : ℕ} {L₁ L₂ : ℤ} {l : ℝ}
    (hpole : -(m : ℝ) < (L₁ : ℝ) - 1)
    (homega : trapezoid L₁ L₂ l ≠ 0) :
    1 < (m : ℝ) + l := by
  have hleft := (section7_trapezoid_ne_zero_support homega).1
  have hunit := section7_one_le_pole_distance hpole
  linarith

/-! ## Exact localization to the three affine pieces -/

/-- The whole-line Fourier integral is exactly the sum of the left unit ramp,
the unweighted middle interval, and the right unit ramp.  The pole hypothesis
keeps the reciprocal presentation continuous on the complete padded support;
`hm` and `hmv` identify it with the original polynomial presentation
`rPhase`. -/
theorem section7_trapezoidIntegral_eq_three_intervals
    {x h m v c : ℝ} {L₁ L₂ : ℤ} {k : ℤ}
    (hm : m ≠ 0) (hmv : m + v ≠ 0) (h12 : L₁ < L₂)
    (hpole : -m < (L₁ : ℝ) - 1) :
    trapezoidIntegral x h m v L₁ L₂ c k =
      (∫ l in (L₁ : ℝ) - 1..(L₁ : ℝ),
        ((l - ((L₁ : ℝ) - 1) : ℝ) : ℂ) *
          e (section7FourierPhase x h m v c (k : ℝ) l)) +
      (∫ l in (L₁ : ℝ)..(L₂ : ℝ),
        e (section7FourierPhase x h m v c (k : ℝ) l)) +
      ∫ l in (L₂ : ℝ)..(L₂ : ℝ) + 1,
        ((((L₂ : ℝ) + 1) - l : ℝ) : ℂ) *
          e (section7FourierPhase x h m v c (k : ℝ) l) := by
  have h12R : (L₁ : ℝ) < (L₂ : ℝ) := by exact_mod_cast h12
  have h01R : (L₁ : ℝ) - 1 ≤ (L₁ : ℝ) := by linarith
  have h23R : (L₂ : ℝ) ≤ (L₂ : ℝ) + 1 := by linarith
  let integrand : ℝ → ℂ := fun l =>
    (trapezoid (L₁ : ℝ) (L₂ : ℝ) l : ℂ) *
      e (section7FourierPhase x h m v c (k : ℝ) l)
  have hphase : trapezoidIntegral x h m v L₁ L₂ c k = ∫ l : ℝ, integrand l := by
    unfold trapezoidIntegral
    apply MeasureTheory.integral_congr_ae
    filter_upwards [] with l
    by_cases homega : trapezoid (L₁ : ℝ) (L₂ : ℝ) l = 0
    · simp [integrand, homega]
    · have hleft := (section7_trapezoid_ne_zero_support homega).1
      have hml : m + l ≠ 0 := by
        have : -m < l := hpole.trans hleft
        linarith
      simp only [integrand]
      rw [rPhase_add_linear_eq_section7FourierPhase hm hmv hml]
  have hsupp : Function.support integrand ⊆
      Ioc ((L₁ : ℝ) - 1) ((L₂ : ℝ) + 1) := by
    intro l hl
    have homega : trapezoid (L₁ : ℝ) (L₂ : ℝ) l ≠ 0 := by
      intro hz
      apply hl
      simp [integrand, hz]
    obtain ⟨hlower, hupper⟩ := section7_trapezoid_ne_zero_support homega
    exact ⟨hlower, hupper.le⟩
  have hphaseCont : ContinuousOn
      (section7FourierPhase x h m v c (k : ℝ))
      (Icc ((L₁ : ℝ) - 1) ((L₂ : ℝ) + 1)) :=
    (section7FourierPhase_contDiffOn_three x h m v c (k : ℝ)).continuousOn.mono
      (fun l hl => by exact hpole.trans_le hl.1)
  have heCont : ContinuousOn
      (fun l => e (section7FourierPhase x h m v c (k : ℝ) l))
      (Icc ((L₁ : ℝ) - 1) ((L₂ : ℝ) + 1)) := by
    unfold e
    exact Complex.continuous_exp.comp_continuousOn
      (continuousOn_const.mul
        (Complex.continuous_ofReal.comp_continuousOn hphaseCont))
  have hint : ContinuousOn integrand
      (Icc ((L₁ : ℝ) - 1) ((L₂ : ℝ) + 1)) := by
    exact ((Complex.continuous_ofReal.comp
      (section7_continuous_trapezoid (L₁ : ℝ) (L₂ : ℝ))).continuousOn.mul heCont)
  have hint01 : IntervalIntegrable integrand volume ((L₁ : ℝ) - 1) (L₁ : ℝ) :=
    ContinuousOn.intervalIntegrable_of_Icc h01R (hint.mono (by
      intro l hl
      exact ⟨hl.1, hl.2.trans (h12R.le.trans h23R)⟩))
  have hint02 : IntervalIntegrable integrand volume ((L₁ : ℝ) - 1) (L₂ : ℝ) :=
    ContinuousOn.intervalIntegrable_of_Icc (h01R.trans h12R.le) (hint.mono (by
      intro l hl
      exact ⟨hl.1, hl.2.trans h23R⟩))
  have hint12 : IntervalIntegrable integrand volume (L₁ : ℝ) (L₂ : ℝ) :=
    ContinuousOn.intervalIntegrable_of_Icc h12R.le (hint.mono (by
      intro l hl
      exact ⟨h01R.trans hl.1, hl.2.trans h23R⟩))
  have hint23 : IntervalIntegrable integrand volume (L₂ : ℝ) ((L₂ : ℝ) + 1) :=
    ContinuousOn.intervalIntegrable_of_Icc h23R (hint.mono (by
      intro l hl
      exact ⟨h01R.trans (h12R.le.trans hl.1), hl.2⟩))
  have heq₀ :
      (∫ l in (L₁ : ℝ) - 1..(L₁ : ℝ), integrand l) =
        ∫ l in (L₁ : ℝ) - 1..(L₁ : ℝ),
          ((l - ((L₁ : ℝ) - 1) : ℝ) : ℂ) *
            e (section7FourierPhase x h m v c (k : ℝ) l) := by
    apply integral_congr
    intro l hl
    have hl' : l ∈ Icc ((L₁ : ℝ) - 1) (L₁ : ℝ) := by
      simpa [uIcc_of_le h01R] using hl
    simp only [integrand]
    rw [section7_trapezoid_eq_leftRamp h12R hl'.1 hl'.2]
  have heq₁ :
      (∫ l in (L₁ : ℝ)..(L₂ : ℝ), integrand l) =
        ∫ l in (L₁ : ℝ)..(L₂ : ℝ),
          e (section7FourierPhase x h m v c (k : ℝ) l) := by
    apply integral_congr
    intro l hl
    have hl' : l ∈ Icc (L₁ : ℝ) (L₂ : ℝ) := by
      simpa [uIcc_of_le h12R.le] using hl
    simp only [integrand]
    rw [section7_trapezoid_eq_one hl'.1 hl'.2]
    simp
  have heq₂ :
      (∫ l in (L₂ : ℝ)..(L₂ : ℝ) + 1, integrand l) =
        ∫ l in (L₂ : ℝ)..(L₂ : ℝ) + 1,
          ((((L₂ : ℝ) + 1) - l : ℝ) : ℂ) *
            e (section7FourierPhase x h m v c (k : ℝ) l) := by
    apply integral_congr
    intro l hl
    have hl' : l ∈ Icc (L₂ : ℝ) ((L₂ : ℝ) + 1) := by
      simpa [uIcc_of_le h23R] using hl
    simp only [integrand]
    rw [section7_trapezoid_eq_rightRamp h12R hl'.1 hl'.2]
  rw [hphase]
  calc
    (∫ l : ℝ, integrand l) =
        ∫ l in (L₁ : ℝ) - 1..(L₂ : ℝ) + 1, integrand l :=
      (integral_eq_integral_of_support_subset hsupp).symm
    _ = (∫ l in (L₁ : ℝ) - 1..(L₂ : ℝ), integrand l) +
        ∫ l in (L₂ : ℝ)..(L₂ : ℝ) + 1, integrand l :=
      (integral_add_adjacent_intervals hint02 hint23).symm
    _ = ((∫ l in (L₁ : ℝ) - 1..(L₁ : ℝ), integrand l) +
        ∫ l in (L₁ : ℝ)..(L₂ : ℝ), integrand l) +
        ∫ l in (L₂ : ℝ)..(L₂ : ℝ) + 1, integrand l := by
      rw [integral_add_adjacent_intervals hint01 hint12]
    _ = _ := by rw [heq₀, heq₁, heq₂]

/-- The two unit ramps contribute at most `1` each.  Thus the complete
trapezoid integral is bounded by `2` plus the norm of its unweighted middle
interval. -/
theorem section7_trapezoidIntegral_norm_le_two_add_middle
    {x h m v c : ℝ} {L₁ L₂ : ℤ} {k : ℤ}
    (hm : m ≠ 0) (hmv : m + v ≠ 0) (h12 : L₁ < L₂)
    (hpole : -m < (L₁ : ℝ) - 1) :
    ‖trapezoidIntegral x h m v L₁ L₂ c k‖ ≤
      2 + ‖∫ l in (L₁ : ℝ)..(L₂ : ℝ),
        e (section7FourierPhase x h m v c (k : ℝ) l)‖ := by
  have h01R : (L₁ : ℝ) - 1 ≤ (L₁ : ℝ) := by linarith
  have h23R : (L₂ : ℝ) ≤ (L₂ : ℝ) + 1 := by linarith
  have hleft :
      ‖∫ l in (L₁ : ℝ) - 1..(L₁ : ℝ),
        ((l - ((L₁ : ℝ) - 1) : ℝ) : ℂ) *
          e (section7FourierPhase x h m v c (k : ℝ) l)‖ ≤ 1 := by
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (L₁ : ℝ) - 1) (b := (L₁ : ℝ)) (C := 1)
      (f := fun l => ((l - ((L₁ : ℝ) - 1) : ℝ) : ℂ) *
        e (section7FourierPhase x h m v c (k : ℝ) l)) (fun l hl => by
          rw [uIoc_of_le h01R] at hl
          have hl' : l ∈ Icc ((L₁ : ℝ) - 1) (L₁ : ℝ) := by
            exact ⟨hl.1.le, hl.2⟩
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_e, mul_one,
            abs_of_nonneg (by linarith [hl'.1])]
          linarith [hl'.2])
    calc
      _ ≤ |(L₁ : ℝ) - ((L₁ : ℝ) - 1)| := by simpa only [one_mul] using hbound
      _ = 1 := by norm_num
  have hright :
      ‖∫ l in (L₂ : ℝ)..(L₂ : ℝ) + 1,
        ((((L₂ : ℝ) + 1) - l : ℝ) : ℂ) *
          e (section7FourierPhase x h m v c (k : ℝ) l)‖ ≤ 1 := by
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (L₂ : ℝ)) (b := (L₂ : ℝ) + 1) (C := 1)
      (f := fun l => ((((L₂ : ℝ) + 1) - l : ℝ) : ℂ) *
        e (section7FourierPhase x h m v c (k : ℝ) l)) (fun l hl => by
          rw [uIoc_of_le h23R] at hl
          have hl' : l ∈ Icc (L₂ : ℝ) ((L₂ : ℝ) + 1) := by
            exact ⟨hl.1.le, hl.2⟩
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_e, mul_one,
            abs_of_nonneg (by linarith [hl'.2])]
          linarith [hl'.1])
    simpa only [one_mul, add_sub_cancel_left, abs_one] using hbound
  rw [section7_trapezoidIntegral_eq_three_intervals hm hmv h12 hpole]
  calc
    ‖(∫ l in (L₁ : ℝ) - 1..(L₁ : ℝ),
          ((l - ((L₁ : ℝ) - 1) : ℝ) : ℂ) *
            e (section7FourierPhase x h m v c (k : ℝ) l)) +
        (∫ l in (L₁ : ℝ)..(L₂ : ℝ),
          e (section7FourierPhase x h m v c (k : ℝ) l)) +
        (∫ l in (L₂ : ℝ)..(L₂ : ℝ) + 1,
          ((((L₂ : ℝ) + 1) - l : ℝ) : ℂ) *
            e (section7FourierPhase x h m v c (k : ℝ) l))‖
        ≤ ‖∫ l in (L₁ : ℝ) - 1..(L₁ : ℝ),
            ((l - ((L₁ : ℝ) - 1) : ℝ) : ℂ) *
              e (section7FourierPhase x h m v c (k : ℝ) l)‖ +
          ‖∫ l in (L₁ : ℝ)..(L₂ : ℝ),
            e (section7FourierPhase x h m v c (k : ℝ) l)‖ +
          ‖∫ l in (L₂ : ℝ)..(L₂ : ℝ) + 1,
            ((((L₂ : ℝ) + 1) - l : ℝ) : ℂ) *
              e (section7FourierPhase x h m v c (k : ℝ) l)‖ := by
        calc
          _ ≤ ‖(∫ l in (L₁ : ℝ) - 1..(L₁ : ℝ),
                ((l - ((L₁ : ℝ) - 1) : ℝ) : ℂ) *
                  e (section7FourierPhase x h m v c (k : ℝ) l)) +
              (∫ l in (L₁ : ℝ)..(L₂ : ℝ),
                e (section7FourierPhase x h m v c (k : ℝ) l))‖ +
              ‖∫ l in (L₂ : ℝ)..(L₂ : ℝ) + 1,
                ((((L₂ : ℝ) + 1) - l : ℝ) : ℂ) *
                  e (section7FourierPhase x h m v c (k : ℝ) l)‖ :=
            norm_add_le _ _
          _ ≤ _ := add_le_add (norm_add_le _ _) le_rfl
    _ ≤ 1 + ‖∫ l in (L₁ : ℝ)..(L₂ : ℝ),
          e (section7FourierPhase x h m v c (k : ℝ) l)‖ + 1 := by
      exact add_le_add (add_le_add hleft le_rfl) hright
    _ = 2 + ‖∫ l in (L₁ : ℝ)..(L₂ : ℝ),
          e (section7FourierPhase x h m v c (k : ℝ) l)‖ := by ring

end IwaniecMozzochiEq73Eq74

end LeanProofs.IntegerPoints
