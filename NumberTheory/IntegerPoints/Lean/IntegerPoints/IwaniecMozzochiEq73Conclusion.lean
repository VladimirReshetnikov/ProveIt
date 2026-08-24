import IntegerPoints.IwaniecMozzochiEq74Conclusion
import IntegerPoints.IwaniecMozzochiRanges

/-!
# Iwaniec--Mozzochi (7.3): the high-frequency conclusion

This file proves the nonstationary estimate that the paper records as (7.3).
The essential point is that the endpoint terms from the first integration by
parts cancel across the left ramp, constant middle, and right ramp of the
trapezoid.  A second integration by parts then gives the quadratic decay.

All constants below are deliberately generous and absolute.  The argument
uses only the hypotheses in the catalogue statement: in particular, no
nonstationary-phase premise is added to the final result.
-/

open Real Set intervalIntegral MeasureTheory

namespace LeanProofs.IntegerPoints

open IwaniecMozzochiEq73Eq74 IwaniecMozzochiEq74Conclusion IMReductionEq75

noncomputable section

namespace IwaniecMozzochiEq73Conclusion

/-! ## A reusable weighted integration-by-parts identity -/

/-- The coefficient produced by one integration by parts when a real
amplitude `u` has constant derivative `du` and the phase derivative is `g`. -/
noncomputable def firstPartsCoeff
    (u : ℝ → ℝ) (du : ℝ) (g g' : ℝ → ℝ) (y : ℝ) : ℝ :=
  du / g y - u y * g' y / (g y) ^ 2

/-- The derivative of `firstPartsCoeff`.  This formula is used for the second
integration by parts. -/
noncomputable def firstPartsCoeffDeriv
    (u : ℝ → ℝ) (du : ℝ) (g g' g'' : ℝ → ℝ) (y : ℝ) : ℝ :=
  -(2 * du * g' y) / (g y) ^ 2 - u y * g'' y / (g y) ^ 2 +
    2 * u y * (g' y) ^ 2 / (g y) ^ 3

/-- Weighted integration by parts, local to a compact interval on which the
phase derivative does not vanish. -/
theorem weighted_phase_parts_on
    {u u' phi g g' : ℝ → ℝ} {p q : ℝ} (hpq : p ≤ q)
    (hu : ∀ y ∈ Icc p q, HasDerivAt u (u' y) y)
    (hu'c : ContinuousOn u' (Icc p q))
    (hphi : ∀ y ∈ Icc p q, HasDerivAt phi (g y) y)
    (hg : ∀ y ∈ Icc p q, HasDerivAt g (g' y) y)
    (hg'c : ContinuousOn g' (Icc p q))
    (hne : ∀ y ∈ Icc p q, g y ≠ 0) :
    ∫ y in p..q, ((u y : ℝ) : ℂ) * e (phi y) =
      e (phi q) * ((u q / g q : ℝ) : ℂ) / (2 * π * Complex.I) -
        e (phi p) * ((u p / g p : ℝ) : ℂ) / (2 * π * Complex.I) -
        (1 / (2 * π * Complex.I)) *
          ∫ y in p..q, e (phi y) *
            ((u' y / g y - u y * g' y / (g y) ^ 2 : ℝ) : ℂ) := by
  have hI : (2 * π * Complex.I : ℂ) ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  have hIcc : uIcc p q = Icc p q := uIcc_of_le hpq
  have hgc : ContinuousOn g (Icc p q) := by
    intro y hy
    exact (hg y hy).continuousAt.continuousWithinAt
  have huc : ContinuousOn u (Icc p q) := by
    intro y hy
    exact (hu y hy).continuousAt.continuousWithinAt
  have hw : ∀ y ∈ uIcc p q,
      HasDerivAt (fun z => ((u z / g z : ℝ) : ℂ) / (2 * π * Complex.I))
        (((u' y / g y - u y * g' y / (g y) ^ 2 : ℝ) : ℂ) /
          (2 * π * Complex.I)) y := by
    intro y hy
    rw [hIcc] at hy
    have hquot := (hu y hy).div (hg y hy) (hne y hy)
    have hquot' : HasDerivAt (fun z => u z / g z)
        (u' y / g y - u y * g' y / (g y) ^ 2) y := by
      convert! hquot using 1 <;> field_simp [hne y hy] <;> ring
    exact hquot'.ofReal_comp.div_const (2 * π * Complex.I)
  have hv : ∀ y ∈ uIcc p q,
      HasDerivAt (fun z => e (phi z))
        (2 * π * Complex.I * g y * e (phi y)) y := by
    intro y hy
    rw [hIcc] at hy
    exact PS.hasDerivAt_e_comp (hphi y hy)
  have hcoeffc : ContinuousOn
      (fun y => ((u' y / g y - u y * g' y / (g y) ^ 2 : ℝ) : ℂ) /
        (2 * π * Complex.I)) (uIcc p q) := by
    rw [hIcc]
    apply ContinuousOn.div_const
    apply Complex.continuous_ofReal.comp_continuousOn
    apply ContinuousOn.sub
    · exact hu'c.div hgc (fun y hy => hne y hy)
    · apply ContinuousOn.div (huc.mul hg'c) (hgc.pow 2)
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
  have hvc : ContinuousOn
      (fun y => 2 * π * Complex.I * g y * e (phi y)) (uIcc p q) := by
    rw [hIcc]
    exact (continuousOn_const.mul
      (Complex.continuous_ofReal.comp_continuousOn hgc)).mul hec
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hw hv
    hcoeffc.intervalIntegrable hvc.intervalIntegrable
  have hleft : ∫ y in p..q,
      ((u y / g y : ℝ) : ℂ) / (2 * π * Complex.I) *
        (2 * π * Complex.I * g y * e (phi y)) =
      ∫ y in p..q, ((u y : ℝ) : ℂ) * e (phi y) := by
    apply integral_congr
    intro y hy
    rw [hIcc] at hy
    have hgy : (g y : ℂ) ≠ 0 := by exact_mod_cast hne y hy
    push_cast
    field_simp
  have hright : ∫ y in p..q,
      (((u' y / g y - u y * g' y / (g y) ^ 2 : ℝ) : ℂ) /
        (2 * π * Complex.I)) * e (phi y) =
      (1 / (2 * π * Complex.I)) *
        ∫ y in p..q, e (phi y) *
          ((u' y / g y - u y * g' y / (g y) ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    apply integral_congr
    intro y _
    simp only [one_div]
    ring
  rw [hleft, hright] at hparts
  rw [hparts]
  ring

/-- Differentiation of the first integration-by-parts coefficient for an
affine amplitude. -/
theorem firstPartsCoeff_hasDerivAt
    {u : ℝ → ℝ} {du : ℝ} {g g' g'' : ℝ → ℝ} {y : ℝ}
    (hu : HasDerivAt u du y) (hg : HasDerivAt g (g' y) y)
    (hg' : HasDerivAt g' (g'' y) y) (hne : g y ≠ 0) :
    HasDerivAt (firstPartsCoeff u du g g')
      (firstPartsCoeffDeriv u du g g' g'' y) y := by
  have hfirst := (hasDerivAt_const y du).div hg hne
  have hsecond := (hu.mul hg').div (hg.pow 2) (pow_ne_zero 2 hne)
  unfold firstPartsCoeff firstPartsCoeffDeriv
  convert! hfirst.sub hsecond using 1 <;>
    simp only [Pi.pow_apply, Pi.mul_apply] <;>
    field_simp [hne] <;> ring

/-- The harmless factor `(2*pi*i)^{-1}` has norm at most one. -/
theorem norm_inv_two_pi_I_le_one :
    ‖(1 / (2 * π * Complex.I) : ℂ)‖ ≤ 1 := by
  rw [norm_div, norm_one, PS.norm_two_pi_I]
  apply (div_le_iff₀ Real.two_pi_pos).2
  nlinarith [Real.two_le_pi]

/-- A convenient norm consequence of `weighted_phase_parts_on`. -/
theorem norm_weighted_phase_integral_le
    {u u' phi g g' : ℝ → ℝ} {p q D B : ℝ} (hpq : p ≤ q)
    (hD : 0 < D) (hB : 0 ≤ B)
    (hu : ∀ y ∈ Icc p q, HasDerivAt u (u' y) y)
    (hu'c : ContinuousOn u' (Icc p q))
    (hphi : ∀ y ∈ Icc p q, HasDerivAt phi (g y) y)
    (hg : ∀ y ∈ Icc p q, HasDerivAt g (g' y) y)
    (hg'c : ContinuousOn g' (Icc p q))
    (hlower : ∀ y ∈ Icc p q, D ≤ |g y|)
    (hcoeff : ∀ y ∈ Icc p q,
      |u' y / g y - u y * g' y / (g y) ^ 2| ≤ B) :
    ‖∫ y in p..q, ((u y : ℝ) : ℂ) * e (phi y)‖ ≤
      |u q| / D + |u p| / D + B * (q - p) := by
  have hne : ∀ y ∈ Icc p q, g y ≠ 0 := by
    intro y hy
    exact abs_pos.mp (hD.trans_le (hlower y hy))
  rw [weighted_phase_parts_on hpq hu hu'c hphi hg hg'c hne]
  have hq : |u q / g q| ≤ |u q| / D := by
    rw [abs_div]
    exact div_le_div₀ (abs_nonneg _) le_rfl hD
      (hlower q ⟨hpq, le_rfl⟩)
  have hp : |u p / g p| ≤ |u p| / D := by
    rw [abs_div]
    exact div_le_div₀ (abs_nonneg _) le_rfl hD
      (hlower p ⟨le_rfl, hpq⟩)
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := p) (b := q) (C := B)
    (f := fun y => e (phi y) *
      ((u' y / g y - u y * g' y / (g y) ^ 2 : ℝ) : ℂ)) (fun y hy => by
        rw [uIoc_of_le hpq] at hy
        rw [norm_mul, norm_e, one_mul, Complex.norm_real, Real.norm_eq_abs]
        exact hcoeff y ⟨hy.1.le, hy.2⟩)
  have hinv := norm_inv_two_pi_I_le_one
  have htau : 1 ≤ ‖(2 * π * Complex.I : ℂ)‖ := by
    rw [PS.norm_two_pi_I]
    nlinarith [Real.two_le_pi]
  have hqterm :
      ‖e (phi q) * ((u q / g q : ℝ) : ℂ) / (2 * π * Complex.I)‖ ≤
        |u q| / D := by
    rw [norm_div, norm_mul, norm_e, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) htau).trans
      (by simpa using hq)
  have hpterm :
      ‖e (phi p) * ((u p / g p : ℝ) : ℂ) / (2 * π * Complex.I)‖ ≤
        |u p| / D := by
    rw [norm_div, norm_mul, norm_e, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact (div_le_div_of_nonneg_left (abs_nonneg _) (by norm_num) htau).trans
      (by simpa using hp)
  have hInt : ‖(1 / (2 * π * Complex.I) : ℂ)‖ *
      ‖∫ y in p..q, e (phi y) *
        ((u' y / g y - u y * g' y / (g y) ^ 2 : ℝ) : ℂ)‖ ≤
      B * |q - p| := by
    exact (mul_le_mul hinv hint (norm_nonneg _) zero_le_one).trans (by simp)
  have hInt' : ‖(1 / (2 * π * Complex.I) : ℂ) *
      (∫ y in p..q, e (phi y) *
        ((u' y / g y - u y * g' y / (g y) ^ 2 : ℝ) : ℂ))‖ ≤
      B * |q - p| := by
    rw [norm_mul]
    exact hInt
  calc
    ‖e (phi q) * ((u q / g q : ℝ) : ℂ) / (2 * π * Complex.I) -
          e (phi p) * ((u p / g p : ℝ) : ℂ) / (2 * π * Complex.I) -
          (1 / (2 * π * Complex.I)) *
            ∫ y in p..q, e (phi y) *
              ((u' y / g y - u y * g' y / (g y) ^ 2 : ℝ) : ℂ)‖
        ≤ ‖e (phi q) * ((u q / g q : ℝ) : ℂ) / (2 * π * Complex.I)‖ +
          ‖e (phi p) * ((u p / g p : ℝ) : ℂ) / (2 * π * Complex.I)‖ +
          ‖(1 / (2 * π * Complex.I)) *
            ∫ y in p..q, e (phi y) *
              ((u' y / g y - u y * g' y / (g y) ^ 2 : ℝ) : ℂ)‖ := by
      calc
        _ ≤ ‖e (phi q) * ((u q / g q : ℝ) : ℂ) / (2 * π * Complex.I) -
              e (phi p) * ((u p / g p : ℝ) : ℂ) / (2 * π * Complex.I)‖ +
            ‖(1 / (2 * π * Complex.I)) *
              ∫ y in p..q, e (phi y) *
                ((u' y / g y - u y * g' y / (g y) ^ 2 : ℝ) : ℂ)‖ :=
          norm_sub_le _ _
        _ ≤ (‖e (phi q) * ((u q / g q : ℝ) : ℂ) / (2 * π * Complex.I)‖ +
              ‖e (phi p) * ((u p / g p : ℝ) : ℂ) / (2 * π * Complex.I)‖) +
            ‖(1 / (2 * π * Complex.I)) *
              ∫ y in p..q, e (phi y) *
                ((u' y / g y - u y * g' y / (g y) ^ 2 : ℝ) : ℂ)‖ :=
          add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ |u q| / D + |u p| / D + B * |q - p| :=
      add_le_add (add_le_add hqterm hpterm) hInt'
    _ = |u q| / D + |u p| / D + B * (q - p) := by
      rw [abs_of_nonneg (sub_nonneg.mpr hpq)]

/-! ## Elementary coefficient bounds -/

theorem firstPartsCoeff_abs_le
    {u : ℝ → ℝ} {du : ℝ} {g g' : ℝ → ℝ} {y D U V E : ℝ}
    (hD : 0 < D) (hU : 0 ≤ U) (hV : 0 ≤ V) (hE : 0 ≤ E)
    (hu : |u y| ≤ U) (hdu : |du| ≤ V)
    (hg : D ≤ |g y|) (hg' : |g' y| ≤ E) :
    |firstPartsCoeff u du g g' y| ≤ V / D + U * E / D ^ 2 := by
  have hgpos : 0 < |g y| := hD.trans_le hg
  have hden : D ^ 2 ≤ |g y| ^ 2 := pow_le_pow_left₀ hD.le hg 2
  have hnum : |u y| * |g' y| ≤ U * E :=
    mul_le_mul hu hg' (abs_nonneg _) hU
  unfold firstPartsCoeff
  calc
    |du / g y - u y * g' y / g y ^ 2| ≤
        |du / g y| + |u y * g' y / g y ^ 2| := abs_sub _ _
    _ = |du| / |g y| + (|u y| * |g' y|) / |g y| ^ 2 := by
      rw [abs_div, abs_div, abs_mul, abs_pow]
    _ ≤ V / D + U * E / D ^ 2 := by
      exact add_le_add
        (div_le_div₀ hV hdu hD hg)
        (div_le_div₀ (mul_nonneg hU hE) hnum (pow_pos hD 2) hden)

/-- Bound for the coefficient produced by the second integration by parts.
The constants are intentionally rounded upward. -/
theorem secondPartsCoeff_abs_le
    {u : ℝ → ℝ} {du : ℝ} {g g' g'' : ℝ → ℝ} {y D E F : ℝ}
    (hD : 0 < D) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hu : |u y| ≤ 1) (hdu : |du| ≤ 1)
    (hg : D ≤ |g y|) (hg' : |g' y| ≤ E) (hg'' : |g'' y| ≤ F) :
    |firstPartsCoeffDeriv u du g g' g'' y / g y -
        firstPartsCoeff u du g g' y * g' y / (g y) ^ 2| ≤
      3 * E / D ^ 3 + F / D ^ 3 + 3 * E ^ 2 / D ^ 4 := by
  have hgpos : 0 < |g y| := hD.trans_le hg
  have hA := firstPartsCoeff_abs_le hD (by norm_num) (by norm_num) hE
    hu hdu hg hg'
  have hden2 : D ^ 2 ≤ |g y| ^ 2 := pow_le_pow_left₀ hD.le hg 2
  have hden3 : D ^ 3 ≤ |g y| ^ 3 := pow_le_pow_left₀ hD.le hg 3
  have hden4 : D ^ 4 ≤ |g y| ^ 4 := pow_le_pow_left₀ hD.le hg 4
  have ht1 : |2 * du * g' y / (g y) ^ 2 / g y| ≤ 2 * E / D ^ 3 := by
    rw [abs_div, abs_div, abs_mul, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_pow]
    have hprod : |du| * |g' y| ≤ 1 * E :=
      mul_le_mul hdu hg' (abs_nonneg _) zero_le_one
    have hn : 2 * |du| * |g' y| ≤ 2 * E := by nlinarith
    have : |g y| ^ 2 * |g y| = |g y| ^ 3 := by ring
    rw [div_div, this]
    exact div_le_div₀ (by positivity) hn (pow_pos hD 3) hden3
  have ht2 : |u y * g'' y / (g y) ^ 2 / g y| ≤ F / D ^ 3 := by
    rw [abs_div, abs_div, abs_mul, abs_pow]
    have hn : |u y| * |g'' y| ≤ F := by
      simpa using mul_le_mul hu hg'' (abs_nonneg _) zero_le_one
    have : |g y| ^ 2 * |g y| = |g y| ^ 3 := by ring
    rw [div_div, this]
    exact div_le_div₀ hF hn (pow_pos hD 3) hden3
  have ht3 : |2 * u y * (g' y) ^ 2 / (g y) ^ 3 / g y| ≤
      2 * E ^ 2 / D ^ 4 := by
    rw [abs_div, abs_div, abs_mul, abs_mul,
      abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_pow, abs_pow]
    have hn : 2 * |u y| * |g' y| ^ 2 ≤ 2 * E ^ 2 := by
      have hsquare := pow_le_pow_left₀ (abs_nonneg (g' y)) hg' 2
      have hprod : |u y| * |g' y| ^ 2 ≤ 1 * E ^ 2 :=
        mul_le_mul hu hsquare (sq_nonneg _) zero_le_one
      nlinarith
    have : |g y| ^ 3 * |g y| = |g y| ^ 4 := by ring
    rw [div_div, this]
    exact div_le_div₀ (by positivity) hn (pow_pos hD 4) hden4
  unfold firstPartsCoeffDeriv
  have hNtri :
      |-(2 * du * g' y) / g y ^ 2 - u y * g'' y / g y ^ 2 +
          2 * u y * g' y ^ 2 / g y ^ 3| ≤
        |2 * du * g' y / g y ^ 2| +
          |u y * g'' y / g y ^ 2| +
          |2 * u y * g' y ^ 2 / g y ^ 3| := by
    calc
      _ ≤ |-(2 * du * g' y) / g y ^ 2 - u y * g'' y / g y ^ 2| +
          |2 * u y * g' y ^ 2 / g y ^ 3| := abs_add_le _ _
      _ ≤ (|-(2 * du * g' y) / g y ^ 2| +
            |u y * g'' y / g y ^ 2|) +
          |2 * u y * g' y ^ 2 / g y ^ 3| :=
        add_le_add (abs_sub _ _) le_rfl
      _ = _ := by rw [neg_div, abs_neg]
  have htri :
      |(-(2 * du * g' y) / g y ^ 2 - u y * g'' y / g y ^ 2 +
            2 * u y * g' y ^ 2 / g y ^ 3) / g y -
          firstPartsCoeff u du g g' y * g' y / g y ^ 2| ≤
        |2 * du * g' y / g y ^ 2 / g y| +
        |u y * g'' y / g y ^ 2 / g y| +
        |2 * u y * g' y ^ 2 / g y ^ 3 / g y| +
        |firstPartsCoeff u du g g' y * g' y / g y ^ 2| := by
    calc
      _ ≤ |(-(2 * du * g' y) / g y ^ 2 - u y * g'' y / g y ^ 2 +
              2 * u y * g' y ^ 2 / g y ^ 3) / g y| +
            |firstPartsCoeff u du g g' y * g' y / g y ^ 2| := abs_sub _ _
      _ = |-(2 * du * g' y) / g y ^ 2 - u y * g'' y / g y ^ 2 +
              2 * u y * g' y ^ 2 / g y ^ 3| / |g y| +
            |firstPartsCoeff u du g g' y * g' y / g y ^ 2| := by
          rw [abs_div]
      _ ≤ (|2 * du * g' y / g y ^ 2| +
              |u y * g'' y / g y ^ 2| +
              |2 * u y * g' y ^ 2 / g y ^ 3|) / |g y| +
            |firstPartsCoeff u du g g' y * g' y / g y ^ 2| :=
          add_le_add (div_le_div_of_nonneg_right hNtri hgpos.le) le_rfl
      _ = (|2 * du * g' y / g y ^ 2 / g y| +
            |u y * g'' y / g y ^ 2 / g y| +
            |2 * u y * g' y ^ 2 / g y ^ 3 / g y|) +
            |firstPartsCoeff u du g g' y * g' y / g y ^ 2| := by
          simp only [add_div, abs_div]
      _ = _ := by ring
  calc
    |(-(2 * du * g' y) / g y ^ 2 - u y * g'' y / g y ^ 2 +
          2 * u y * g' y ^ 2 / g y ^ 3) / g y -
        firstPartsCoeff u du g g' y * g' y / g y ^ 2| ≤ _ := htri
    _ ≤ 2 * E / D ^ 3 + F / D ^ 3 + 2 * E ^ 2 / D ^ 4 +
        (E / D ^ 3 + E ^ 2 / D ^ 4) := by
      have ht4' : |firstPartsCoeff u du g g' y * g' y / (g y) ^ 2| ≤
          E / D ^ 3 + E ^ 2 / D ^ 4 := by
        rw [abs_div, abs_mul, abs_pow]
        have hA' : |firstPartsCoeff u du g g' y| ≤
            1 / D + E / D ^ 2 := by simpa only [one_mul] using hA
        have hn : |firstPartsCoeff u du g g' y| * |g' y| ≤
            (1 / D + E / D ^ 2) * E :=
          mul_le_mul hA' hg' (abs_nonneg _) (by positivity)
        have hb := div_le_div₀ (by positivity) hn (pow_pos hD 2) hden2
        calc
          _ ≤ (1 / D + E / D ^ 2) * E / D ^ 2 := hb
          _ = E / D ^ 3 + E ^ 2 / D ^ 4 := by
            field_simp [hD.ne'] <;> ring
      exact add_le_add (add_le_add (add_le_add ht1 ht2) ht3) ht4'
    _ = 3 * E / D ^ 3 + F / D ^ 3 + 3 * E ^ 2 / D ^ 4 := by ring

/-! ## Cancellation across an affine trapezoid -/

/-- After one integration by parts, the six endpoint terms cancel exactly
across the three affine pieces of a trapezoid. -/
theorem three_affine_phase_parts_on
    {phi g g' : ℝ → ℝ} {a b c d : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (habOne : b - a = 1) (hcdOne : d - c = 1)
    (hphi : ∀ y ∈ Icc a d, HasDerivAt phi (g y) y)
    (hg : ∀ y ∈ Icc a d, HasDerivAt g (g' y) y)
    (hg'c : ContinuousOn g' (Icc a d))
    (hne : ∀ y ∈ Icc a d, g y ≠ 0) :
    (∫ y in a..b, (((y - a : ℝ) : ℂ) * e (phi y))) +
        (∫ y in b..c, e (phi y)) +
        (∫ y in c..d, (((d - y : ℝ) : ℂ) * e (phi y))) =
      -(1 / (2 * π * Complex.I)) *
        ((∫ y in a..b, e (phi y) *
            ((1 / g y - (y - a) * g' y / (g y) ^ 2 : ℝ) : ℂ)) +
          (∫ y in b..c, e (phi y) *
            ((-(g' y) / (g y) ^ 2 : ℝ) : ℂ)) +
          (∫ y in c..d, e (phi y) *
            ((-1 / g y - (d - y) * g' y / (g y) ^ 2 : ℝ) : ℂ))) := by
  have hsub_ab : Icc a b ⊆ Icc a d := fun y hy =>
    ⟨hy.1, hy.2.trans (hbc.trans hcd)⟩
  have hsub_bc : Icc b c ⊆ Icc a d := fun y hy =>
    ⟨hab.trans hy.1, hy.2.trans hcd⟩
  have hsub_cd : Icc c d ⊆ Icc a d := fun y hy =>
    ⟨hab.trans (hbc.trans hy.1), hy.2⟩
  have hleft := weighted_phase_parts_on (u := fun y : ℝ => y - a)
    (u' := fun _ => 1) hab
    (fun y _ => (hasDerivAt_id y).sub_const a) continuousOn_const
    (fun y hy => hphi y (hsub_ab hy))
    (fun y hy => hg y (hsub_ab hy)) (hg'c.mono hsub_ab)
    (fun y hy => hne y (hsub_ab hy))
  have hmiddle := weighted_phase_parts_on (u := fun _ : ℝ => 1)
    (u' := fun _ => 0) hbc
    (fun y _ => hasDerivAt_const y 1) continuousOn_const
    (fun y hy => hphi y (hsub_bc hy))
    (fun y hy => hg y (hsub_bc hy)) (hg'c.mono hsub_bc)
    (fun y hy => hne y (hsub_bc hy))
  have hmiddle' := hmiddle
  simp only [Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_div,
    zero_sub] at hmiddle'
  have hright := weighted_phase_parts_on (u := fun y : ℝ => d - y)
    (u' := fun _ => -1) hcd
    (fun y _ => (hasDerivAt_id y).const_sub d) continuousOn_const
    (fun y hy => hphi y (hsub_cd hy))
    (fun y hy => hg y (hsub_cd hy)) (hg'c.mono hsub_cd)
    (fun y hy => hne y (hsub_cd hy))
  rw [hleft, hmiddle', hright]
  simp only [sub_self, Complex.ofReal_zero, zero_div, mul_zero, zero_mul,
    Complex.ofReal_one, one_mul, Complex.ofReal_neg, Complex.ofReal_ofNat,
    neg_div]
  rw [habOne, hcdOne]
  push_cast
  ring

/-- First-order decay for the three-piece trapezoid expression. -/
theorem norm_three_affine_integrals_le_once
    {phi g g' : ℝ → ℝ} {a b c d D E : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (habOne : b - a = 1) (hcdOne : d - c = 1)
    (hD : 0 < D) (hE : 0 ≤ E)
    (hphi : ∀ y ∈ Icc a d, HasDerivAt phi (g y) y)
    (hg : ∀ y ∈ Icc a d, HasDerivAt g (g' y) y)
    (hg'c : ContinuousOn g' (Icc a d))
    (hlower : ∀ y ∈ Icc a d, D ≤ |g y|)
    (hupper : ∀ y ∈ Icc a d, |g' y| ≤ E) :
    ‖(∫ y in a..b, (((y - a : ℝ) : ℂ) * e (phi y))) +
        (∫ y in b..c, e (phi y)) +
        (∫ y in c..d, (((d - y : ℝ) : ℂ) * e (phi y)))‖ ≤
      2 / D + E * (d - a) / D ^ 2 := by
  have hne : ∀ y ∈ Icc a d, g y ≠ 0 := by
    intro y hy
    exact abs_pos.mp (hD.trans_le (hlower y hy))
  rw [three_affine_phase_parts_on hab hbc hcd habOne hcdOne hphi hg hg'c hne]
  let J₀ : ℂ := ∫ y in a..b, e (phi y) *
    ((firstPartsCoeff (fun z => z - a) 1 g g' y : ℝ) : ℂ)
  let J₁ : ℂ := ∫ y in b..c, e (phi y) *
    ((firstPartsCoeff (fun _ => 1) 0 g g' y : ℝ) : ℂ)
  let J₂ : ℂ := ∫ y in c..d, e (phi y) *
    ((firstPartsCoeff (fun z => d - z) (-1) g g' y : ℝ) : ℂ)
  have hJ₀ : ‖J₀‖ ≤ 1 / D + E / D ^ 2 := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (C := 1 / D + E / D ^ 2)
      (f := fun y => e (phi y) *
        ((firstPartsCoeff (fun z => z - a) 1 g g' y : ℝ) : ℂ)) (fun y hy => by
          rw [uIoc_of_le hab] at hy
          have hy' : y ∈ Icc a d := ⟨hy.1.le, hy.2.trans (hbc.trans hcd)⟩
          rw [norm_mul, norm_e, one_mul, Complex.norm_real, Real.norm_eq_abs]
          simpa using firstPartsCoeff_abs_le (U := 1) (V := 1) hD
            (by norm_num) (by norm_num) hE (by
              rw [abs_of_nonneg (sub_nonneg.mpr hy.1.le)]
              linarith [hy.2, habOne]) (by norm_num)
            (hlower y hy') (hupper y hy'))
    simpa only [J₀, habOne, abs_one, mul_one] using hb
  have hJ₁ : ‖J₁‖ ≤ E * (c - b) / D ^ 2 := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := b) (b := c) (C := E / D ^ 2)
      (f := fun y => e (phi y) *
        ((firstPartsCoeff (fun _ => 1) 0 g g' y : ℝ) : ℂ)) (fun y hy => by
          rw [uIoc_of_le hbc] at hy
          have hy' : y ∈ Icc a d := ⟨hab.trans hy.1.le, hy.2.trans hcd⟩
          rw [norm_mul, norm_e, one_mul, Complex.norm_real, Real.norm_eq_abs]
          simpa using firstPartsCoeff_abs_le (U := 1) (V := 0) hD
            (by norm_num) (by norm_num) hE
            (by norm_num : |(1 : ℝ)| ≤ 1) (by norm_num : |(0 : ℝ)| ≤ 0)
            (hlower y hy') (hupper y hy'))
    have hcb : 0 ≤ c - b := sub_nonneg.mpr hbc
    have hb' : ‖J₁‖ ≤ (E / D ^ 2) * (c - b) := by
      simpa only [J₁, abs_of_nonneg hcb] using hb
    calc
      ‖J₁‖ ≤ (E / D ^ 2) * (c - b) := hb'
      _ = E * (c - b) / D ^ 2 := by ring
  have hJ₂ : ‖J₂‖ ≤ 1 / D + E / D ^ 2 := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := c) (b := d) (C := 1 / D + E / D ^ 2)
      (f := fun y => e (phi y) *
        ((firstPartsCoeff (fun z => d - z) (-1) g g' y : ℝ) : ℂ)) (fun y hy => by
          rw [uIoc_of_le hcd] at hy
          have hy' : y ∈ Icc a d := ⟨hab.trans (hbc.trans hy.1.le), hy.2⟩
          rw [norm_mul, norm_e, one_mul, Complex.norm_real, Real.norm_eq_abs]
          simpa using firstPartsCoeff_abs_le (U := 1) (V := 1) hD
            (by norm_num) (by norm_num) hE (by
              rw [abs_of_nonneg (sub_nonneg.mpr hy.2)]
              linarith [hy.1, hcdOne]) (by norm_num)
            (hlower y hy') (hupper y hy'))
    simpa only [J₂, hcdOne, abs_one, mul_one] using hb
  have hidentify :
      (∫ y in a..b, e (phi y) *
          ((1 / g y - (y - a) * g' y / (g y) ^ 2 : ℝ) : ℂ)) = J₀ ∧
      (∫ y in b..c, e (phi y) *
          ((-(g' y) / (g y) ^ 2 : ℝ) : ℂ)) = J₁ ∧
      (∫ y in c..d, e (phi y) *
          ((-1 / g y - (d - y) * g' y / (g y) ^ 2 : ℝ) : ℂ)) = J₂ := by
    simp only [J₀, J₁, J₂]
    constructor
    · apply integral_congr
      intro y _
      unfold firstPartsCoeff
      rfl
    constructor
    · apply integral_congr
      intro y _
      unfold firstPartsCoeff
      push_cast
      ring
    · apply integral_congr
      intro y _
      unfold firstPartsCoeff
      push_cast
      ring
  rw [hidentify.1, hidentify.2.1, hidentify.2.2]
  calc
    ‖-(1 / (2 * π * Complex.I)) * (J₀ + J₁ + J₂)‖ ≤
        ‖J₀‖ + ‖J₁‖ + ‖J₂‖ := by
      rw [norm_mul, norm_neg]
      calc
        ‖(1 / (2 * π * Complex.I) : ℂ)‖ * ‖J₀ + J₁ + J₂‖ ≤
            1 * ‖J₀ + J₁ + J₂‖ :=
          mul_le_mul_of_nonneg_right norm_inv_two_pi_I_le_one (norm_nonneg _)
        _ ≤ ‖J₀‖ + ‖J₁‖ + ‖J₂‖ := by
          simpa only [one_mul] using (norm_add_le (J₀ + J₁) J₂).trans
            (add_le_add (norm_add_le J₀ J₁) le_rfl)
    _ ≤ (1 / D + E / D ^ 2) + E * (c - b) / D ^ 2 +
        (1 / D + E / D ^ 2) := add_le_add (add_le_add hJ₀ hJ₁) hJ₂
    _ = 2 / D + E * (d - a) / D ^ 2 := by
      have hwidth : d - a = 2 + (c - b) := by linarith [habOne, hcdOne]
      rw [hwidth]
      field_simp [hD.ne'] <;> ring

/-- Quadratic decay for the same three-piece trapezoid expression. -/
theorem norm_three_affine_integrals_le_twice
    {phi g g' g'' : ℝ → ℝ} {a b c d D E F : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (habOne : b - a = 1) (hcdOne : d - c = 1)
    (hD : 0 < D) (hE : 0 ≤ E) (hF : 0 ≤ F)
    (hphi : ∀ y ∈ Icc a d, HasDerivAt phi (g y) y)
    (hg : ∀ y ∈ Icc a d, HasDerivAt g (g' y) y)
    (hg' : ∀ y ∈ Icc a d, HasDerivAt g' (g'' y) y)
    (hg''c : ContinuousOn g'' (Icc a d))
    (hlower : ∀ y ∈ Icc a d, D ≤ |g y|)
    (hupper : ∀ y ∈ Icc a d, |g' y| ≤ E)
    (hupper' : ∀ y ∈ Icc a d, |g'' y| ≤ F) :
    ‖(∫ y in a..b, (((y - a : ℝ) : ℂ) * e (phi y))) +
        (∫ y in b..c, e (phi y)) +
        (∫ y in c..d, (((d - y : ℝ) : ℂ) * e (phi y)))‖ ≤
      6 / D ^ 2 + 6 * E / D ^ 3 +
        (3 * E / D ^ 3 + F / D ^ 3 + 3 * E ^ 2 / D ^ 4) * (d - a) := by
  have hgc : ContinuousOn g (Icc a d) := by
    intro y hy
    exact (hg y hy).continuousAt.continuousWithinAt
  have hg'c : ContinuousOn g' (Icc a d) := by
    intro y hy
    exact (hg' y hy).continuousAt.continuousWithinAt
  have hne : ∀ y ∈ Icc a d, g y ≠ 0 := by
    intro y hy
    exact abs_pos.mp (hD.trans_le (hlower y hy))
  have hAderivc : ∀ (u : ℝ → ℝ) (du : ℝ), ContinuousOn u (Icc a d) →
      ContinuousOn (firstPartsCoeffDeriv u du g g' g'') (Icc a d) := by
    intro u du huc
    unfold firstPartsCoeffDeriv
    have hg2ne : ∀ y ∈ Icc a d, g y ^ 2 ≠ 0 :=
      fun y hy => pow_ne_zero 2 (hne y hy)
    have hg3ne : ∀ y ∈ Icc a d, g y ^ 3 ≠ 0 :=
      fun y hy => pow_ne_zero 3 (hne y hy)
    have ht1 : ContinuousOn
        (fun y => -(2 * du * g' y) / g y ^ 2) (Icc a d) := by
      have hraw := ((continuousOn_const : ContinuousOn
        (fun _ : ℝ => -(2 * du)) (Icc a d)).mul hg'c).div
          (hgc.pow 2) hg2ne
      refine hraw.congr ?_
      intro y hy
      simp only [Pi.mul_apply, Pi.div_apply, Pi.pow_apply]
      ring
    have ht2 : ContinuousOn
        (fun y => u y * g'' y / g y ^ 2) (Icc a d) := by
      convert! (huc.mul hg''c).div (hgc.pow 2) hg2ne using 1
    have ht3 : ContinuousOn
        (fun y => 2 * u y * g' y ^ 2 / g y ^ 3) (Icc a d) := by
      have hraw := (((continuousOn_const : ContinuousOn
        (fun _ : ℝ => (2 : ℝ)) (Icc a d)).mul huc).mul (hg'c.pow 2)).div
          (hgc.pow 3) hg3ne
      refine hraw.congr ?_
      intro y hy
      simp only [Pi.mul_apply, Pi.div_apply, Pi.pow_apply]
    convert! (ht1.sub ht2).add ht3 using 1
  let B : ℝ := 3 * E / D ^ 3 + F / D ^ 3 + 3 * E ^ 2 / D ^ 4
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hpiece : ∀ (u : ℝ → ℝ) (du p q : ℝ),
      |du| ≤ 1 → Icc p q ⊆ Icc a d → p ≤ q → Continuous u →
      (∀ y ∈ Icc p q, HasDerivAt u du y) →
      (∀ y ∈ Icc p q, |u y| ≤ 1) →
      ‖∫ y in p..q, e (phi y) *
          ((firstPartsCoeff u du g g' y : ℝ) : ℂ)‖ ≤
        2 * (1 / D + E / D ^ 2) / D + B * (q - p) := by
    intro u du p q hduabs hsub hpq hucont huderiv huabs
    have hAderiv : ∀ y ∈ Icc p q,
        HasDerivAt (firstPartsCoeff u du g g')
          (firstPartsCoeffDeriv u du g g' g'' y) y := by
      intro y hy
      exact firstPartsCoeff_hasDerivAt (huderiv y hy) (hg y (hsub hy))
        (hg' y (hsub hy)) (hne y (hsub hy))
    have hcoeff : ∀ y ∈ Icc p q,
        |firstPartsCoeffDeriv u du g g' g'' y / g y -
          firstPartsCoeff u du g g' y * g' y / (g y) ^ 2| ≤ B := by
      intro y hy
      exact secondPartsCoeff_abs_le hD hE hF (huabs y hy) hduabs
        (hlower y (hsub hy)) (hupper y (hsub hy)) (hupper' y (hsub hy))
    have hraw := norm_weighted_phase_integral_le hpq hD hB hAderiv
      ((hAderivc u du hucont.continuousOn).mono hsub)
      (fun y hy => hphi y (hsub hy)) (fun y hy => hg y (hsub hy))
      (hg'c.mono hsub) (fun y hy => hlower y (hsub hy)) hcoeff
    have hpA : |firstPartsCoeff u du g g' p| ≤ 1 / D + E / D ^ 2 := by
      simpa only [one_mul] using firstPartsCoeff_abs_le hD (by norm_num)
        (by norm_num) hE (huabs p ⟨le_rfl, hpq⟩) hduabs
        (hlower p (hsub ⟨le_rfl, hpq⟩)) (hupper p (hsub ⟨le_rfl, hpq⟩))
    have hqA : |firstPartsCoeff u du g g' q| ≤ 1 / D + E / D ^ 2 := by
      simpa only [one_mul] using firstPartsCoeff_abs_le hD (by norm_num)
        (by norm_num) hE (huabs q ⟨hpq, le_rfl⟩) hduabs
        (hlower q (hsub ⟨hpq, le_rfl⟩)) (hupper q (hsub ⟨hpq, le_rfl⟩))
    have heq :
        (∫ y in p..q, e (phi y) *
            ((firstPartsCoeff u du g g' y : ℝ) : ℂ)) =
          ∫ y in p..q, ((firstPartsCoeff u du g g' y : ℝ) : ℂ) *
            e (phi y) := by
      apply integral_congr
      intro y _
      ring
    rw [heq]
    exact hraw.trans <| calc
      |firstPartsCoeff u du g g' q| / D +
            |firstPartsCoeff u du g g' p| / D + B * (q - p) ≤
          (1 / D + E / D ^ 2) / D +
            (1 / D + E / D ^ 2) / D + B * (q - p) := by
        gcongr
      _ = 2 * (1 / D + E / D ^ 2) / D + B * (q - p) := by ring
  have hsub_ab : Icc a b ⊆ Icc a d := fun y hy =>
    ⟨hy.1, hy.2.trans (hbc.trans hcd)⟩
  have hsub_bc : Icc b c ⊆ Icc a d := fun y hy =>
    ⟨hab.trans hy.1, hy.2.trans hcd⟩
  have hsub_cd : Icc c d ⊆ Icc a d := fun y hy =>
    ⟨hab.trans (hbc.trans hy.1), hy.2⟩
  have hJ₀ := hpiece (fun y => y - a) 1 a b (by norm_num) hsub_ab hab
    (continuous_id.sub continuous_const)
    (fun y _ => (hasDerivAt_id y).sub_const a) (fun y hy => by
      rw [abs_of_nonneg (sub_nonneg.mpr hy.1)]
      linarith [hy.2, habOne])
  have hJ₁ := hpiece (fun _ => 1) 0 b c (by norm_num) hsub_bc hbc continuous_const
    (fun y _ => hasDerivAt_const y 1) (fun _ _ => by norm_num)
  have hJ₂ := hpiece (fun y => d - y) (-1) c d (by norm_num) hsub_cd hcd
    (continuous_const.sub continuous_id)
    (fun y _ => (hasDerivAt_id y).const_sub d) (fun y hy => by
      rw [abs_of_nonneg (sub_nonneg.mpr hy.2)]
      linarith [hy.1, hcdOne])
  rw [three_affine_phase_parts_on hab hbc hcd habOne hcdOne hphi hg hg'c hne]
  simp only [firstPartsCoeff, zero_div, zero_sub, one_mul, neg_div] at hJ₀ hJ₁ hJ₂
  have hJ₀' :
      ‖∫ y in a..b, e (phi y) *
          ((1 / g y - (y - a) * g' y / (g y) ^ 2 : ℝ) : ℂ)‖ ≤
        2 * (1 / D + E / D ^ 2) / D + B * (b - a) := by
    simpa only [neg_div] using hJ₀
  have hJ₁' :
      ‖∫ y in b..c, e (phi y) *
          ((-(g' y) / (g y) ^ 2 : ℝ) : ℂ)‖ ≤
        2 * (1 / D + E / D ^ 2) / D + B * (c - b) := by
    simpa only [neg_div] using hJ₁
  have hJ₂' :
      ‖∫ y in c..d, e (phi y) *
          ((-1 / g y - (d - y) * g' y / (g y) ^ 2 : ℝ) : ℂ)‖ ≤
        2 * (1 / D + E / D ^ 2) / D + B * (d - c) := by
    simpa only [neg_div] using hJ₂
  have hsum :
      ‖(∫ y in a..b, e (phi y) *
          ((1 / g y - (y - a) * g' y / (g y) ^ 2 : ℝ) : ℂ)) +
        (∫ y in b..c, e (phi y) *
          ((-(g' y) / (g y) ^ 2 : ℝ) : ℂ)) +
        (∫ y in c..d, e (phi y) *
          ((-1 / g y - (d - y) * g' y / (g y) ^ 2 : ℝ) : ℂ))‖ ≤
      6 * (1 / D + E / D ^ 2) / D + B * (d - a) := by
    calc
      _ ≤ ‖∫ y in a..b, e (phi y) *
              ((1 / g y - (y - a) * g' y / (g y) ^ 2 : ℝ) : ℂ)‖ +
            ‖∫ y in b..c, e (phi y) *
              ((-(g' y) / (g y) ^ 2 : ℝ) : ℂ)‖ +
            ‖∫ y in c..d, e (phi y) *
              ((-1 / g y - (d - y) * g' y / (g y) ^ 2 : ℝ) : ℂ)‖ := by
          exact (norm_add_le _ _).trans
            (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ (2 * (1 / D + E / D ^ 2) / D + B * (b - a)) +
          (2 * (1 / D + E / D ^ 2) / D + B * (c - b)) +
          (2 * (1 / D + E / D ^ 2) / D + B * (d - c)) := by
        exact add_le_add (add_le_add hJ₀' hJ₁') hJ₂'
      _ = 6 * (1 / D + E / D ^ 2) / D + B * (d - a) := by ring
  let S : ℂ :=
    (∫ y in a..b, e (phi y) *
        ((1 / g y - (y - a) * g' y / (g y) ^ 2 : ℝ) : ℂ)) +
      (∫ y in b..c, e (phi y) *
        ((-(g' y) / (g y) ^ 2 : ℝ) : ℂ)) +
      (∫ y in c..d, e (phi y) *
        ((-1 / g y - (d - y) * g' y / (g y) ^ 2 : ℝ) : ℂ))
  have hsumS : ‖S‖ ≤ 6 * (1 / D + E / D ^ 2) / D + B * (d - a) := by
    simpa only [S] using hsum
  change ‖-(1 / (2 * π * Complex.I)) * S‖ ≤ _
  calc
    ‖-(1 / (2 * π * Complex.I)) * S‖ =
        ‖1 / (2 * π * Complex.I)‖ * ‖S‖ := by
      rw [norm_mul, norm_neg]
    _ ≤ 1 * ‖S‖ :=
      mul_le_mul_of_nonneg_right norm_inv_two_pi_I_le_one (norm_nonneg S)
    _ ≤ 6 * (1 / D + E / D ^ 2) / D + B * (d - a) := by
      simpa only [one_mul] using hsumS
    _ = 6 / D ^ 2 + 6 * E / D ^ 3 +
        (3 * E / D ^ 3 + F / D ^ 3 + 3 * E ^ 2 / D ^ 4) * (d - a) := by
      simp only [B]
      field_simp [hD.ne'] <;> ring

/-! ## Main-range scale and padded-support geometry -/

/-- The representative Farey length is at least one in the main range. -/
theorem one_le_fareyLength
    {x H M : ℝ} {a c : ℕ}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c) :
    1 ≤ fareyLength x H M c := by
  rcases hmain with ⟨hx, _hxM, _hMx, hH, hHupper, _hshift₁,
    _hshift₂, hMlower⟩
  rcases hfarey with ⟨hc, hcH, _, _, _⟩
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hc0 : 0 < (c : ℝ) := by exact_mod_cast (zero_lt_one.trans_le hc)
  have hHupper' : H ≤ M * x ^ (-(7 : ℝ) / 22) := by
    convert hHupper using 1
    norm_num [theta0]
  have hMlower' : x ^ ((19 : ℝ) / 44) ≤ M := by
    calc
      x ^ ((19 : ℝ) / 44) = x ^ ((9 : ℝ) / 2 * theta0 - 1) := by
        congr 1
        norm_num [theta0]
      _ ≤ M := hMlower.le
  calc
    1 ≤ x ^ ((3 : ℝ) / 44) := Real.one_le_rpow hx (by norm_num)
    _ ≤ fareyLength x H M c :=
      fareyLength_ge_rpow x H M c hx0 hH0 hc0 hcH hHupper' hMlower'

/-- Once `M` is larger than `256`, the main-range shift inequality improves
the coarse `lambda < M` estimate to `lambda < M/2`. -/
theorem fareyLength_lt_half_of_large_M
    {x H M : ℝ} {a c : ℕ}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c)
    (hMlarge : 256 < M) :
    fareyLength x H M c < M / 2 := by
  rcases hmain with ⟨hx, _hxM, hMsqrt, hH, _hHupper, hshift₁, _, _⟩
  rcases hfarey with ⟨hc, _hcH, _, _, _⟩
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hH0 : 0 < H := zero_lt_one.trans_le hH
  have hM0 : 0 < M := by linarith
  have hcR : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have hc0 : (0 : ℝ) < c := zero_lt_one.trans_le hcR
  have hroot : M < Real.sqrt x := by
    simpa only [Real.sqrt_eq_rpow] using hMsqrt
  have hxlarge : (65536 : ℝ) < x := by
    have hsqrt : 256 < Real.sqrt x := hMlarge.trans hroot
    nlinarith [Real.sq_sqrt hx0.le]
  have htwo : (2 : ℝ) ≤ x ^ ((3 : ℝ) / 22) := by
    have hroot16 : (((2 : ℝ) ^ 16) ^ ((16 : ℝ)⁻¹)) = 2 :=
      Real.pow_rpow_inv_natCast (by norm_num) (by norm_num : (16 : ℕ) ≠ 0)
    calc
      (2 : ℝ) = (((2 : ℝ) ^ 16) ^ ((16 : ℝ)⁻¹)) := hroot16.symm
      _ = (65536 : ℝ) ^ ((16 : ℝ)⁻¹) := by norm_num
      _ ≤ x ^ ((16 : ℝ)⁻¹) :=
        Real.rpow_le_rpow (by norm_num) hxlarge.le (by norm_num)
      _ ≤ x ^ ((3 : ℝ) / 22) :=
        Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have htwoM : 2 * M < x ^ ((7 : ℝ) / 11) := by
    have hprod : 2 * Real.sqrt x ≤
        x ^ ((3 : ℝ) / 22) * Real.sqrt x :=
      mul_le_mul_of_nonneg_right htwo (Real.sqrt_nonneg x)
    calc
      2 * M < 2 * Real.sqrt x := mul_lt_mul_of_pos_left hroot (by norm_num)
      _ ≤ x ^ ((3 : ℝ) / 22) * Real.sqrt x := hprod
      _ = x ^ ((7 : ℝ) / 11) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx0]
        congr 1
        norm_num
  have hshift₁' : M * x ^ (-(4 : ℝ) / 11) < H := by
    convert hshift₁ using 1
    norm_num [theta0]
  have hxpow : x * x ^ (-(4 : ℝ) / 11) = x ^ ((7 : ℝ) / 11) := by
    calc
      x * x ^ (-(4 : ℝ) / 11) = x ^ ((1 : ℝ) + -(4 : ℝ) / 11) := by
        simpa using (Real.rpow_add hx0 (1 : ℝ) (-(4 : ℝ) / 11)).symm
      _ = x ^ ((7 : ℝ) / 11) := by norm_num
  have hMpowH : M * x ^ ((7 : ℝ) / 11) < x * (c : ℝ) * H := by
    have hbase : M * x ^ ((7 : ℝ) / 11) < x * H := by
      calc
        M * x ^ ((7 : ℝ) / 11) = x * (M * x ^ (-(4 : ℝ) / 11)) := by
          rw [← hxpow]
          ring
        _ < x * H := mul_lt_mul_of_pos_left hshift₁' hx0
    calc
      M * x ^ ((7 : ℝ) / 11) < x * H := hbase
      _ ≤ x * (c : ℝ) * H := by
        have : x * H ≤ x * (c : ℝ) * H := by
          calc
            x * H = x * 1 * H := by ring
            _ ≤ x * (c : ℝ) * H := by gcongr
        exact this
  have hden : 2 * M ^ 2 < x * (c : ℝ) * H := by
    calc
      2 * M ^ 2 = M * (2 * M) := by ring
      _ < M * x ^ ((7 : ℝ) / 11) := mul_lt_mul_of_pos_left htwoM hM0
      _ < x * (c : ℝ) * H := hMpowH
  have hden0 : 0 < x * (c : ℝ) * H := by positivity
  unfold fareyLength
  apply (div_lt_iff₀ hden0).2
  have hMhalf : 0 < M / 2 := div_pos hM0 (by norm_num)
  have hmul := mul_lt_mul_of_pos_left hden hMhalf
  calc
    M ^ 3 = (M / 2) * (2 * M ^ 2) := by ring
    _ < (M / 2) * (x * (c : ℝ) * H) := hmul
    _ = M / 2 * (x * (c : ℝ) * H) := rfl

/-- On the complete padded support the denominator is not merely pole-free:
it is at least a fixed fraction of `M`.  Small `M` is handled by integrality;
large `M` uses the preceding half-length estimate. -/
theorem padded_denominator_lower_fraction
    {x H M : ℝ} {a c : ℕ} {L₁ L₂ : ℤ}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c)
    (hpole : -(fareyPoint x a c : ℝ) < (L₁ : ℝ) - 1)
    (hL₁ : -fareyLength x H M c < (L₁ : ℝ))
    {y : ℝ} (hy : y ∈ Icc ((L₁ : ℝ) - 1) ((L₂ : ℝ) + 1)) :
    M / 256 ≤ (fareyPoint x a c : ℝ) + y := by
  have hM0 : 0 < M :=
    (Real.rpow_pos_of_pos (zero_lt_one.trans_le hmain.1) theta0).trans hmain.2.1
  by_cases hlarge : 256 < M
  · have hlam := fareyLength_lt_half_of_large_M hmain hfarey hlarge
    obtain ⟨_hmPos, _hvNonneg, hvLt, hsum, _, _, _⟩ :=
      fareyPoint_geometry hmain hfarey
    have hmLower : M - 1 < (fareyPoint x a c : ℝ) := by
      linarith
    have hyLower : -fareyLength x H M c - 1 < y := by
      linarith [hy.1]
    nlinarith
  · have hMle : M ≤ 256 := le_of_not_gt hlarge
    have hunit := section7_one_le_pole_distance
      (m := fareyPoint x a c) (L₁ := L₁) hpole
    have hone : 1 ≤ (fareyPoint x a c : ℝ) + y := by linarith [hy.1]
    nlinarith

/-- The padded support has length at most `11 lambda`. -/
theorem padded_width_le
    {x H M : ℝ} {a c : ℕ} {L₁ L₂ : ℤ}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c)
    (hL₁ : -fareyLength x H M c < (L₁ : ℝ))
    (hL₂ : (L₂ : ℝ) < 8 * fareyLength x H M c) :
    ((L₂ : ℝ) + 1) - ((L₁ : ℝ) - 1) ≤ 11 * fareyLength x H M c := by
  have hlam := one_le_fareyLength hmain hfarey
  linarith

/-- Every padded-support point is within `10 lambda` of the Farey centre's
fractional part. -/
theorem padded_displacement_le
    {x H M : ℝ} {a c : ℕ} {L₁ L₂ : ℤ}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c)
    (hL₁ : -fareyLength x H M c < (L₁ : ℝ))
    (hL₂ : (L₂ : ℝ) < 8 * fareyLength x H M c)
    {y : ℝ} (hy : y ∈ Icc ((L₁ : ℝ) - 1) ((L₂ : ℝ) + 1)) :
    |y - fareyFrac x a c| ≤ 10 * fareyLength x H M c := by
  have hlam := one_le_fareyLength hmain hfarey
  have hv := (fareyPoint_geometry hmain hfarey).2.1
  have hvlt := (fareyPoint_geometry hmain hfarey).2.2.1
  rw [abs_le]
  constructor <;> linarith [hy.1, hy.2]

/-- The defining scale identity, in the ordering used by the derivative
bounds below. -/
theorem farey_scale_identity
    {x H M : ℝ} {c : ℕ} (hx : 0 < x) (hH : 0 < H) (hc : 0 < (c : ℝ)) :
    (c : ℝ) * x * H * fareyLength x H M c = M ^ 3 := by
  unfold fareyLength
  field_simp [hx.ne', hH.ne', hc.ne'] <;> ring

/-- Cancellation-friendly factorization of the first reciprocal derivative. -/
theorem section7ReciprocalPhaseDeriv_eq_factored
    {x h m v y : ℝ} (hmv : m + v ≠ 0) (hmy : m + y ≠ 0) :
    section7ReciprocalPhaseDeriv x h m v y =
      x * h * (y - v) * (2 * m + y + v) /
        ((m + v) ^ 2 * (m + y) ^ 2) := by
  unfold section7ReciprocalPhaseDeriv
  field_simp [hmv, hmy] <;> ring

/-! ## Uniform derivative bounds on the padded support -/

/-- A scale-normalized first-derivative bound. -/
theorem reciprocal_first_derivative_scale_bound
    {x H M c h m v y lam : ℝ}
    (hx : 0 < x) (hH : 0 < H) (hM : 0 < M) (hc : 0 < c)
    (hlam : 0 < lam) (hh : 0 < h) (hhUpper : h ≤ 4 * H)
    (hsLower : M ≤ m + v) (hsUpper : m + v ≤ 2 * M)
    (hdLower : M / 256 ≤ m + y) (hdUpper : m + y ≤ 11 * M)
    (hdisp : |y - v| ≤ 10 * lam)
    (hscale : c * x * H * lam = M ^ 3) :
    c * |section7ReciprocalPhaseDeriv x h m v y| ≤ 34078720 := by
  have hsPos : 0 < m + v := hM.trans_le hsLower
  have hdPos : 0 < m + y := (div_pos hM (by norm_num)).trans_le hdLower
  have hfactorPos : 0 < 2 * m + y + v := by linarith
  have hfactorUpper : 2 * m + y + v ≤ 13 * M := by linarith
  rw [section7ReciprocalPhaseDeriv_eq_factored hsPos.ne' hdPos.ne', abs_div,
    abs_mul, abs_mul, abs_mul, abs_mul, abs_pow, abs_pow, abs_of_pos hx,
    abs_of_pos hh, abs_of_pos hsPos, abs_of_pos hdPos, abs_of_pos hfactorPos]
  have hnum : x * h * |y - v| * (2 * m + y + v) ≤
      520 * x * H * lam * M := by
    calc
      x * h * |y - v| * (2 * m + y + v) ≤
          x * (4 * H) * (10 * lam) * (13 * M) := by gcongr
      _ = 520 * x * H * lam * M := by ring
  have hden : M ^ 2 * (M / 256) ^ 2 ≤ (m + v) ^ 2 * (m + y) ^ 2 := by
    exact mul_le_mul
      (pow_le_pow_left₀ hM.le hsLower 2)
      (pow_le_pow_left₀ (div_nonneg hM.le (by norm_num)) hdLower 2)
      (sq_nonneg _) (sq_nonneg _)
  have hquot :
      x * h * |y - v| * (2 * m + y + v) /
          ((m + v) ^ 2 * (m + y) ^ 2) ≤
        (520 * x * H * lam * M) / (M ^ 2 * (M / 256) ^ 2) :=
    div_le_div₀ (by positivity) hnum (by positivity) hden
  calc
    c * (x * h * |y - v| * (2 * m + y + v) /
        ((m + v) ^ 2 * (m + y) ^ 2)) ≤
      c * ((520 * x * H * lam * M) / (M ^ 2 * (M / 256) ^ 2)) :=
        mul_le_mul_of_nonneg_left hquot hc.le
    _ = 34078720 := by
      field_simp [hM.ne']
      nlinarith [hscale]

/-- A scale-normalized second-derivative bound. -/
theorem reciprocal_second_derivative_scale_bound
    {x H M c h m v y lam : ℝ}
    (hx : 0 < x) (hH : 0 < H) (hM : 0 < M) (hc : 0 < c)
    (hlam : 0 < lam) (hh : 0 < h) (hhUpper : h ≤ 4 * H)
    (hdLower : M / 256 ≤ m + y)
    (hscale : c * x * H * lam = M ^ 3) :
    c * lam * |section7ReciprocalPhaseDeriv2 x h m v y| ≤ 134217728 := by
  have hdPos : 0 < m + y := (div_pos hM (by norm_num)).trans_le hdLower
  unfold section7ReciprocalPhaseDeriv2
  rw [abs_div, abs_mul, abs_mul, abs_pow,
    abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos hx,
    abs_of_pos hh, abs_of_pos hdPos]
  have hnum : 2 * x * h ≤ 8 * x * H := by
    have hhx := mul_le_mul_of_nonneg_left hhUpper hx.le
    nlinarith
  have hden : (M / 256) ^ 3 ≤ (m + y) ^ 3 :=
    pow_le_pow_left₀ (div_nonneg hM.le (by norm_num)) hdLower 3
  have hquot : (2 * x * h) / (m + y) ^ 3 ≤
      (8 * x * H) / (M / 256) ^ 3 :=
    div_le_div₀ (by positivity) hnum (by positivity) hden
  calc
    c * lam * (2 * x * h / (m + y) ^ 3) ≤
        c * lam * (8 * x * H / (M / 256) ^ 3) :=
      mul_le_mul_of_nonneg_left hquot (mul_nonneg hc.le hlam.le)
    _ = 134217728 := by
      field_simp [hM.ne']
      nlinarith [hscale]

/-- A scale-normalized third-derivative bound. -/
theorem reciprocal_third_derivative_scale_bound
    {x H M c h m v y lam : ℝ}
    (hx : 0 < x) (hH : 0 < H) (hM : 0 < M) (hc : 0 < c)
    (hlam : 0 < lam) (hh : 0 < h) (hhUpper : h ≤ 4 * H)
    (hdLower : M / 256 ≤ m + y)
    (hscale : c * x * H * lam = M ^ 3) :
    c * lam * M * |section7ReciprocalPhaseDeriv3 x h m v y| ≤
      103079215104 := by
  have hdPos : 0 < m + y := (div_pos hM (by norm_num)).trans_le hdLower
  unfold section7ReciprocalPhaseDeriv3
  rw [abs_div, abs_neg, abs_mul, abs_mul, abs_pow,
    abs_of_pos (by norm_num : (0 : ℝ) < 6),
    abs_of_pos hx, abs_of_pos hh, abs_of_pos hdPos]
  have hnum : 6 * x * h ≤ 24 * x * H := by
    have hhx := mul_le_mul_of_nonneg_left hhUpper hx.le
    nlinarith
  have hden : (M / 256) ^ 4 ≤ (m + y) ^ 4 :=
    pow_le_pow_left₀ (div_nonneg hM.le (by norm_num)) hdLower 4
  have hquot : (6 * x * h) / (m + y) ^ 4 ≤
      (24 * x * H) / (M / 256) ^ 4 :=
    div_le_div₀ (by positivity) hnum (by positivity) hden
  calc
    c * lam * M * (6 * x * h / (m + y) ^ 4) ≤
        c * lam * M * (24 * x * H / (M / 256) ^ 4) :=
      mul_le_mul_of_nonneg_left hquot
        (mul_nonneg (mul_nonneg hc.le hlam.le) hM.le)
    _ = 103079215104 := by
      field_simp [hM.ne']
      nlinarith [hscale]

/-- Uniform bound for `c |r'(y)|` on the complete padded support. -/
theorem padded_first_derivative_bound
    {x H M : ℝ} {a c h : ℕ} {L₁ L₂ : ℤ}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c)
    (hhmem : h ∈ intRange H (4 * H))
    (hpole : -(fareyPoint x a c : ℝ) < (L₁ : ℝ) - 1)
    (hL₁ : -fareyLength x H M c < (L₁ : ℝ))
    (hL₂ : (L₂ : ℝ) < 8 * fareyLength x H M c)
    {y : ℝ} (hy : y ∈ Icc ((L₁ : ℝ) - 1) ((L₂ : ℝ) + 1)) :
    (c : ℝ) * |section7ReciprocalPhaseDeriv x h (fareyPoint x a c)
      (fareyFrac x a c) y| ≤ 34078720 := by
  have hx : 0 < x := zero_lt_one.trans_le hmain.1
  have hH : 0 < H := zero_lt_one.trans_le hmain.2.2.2.1
  have hM : 0 < M := (Real.rpow_pos_of_pos hx theta0).trans hmain.2.1
  have hc : 0 < (c : ℝ) := by
    exact_mod_cast (zero_lt_one.trans_le hfarey.1)
  have hlam : 0 < fareyLength x H M c := by
    exact zero_lt_one.trans_le (one_le_fareyLength hmain hfarey)
  have hhBounds := mem_intRange_four_mul hH hhmem
  have hhPos : (0 : ℝ) < h := hH.trans hhBounds.1
  obtain ⟨_hmPos, _hvNonneg, _hvLt, _hsum, _hcoef, hsLower, hsUpper⟩ :=
    fareyPoint_geometry hmain hfarey
  have hdLower := padded_denominator_lower_fraction hmain hfarey hpole hL₁ hy
  have hdUpper := (padded_denominator_bounds hmain hfarey hpole hL₂ hy).2
  exact reciprocal_first_derivative_scale_bound hx hH hM hc hlam hhPos
    hhBounds.2 (by simpa only [_hsum] using hsLower)
    (by simpa only [_hsum] using hsUpper) hdLower hdUpper
    (padded_displacement_le hmain hfarey hL₁ hL₂ hy)
    (farey_scale_identity hx hH hc)

/-- Uniform bound for `c lambda |r''(y)|`. -/
theorem padded_second_derivative_bound
    {x H M : ℝ} {a c h : ℕ} {L₁ L₂ : ℤ}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c)
    (hhmem : h ∈ intRange H (4 * H))
    (hpole : -(fareyPoint x a c : ℝ) < (L₁ : ℝ) - 1)
    (hL₁ : -fareyLength x H M c < (L₁ : ℝ))
    {y : ℝ} (hy : y ∈ Icc ((L₁ : ℝ) - 1) ((L₂ : ℝ) + 1)) :
    (c : ℝ) * fareyLength x H M c *
        |section7ReciprocalPhaseDeriv2 x h (fareyPoint x a c)
          (fareyFrac x a c) y| ≤
      134217728 := by
  have hx : 0 < x := zero_lt_one.trans_le hmain.1
  have hH : 0 < H := zero_lt_one.trans_le hmain.2.2.2.1
  have hM : 0 < M := (Real.rpow_pos_of_pos hx theta0).trans hmain.2.1
  have hc : 0 < (c : ℝ) := by exact_mod_cast
    (zero_lt_one.trans_le hfarey.1)
  have hlam : 0 < fareyLength x H M c := by
    exact zero_lt_one.trans_le (one_le_fareyLength hmain hfarey)
  have hhBounds := mem_intRange_four_mul hH hhmem
  have hhPos : (0 : ℝ) < h := hH.trans hhBounds.1
  exact reciprocal_second_derivative_scale_bound
    (v := fareyFrac x a c) hx hH hM hc hlam hhPos
    hhBounds.2 (padded_denominator_lower_fraction hmain hfarey hpole hL₁ hy)
    (farey_scale_identity hx hH hc)

/-- Uniform bound for `c lambda M |r'''(y)|`. -/
theorem padded_third_derivative_bound
    {x H M : ℝ} {a c h : ℕ} {L₁ L₂ : ℤ}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c)
    (hhmem : h ∈ intRange H (4 * H))
    (hpole : -(fareyPoint x a c : ℝ) < (L₁ : ℝ) - 1)
    (hL₁ : -fareyLength x H M c < (L₁ : ℝ))
    {y : ℝ} (hy : y ∈ Icc ((L₁ : ℝ) - 1) ((L₂ : ℝ) + 1)) :
    (c : ℝ) * fareyLength x H M c * M *
        |section7ReciprocalPhaseDeriv3 x h (fareyPoint x a c)
          (fareyFrac x a c) y| ≤
      103079215104 := by
  have hx : 0 < x := zero_lt_one.trans_le hmain.1
  have hH : 0 < H := zero_lt_one.trans_le hmain.2.2.2.1
  have hM : 0 < M := (Real.rpow_pos_of_pos hx theta0).trans hmain.2.1
  have hc : 0 < (c : ℝ) := by exact_mod_cast
    (zero_lt_one.trans_le hfarey.1)
  have hlam : 0 < fareyLength x H M c := by
    exact zero_lt_one.trans_le (one_le_fareyLength hmain hfarey)
  have hhBounds := mem_intRange_four_mul hH hhmem
  have hhPos : (0 : ℝ) < h := hH.trans hhBounds.1
  exact reciprocal_third_derivative_scale_bound
    (v := fareyFrac x a c) hx hH hM hc hlam hhPos
    hhBounds.2 (padded_denominator_lower_fraction hmain hfarey hpole hL₁ hy)
    (farey_scale_identity hx hH hc)

/-- For frequencies beyond twice the absolute first-derivative constant, the
linear Fourier term dominates throughout the padded support. -/
theorem padded_phase_derivative_lower
    {x H M : ℝ} {a c h : ℕ} {L₁ L₂ : ℤ} {k : ℤ}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c)
    (hhmem : h ∈ intRange H (4 * H))
    (hpole : -(fareyPoint x a c : ℝ) < (L₁ : ℝ) - 1)
    (hL₁ : -fareyLength x H M c < (L₁ : ℝ))
    (hL₂ : (L₂ : ℝ) < 8 * fareyLength x H M c)
    (hk : (68157440 : ℝ) ≤ |(k : ℝ)|)
    {y : ℝ} (hy : y ∈ Icc ((L₁ : ℝ) - 1) ((L₂ : ℝ) + 1)) :
    |(k : ℝ)| / (2 * (c : ℝ)) ≤
      |section7FourierPhaseDeriv x h (fareyPoint x a c)
        (fareyFrac x a c) c (k : ℝ) y| := by
  have hc : (0 : ℝ) < c := by exact_mod_cast
    (zero_lt_one.trans_le hfarey.1)
  have hr := padded_first_derivative_bound hmain hfarey hhmem hpole hL₁ hL₂ hy
  have hrDiv :
      |section7ReciprocalPhaseDeriv x h (fareyPoint x a c)
        (fareyFrac x a c) y| ≤ 34078720 / (c : ℝ) := by
    apply (le_div_iff₀ hc).2
    nlinarith
  have hstep : |(k : ℝ)| / (2 * (c : ℝ)) ≤
      |(k : ℝ)| / (c : ℝ) - 34078720 / (c : ℝ) := by
    field_simp [hc.ne']
    nlinarith
  have htri : |(k : ℝ) / (c : ℝ)| -
      |section7ReciprocalPhaseDeriv x h (fareyPoint x a c)
        (fareyFrac x a c) y| ≤
      |section7ReciprocalPhaseDeriv x h (fareyPoint x a c)
          (fareyFrac x a c) y + (k : ℝ) / (c : ℝ)| := by
    simpa only [add_comm] using
      (abs_sub_abs_le_abs_add ((k : ℝ) / (c : ℝ))
        (section7ReciprocalPhaseDeriv x h (fareyPoint x a c)
          (fareyFrac x a c) y))
  unfold section7FourierPhaseDeriv
  calc
    |(k : ℝ)| / (2 * (c : ℝ)) ≤
        |(k : ℝ)| / (c : ℝ) - 34078720 / (c : ℝ) := hstep
    _ ≤ |(k : ℝ)| / (c : ℝ) -
        |section7ReciprocalPhaseDeriv x h (fareyPoint x a c)
          (fareyFrac x a c) y| := sub_le_sub_left hrDiv _
    _ = |(k : ℝ) / (c : ℝ)| -
        |section7ReciprocalPhaseDeriv x h (fareyPoint x a c)
          (fareyFrac x a c) y| := by rw [abs_div, abs_of_pos hc]
    _ ≤ _ := htri

/-- Pointwise second-derivative upper bound in the normalization used by the
abstract integration-by-parts estimate. -/
theorem padded_phase_second_upper
    {x H M : ℝ} {a c h : ℕ} {L₁ L₂ : ℤ}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c)
    (hhmem : h ∈ intRange H (4 * H))
    (hpole : -(fareyPoint x a c : ℝ) < (L₁ : ℝ) - 1)
    (hL₁ : -fareyLength x H M c < (L₁ : ℝ))
    {y : ℝ} (hy : y ∈ Icc ((L₁ : ℝ) - 1) ((L₂ : ℝ) + 1)) :
    |section7ReciprocalPhaseDeriv2 x h (fareyPoint x a c)
      (fareyFrac x a c) y| ≤
      134217728 / ((c : ℝ) * fareyLength x H M c) := by
  have hc : (0 : ℝ) < c := by exact_mod_cast
    (zero_lt_one.trans_le hfarey.1)
  have hlam : 0 < fareyLength x H M c :=
    zero_lt_one.trans_le (one_le_fareyLength hmain hfarey)
  apply (le_div_iff₀ (mul_pos hc hlam)).2
  have := padded_second_derivative_bound hmain hfarey hhmem hpole hL₁ hy
  nlinarith

/-- Pointwise third-derivative upper bound in the normalization used by the
second integration by parts. -/
theorem padded_phase_third_upper
    {x H M : ℝ} {a c h : ℕ} {L₁ L₂ : ℤ}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c)
    (hhmem : h ∈ intRange H (4 * H))
    (hpole : -(fareyPoint x a c : ℝ) < (L₁ : ℝ) - 1)
    (hL₁ : -fareyLength x H M c < (L₁ : ℝ))
    {y : ℝ} (hy : y ∈ Icc ((L₁ : ℝ) - 1) ((L₂ : ℝ) + 1)) :
    |section7ReciprocalPhaseDeriv3 x h (fareyPoint x a c)
      (fareyFrac x a c) y| ≤
      103079215104 /
        ((c : ℝ) * fareyLength x H M c * M) := by
  have hc : (0 : ℝ) < c := by exact_mod_cast
    (zero_lt_one.trans_le hfarey.1)
  have hlam : 0 < fareyLength x H M c :=
    zero_lt_one.trans_le (one_le_fareyLength hmain hfarey)
  have hM : 0 < M :=
    (Real.rpow_pos_of_pos (zero_lt_one.trans_le hmain.1) theta0).trans hmain.2.1
  apply (le_div_iff₀ (mul_pos (mul_pos hc hlam) hM)).2
  have := padded_third_derivative_bound hmain hfarey hhmem hpole hL₁ hy
  nlinarith

/-! ## Pure scale arithmetic for the two decay rates -/

theorem once_scale_le
    {K c lam W Q : ℝ} (hK : 1 ≤ K) (hc : 0 < c) (hlam : 1 ≤ lam)
    (hW : 0 ≤ W) (hWupper : W ≤ 11 * lam) (hQ : 0 ≤ Q) :
    2 / (K / (2 * c)) + (Q / (c * lam)) * W / (K / (2 * c)) ^ 2 ≤
      (4 + 44 * Q) * c / K := by
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hlam0 : 0 < lam := zero_lt_one.trans_le hlam
  have heq :
      2 / (K / (2 * c)) + (Q / (c * lam)) * W / (K / (2 * c)) ^ 2 =
        4 * c / K + 4 * Q * c * W / (lam * K ^ 2) := by
    field_simp [hK0.ne', hc.ne', hlam0.ne']
    ring
  rw [heq]
  have hsecond : 4 * Q * c * W / (lam * K ^ 2) ≤ 44 * Q * c / K := by
    calc
      4 * Q * c * W / (lam * K ^ 2) ≤
          4 * Q * c * (11 * lam) / (lam * K ^ 2) := by gcongr
      _ = 44 * Q * c / K ^ 2 := by
        field_simp [hlam0.ne']
        ring
      _ ≤ 44 * Q * c / K := by
        apply div_le_div_of_nonneg_left (by positivity) hK0
        nlinarith [sq_nonneg (K - 1)]
  calc
    4 * c / K + 4 * Q * c * W / (lam * K ^ 2) ≤
        4 * c / K + 44 * Q * c / K := add_le_add le_rfl hsecond
    _ = (4 + 44 * Q) * c / K := by ring

theorem twice_scale_le
    {K c lam M W Q R : ℝ}
    (hK : 1 ≤ K) (hc : 0 < c) (hlam : 1 ≤ lam) (hM : 1 ≤ M)
    (hW : 0 ≤ W) (hWupper : W ≤ 11 * lam)
    (hQ : 0 ≤ Q) (hR : 0 ≤ R) :
    6 / (K / (2 * c)) ^ 2 +
        6 * (Q / (c * lam)) / (K / (2 * c)) ^ 3 +
        (3 * (Q / (c * lam)) / (K / (2 * c)) ^ 3 +
          (R / (c * lam * M)) / (K / (2 * c)) ^ 3 +
          3 * (Q / (c * lam)) ^ 2 / (K / (2 * c)) ^ 4) * W ≤
      (24 + 312 * Q + 88 * R + 528 * Q ^ 2) * c ^ 2 / K ^ 2 := by
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hlam0 : 0 < lam := zero_lt_one.trans_le hlam
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  have heq :
      6 / (K / (2 * c)) ^ 2 +
          6 * (Q / (c * lam)) / (K / (2 * c)) ^ 3 +
          (3 * (Q / (c * lam)) / (K / (2 * c)) ^ 3 +
            (R / (c * lam * M)) / (K / (2 * c)) ^ 3 +
            3 * (Q / (c * lam)) ^ 2 / (K / (2 * c)) ^ 4) * W =
        24 * c ^ 2 / K ^ 2 +
          48 * Q * c ^ 2 / (lam * K ^ 3) +
          24 * Q * c ^ 2 * W / (lam * K ^ 3) +
          8 * R * c ^ 2 * W / (lam * M * K ^ 3) +
          48 * Q ^ 2 * c ^ 2 * W / (lam ^ 2 * K ^ 4) := by
    field_simp [hK0.ne', hc.ne', hlam0.ne', hM0.ne']
    ring
  rw [heq]
  have hK2 : K ^ 2 ≤ K ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg K) (sub_nonneg.mpr hK)]
  have hKsq : 1 ≤ K ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hK) (by linarith : 0 ≤ K + 1)]
  have hK24 : K ^ 2 ≤ K ^ 4 := by
    nlinarith [mul_nonneg (sq_nonneg K) (sub_nonneg.mpr hKsq)]
  have ht1 : 48 * Q * c ^ 2 / (lam * K ^ 3) ≤
      48 * Q * c ^ 2 / K ^ 2 := by
    apply div_le_div_of_nonneg_left (by positivity) (pow_pos hK0 2)
    have : K ^ 2 ≤ lam * K ^ 3 := by
      calc K ^ 2 ≤ K ^ 3 := hK2
           _ ≤ lam * K ^ 3 := by
             simpa only [one_mul] using
               mul_le_mul_of_nonneg_right hlam (pow_nonneg hK0.le 3)
    exact this
  have ht2 : 24 * Q * c ^ 2 * W / (lam * K ^ 3) ≤
      264 * Q * c ^ 2 / K ^ 2 := by
    calc
      24 * Q * c ^ 2 * W / (lam * K ^ 3) ≤
          24 * Q * c ^ 2 * (11 * lam) / (lam * K ^ 3) := by gcongr
      _ = 264 * Q * c ^ 2 / K ^ 3 := by
        field_simp [hlam0.ne']
        ring
      _ ≤ 264 * Q * c ^ 2 / K ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (pow_pos hK0 2) hK2
  have ht3 : 8 * R * c ^ 2 * W / (lam * M * K ^ 3) ≤
      88 * R * c ^ 2 / K ^ 2 := by
    calc
      8 * R * c ^ 2 * W / (lam * M * K ^ 3) ≤
          8 * R * c ^ 2 * (11 * lam) / (lam * M * K ^ 3) := by gcongr
      _ = 88 * R * c ^ 2 / (M * K ^ 3) := by
        field_simp [hlam0.ne']
        ring
      _ ≤ 88 * R * c ^ 2 / K ^ 2 := by
        apply div_le_div_of_nonneg_left (by positivity) (pow_pos hK0 2)
        calc K ^ 2 ≤ K ^ 3 := hK2
             _ ≤ M * K ^ 3 := by
               simpa only [one_mul] using
                 mul_le_mul_of_nonneg_right hM (pow_nonneg hK0.le 3)
  have ht4 : 48 * Q ^ 2 * c ^ 2 * W / (lam ^ 2 * K ^ 4) ≤
      528 * Q ^ 2 * c ^ 2 / K ^ 2 := by
    calc
      48 * Q ^ 2 * c ^ 2 * W / (lam ^ 2 * K ^ 4) ≤
          48 * Q ^ 2 * c ^ 2 * (11 * lam) / (lam ^ 2 * K ^ 4) := by gcongr
      _ = 528 * Q ^ 2 * c ^ 2 / (lam * K ^ 4) := by
        field_simp [hlam0.ne']
        ring
      _ ≤ 528 * Q ^ 2 * c ^ 2 / K ^ 2 := by
        apply div_le_div_of_nonneg_left (by positivity) (pow_pos hK0 2)
        calc K ^ 2 ≤ K ^ 4 := hK24
             _ ≤ lam * K ^ 4 := by
               simpa only [one_mul] using
                 mul_le_mul_of_nonneg_right hlam (pow_nonneg hK0.le 4)
  calc
    24 * c ^ 2 / K ^ 2 + 48 * Q * c ^ 2 / (lam * K ^ 3) +
          24 * Q * c ^ 2 * W / (lam * K ^ 3) +
          8 * R * c ^ 2 * W / (lam * M * K ^ 3) +
          48 * Q ^ 2 * c ^ 2 * W / (lam ^ 2 * K ^ 4) ≤
        24 * c ^ 2 / K ^ 2 + 48 * Q * c ^ 2 / K ^ 2 +
          264 * Q * c ^ 2 / K ^ 2 + 88 * R * c ^ 2 / K ^ 2 +
          528 * Q ^ 2 * c ^ 2 / K ^ 2 := by
      exact add_le_add
        (add_le_add (add_le_add (add_le_add le_rfl ht1) ht2) ht3) ht4
    _ = (24 + 312 * Q + 88 * R + 528 * Q ^ 2) * c ^ 2 / K ^ 2 := by ring

/-! ## Equation (7.3) and the combined catalogue theorem -/

/-- **Iwaniec--Mozzochi (7.3).**  The high-frequency trapezoid integral has
both the first- and second-order nonstationary decay, hence their minimum. -/
theorem iwaniecMozzochi_eq73_holds :
    ∃ k₀ C : ℝ, 0 < k₀ ∧ 0 < C ∧
      ∀ (x H M : ℝ) (a c h : ℕ) (L₁ L₂ : ℤ),
        InMainRange x H M → InFareySet x H M a c →
        h ∈ intRange H (4 * H) → L₁ < L₂ →
        -(fareyPoint x a c : ℝ) < (L₁ : ℝ) - 1 →
        -fareyLength x H M c < L₁ →
        (L₂ : ℝ) < 8 * fareyLength x H M c →
        ∀ k : ℤ, k₀ ≤ |(k : ℝ)| →
          ‖trapezoidIntegral x h (fareyPoint x a c) (fareyFrac x a c)
            L₁ L₂ c k‖ ≤
            C * min (c / |(k : ℝ)|) ((c : ℝ) ^ 2 / (k : ℝ) ^ 2) := by
  let Q : ℝ := 134217728
  let R : ℝ := 103079215104
  let C₁ : ℝ := 4 + 44 * Q
  let C₂ : ℝ := 24 + 312 * Q + 88 * R + 528 * Q ^ 2
  let C : ℝ := max C₁ C₂
  have hC₁pos : 0 < C₁ := by dsimp only [C₁, Q]; positivity
  have hC₂pos : 0 < C₂ := by dsimp only [C₂, Q, R]; positivity
  have hCpos : 0 < C := hC₁pos.trans_le (le_max_left C₁ C₂)
  refine ⟨68157440, C, by norm_num, hCpos, ?_⟩
  intro x H M a c h L₁ L₂ hmain hfarey hhmem h12 hpole hL₁ hL₂ k hk
  have hx : 0 < x := zero_lt_one.trans_le hmain.1
  have hH : 0 < H := zero_lt_one.trans_le hmain.2.2.2.1
  have hM : 0 < M := (Real.rpow_pos_of_pos hx theta0).trans hmain.2.1
  have hMone : 1 ≤ M := by
    exact (Real.one_le_rpow hmain.1 (by norm_num [theta0])).trans hmain.2.1.le
  have hc : (0 : ℝ) < c := by exact_mod_cast
    (zero_lt_one.trans_le hfarey.1)
  have hlamOne : 1 ≤ fareyLength x H M c := one_le_fareyLength hmain hfarey
  have hlam : 0 < fareyLength x H M c := zero_lt_one.trans_le hlamOne
  have hK : 1 ≤ |(k : ℝ)| := by nlinarith
  have hK0 : 0 < |(k : ℝ)| := zero_lt_one.trans_le hK
  have hab : (L₁ : ℝ) - 1 ≤ (L₁ : ℝ) := by linarith
  have hbc : (L₁ : ℝ) ≤ (L₂ : ℝ) := by exact_mod_cast h12.le
  have hcd : (L₂ : ℝ) ≤ (L₂ : ℝ) + 1 := by linarith
  have hwidth0 : 0 ≤ ((L₂ : ℝ) + 1) - ((L₁ : ℝ) - 1) := by linarith
  have hwidth := padded_width_le hmain hfarey hL₁ hL₂
  obtain ⟨hmPos, _hvNonneg, _hvLt, _hsum, _hcoef, hsLower, _hsUpper⟩ :=
    fareyPoint_geometry hmain hfarey
  have hm : (fareyPoint x a c : ℝ) ≠ 0 := by exact_mod_cast hmPos.ne'
  have hmv : (fareyPoint x a c : ℝ) + fareyFrac x a c ≠ 0 := by
    rw [_hsum]
    exact (hM.trans_le hsLower).ne'
  have hpadded : ∀ y ∈
      Icc ((L₁ : ℝ) - 1) ((L₂ : ℝ) + 1),
      0 < (fareyPoint x a c : ℝ) + y := by
    intro y hy
    exact (div_pos hM (by norm_num)).trans_le
      (padded_denominator_lower_fraction hmain hfarey hpole hL₁ hy)
  have hphi : ∀ y ∈ Icc ((L₁ : ℝ) - 1) ((L₂ : ℝ) + 1),
      HasDerivAt
        (section7FourierPhase x h (fareyPoint x a c)
          (fareyFrac x a c) c (k : ℝ))
        (section7FourierPhaseDeriv x h (fareyPoint x a c)
          (fareyFrac x a c) c (k : ℝ) y) y := by
    intro y hy
    exact section7FourierPhase_hasDerivAt (hpadded y hy).ne'
  have hg : ∀ y ∈ Icc ((L₁ : ℝ) - 1) ((L₂ : ℝ) + 1),
      HasDerivAt
        (section7FourierPhaseDeriv x h (fareyPoint x a c)
          (fareyFrac x a c) c (k : ℝ))
        (section7ReciprocalPhaseDeriv2 x h (fareyPoint x a c)
          (fareyFrac x a c) y) y := by
    intro y hy
    exact section7FourierPhaseDeriv_hasDerivAt (hpadded y hy).ne'
  have hg' : ∀ y ∈ Icc ((L₁ : ℝ) - 1) ((L₂ : ℝ) + 1),
      HasDerivAt
        (section7ReciprocalPhaseDeriv2 x h (fareyPoint x a c)
          (fareyFrac x a c))
        (section7ReciprocalPhaseDeriv3 x h (fareyPoint x a c)
          (fareyFrac x a c) y) y := by
    intro y hy
    exact section7FourierPhaseDeriv2_hasDerivAt (hpadded y hy).ne'
  have hg''c : ContinuousOn
      (section7ReciprocalPhaseDeriv3 x h (fareyPoint x a c)
        (fareyFrac x a c))
      (Icc ((L₁ : ℝ) - 1) ((L₂ : ℝ) + 1)) := by
    unfold section7ReciprocalPhaseDeriv3
    apply ContinuousOn.div continuousOn_const
      ((continuousOn_const.add continuousOn_id).pow 4)
    intro y hy
    exact pow_ne_zero 4 (hpadded y hy).ne'
  have hlower : ∀ y ∈ Icc ((L₁ : ℝ) - 1) ((L₂ : ℝ) + 1),
      |(k : ℝ)| / (2 * (c : ℝ)) ≤
        |section7FourierPhaseDeriv x h (fareyPoint x a c)
          (fareyFrac x a c) c (k : ℝ) y| := by
    intro y hy
    exact padded_phase_derivative_lower hmain hfarey hhmem hpole hL₁ hL₂ hk hy
  have hupper : ∀ y ∈ Icc ((L₁ : ℝ) - 1) ((L₂ : ℝ) + 1),
      |section7ReciprocalPhaseDeriv2 x h (fareyPoint x a c)
        (fareyFrac x a c) y| ≤
        Q / ((c : ℝ) * fareyLength x H M c) := by
    intro y hy
    simpa only [Q] using padded_phase_second_upper hmain hfarey hhmem hpole hL₁ hy
  have hupper' : ∀ y ∈ Icc ((L₁ : ℝ) - 1) ((L₂ : ℝ) + 1),
      |section7ReciprocalPhaseDeriv3 x h (fareyPoint x a c)
        (fareyFrac x a c) y| ≤
        R / ((c : ℝ) * fareyLength x H M c * M) := by
    intro y hy
    simpa only [R] using padded_phase_third_upper hmain hfarey hhmem hpole hL₁ hy
  have hOnce := norm_three_affine_integrals_le_once
    (phi := section7FourierPhase x h (fareyPoint x a c)
      (fareyFrac x a c) c (k : ℝ))
    (g := section7FourierPhaseDeriv x h (fareyPoint x a c)
      (fareyFrac x a c) c (k : ℝ))
    (g' := section7ReciprocalPhaseDeriv2 x h (fareyPoint x a c)
      (fareyFrac x a c))
    (a := (L₁ : ℝ) - 1) (b := (L₁ : ℝ))
    (c := (L₂ : ℝ)) (d := (L₂ : ℝ) + 1)
    (D := |(k : ℝ)| / (2 * (c : ℝ)))
    (E := Q / ((c : ℝ) * fareyLength x H M c))
    hab hbc hcd (by ring) (by ring)
    (div_pos hK0 (mul_pos (by norm_num) hc)) (by positivity)
    hphi hg (by
      intro y hy
      exact (hg' y hy).continuousAt.continuousWithinAt) hlower hupper
  have hTwice := norm_three_affine_integrals_le_twice
    (phi := section7FourierPhase x h (fareyPoint x a c)
      (fareyFrac x a c) c (k : ℝ))
    (g := section7FourierPhaseDeriv x h (fareyPoint x a c)
      (fareyFrac x a c) c (k : ℝ))
    (g' := section7ReciprocalPhaseDeriv2 x h (fareyPoint x a c)
      (fareyFrac x a c))
    (g'' := section7ReciprocalPhaseDeriv3 x h (fareyPoint x a c)
      (fareyFrac x a c))
    (a := (L₁ : ℝ) - 1) (b := (L₁ : ℝ))
    (c := (L₂ : ℝ)) (d := (L₂ : ℝ) + 1)
    (D := |(k : ℝ)| / (2 * (c : ℝ)))
    (E := Q / ((c : ℝ) * fareyLength x H M c))
    (F := R / ((c : ℝ) * fareyLength x H M c * M))
    hab hbc hcd (by ring) (by ring)
    (div_pos hK0 (mul_pos (by norm_num) hc)) (by positivity) (by positivity)
    hphi hg hg' hg''c hlower hupper hupper'
  have hOnceScale := once_scale_le (K := |(k : ℝ)|) (c := (c : ℝ))
    (lam := fareyLength x H M c)
    (W := ((L₂ : ℝ) + 1) - ((L₁ : ℝ) - 1)) (Q := Q)
    hK hc hlamOne hwidth0 hwidth (by positivity)
  have hTwiceScale := twice_scale_le (K := |(k : ℝ)|) (c := (c : ℝ))
    (lam := fareyLength x H M c) (M := M)
    (W := ((L₂ : ℝ) + 1) - ((L₁ : ℝ) - 1)) (Q := Q) (R := R)
    hK hc hlamOne hMone hwidth0 hwidth (by positivity) (by positivity)
  rw [section7_trapezoidIntegral_eq_three_intervals hm hmv h12 hpole]
  have hFirst :
      ‖(∫ y in (L₁ : ℝ) - 1..(L₁ : ℝ),
          (((y - ((L₁ : ℝ) - 1) : ℝ) : ℂ) *
            e (section7FourierPhase x h (fareyPoint x a c)
              (fareyFrac x a c) c (k : ℝ) y))) +
        (∫ y in (L₁ : ℝ)..(L₂ : ℝ),
          e (section7FourierPhase x h (fareyPoint x a c)
            (fareyFrac x a c) c (k : ℝ) y)) +
        (∫ y in (L₂ : ℝ)..(L₂ : ℝ) + 1,
          (((((L₂ : ℝ) + 1) - y : ℝ) : ℂ) *
            e (section7FourierPhase x h (fareyPoint x a c)
              (fareyFrac x a c) c (k : ℝ) y)))‖ ≤
        C₁ * (c : ℝ) / |(k : ℝ)| :=
    hOnce.trans (by simpa only [C₁] using hOnceScale)
  have hSecond :
      ‖(∫ y in (L₁ : ℝ) - 1..(L₁ : ℝ),
          (((y - ((L₁ : ℝ) - 1) : ℝ) : ℂ) *
            e (section7FourierPhase x h (fareyPoint x a c)
              (fareyFrac x a c) c (k : ℝ) y))) +
        (∫ y in (L₁ : ℝ)..(L₂ : ℝ),
          e (section7FourierPhase x h (fareyPoint x a c)
            (fareyFrac x a c) c (k : ℝ) y)) +
        (∫ y in (L₂ : ℝ)..(L₂ : ℝ) + 1,
          (((((L₂ : ℝ) + 1) - y : ℝ) : ℂ) *
            e (section7FourierPhase x h (fareyPoint x a c)
              (fareyFrac x a c) c (k : ℝ) y)))‖ ≤
        C₂ * (c : ℝ) ^ 2 / (k : ℝ) ^ 2 := by
    have habskSq : |(k : ℝ)| ^ 2 = (k : ℝ) ^ 2 := sq_abs (k : ℝ)
    rw [← habskSq]
    exact hTwice.trans (by simpa only [C₂] using hTwiceScale)
  have hC₁ : C₁ ≤ C := le_max_left C₁ C₂
  have hC₂ : C₂ ≤ C := le_max_right C₁ C₂
  have hFirstC :
      ‖(∫ y in (L₁ : ℝ) - 1..(L₁ : ℝ),
          (((y - ((L₁ : ℝ) - 1) : ℝ) : ℂ) *
            e (section7FourierPhase x h (fareyPoint x a c)
              (fareyFrac x a c) c (k : ℝ) y))) +
        (∫ y in (L₁ : ℝ)..(L₂ : ℝ),
          e (section7FourierPhase x h (fareyPoint x a c)
            (fareyFrac x a c) c (k : ℝ) y)) +
        (∫ y in (L₂ : ℝ)..(L₂ : ℝ) + 1,
          (((((L₂ : ℝ) + 1) - y : ℝ) : ℂ) *
            e (section7FourierPhase x h (fareyPoint x a c)
              (fareyFrac x a c) c (k : ℝ) y)))‖ ≤
        C * ((c : ℝ) / |(k : ℝ)|) := by
    exact hFirst.trans (by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_right hC₁ (div_nonneg hc.le (abs_nonneg _)))
  have hSecondC :
      ‖(∫ y in (L₁ : ℝ) - 1..(L₁ : ℝ),
          (((y - ((L₁ : ℝ) - 1) : ℝ) : ℂ) *
            e (section7FourierPhase x h (fareyPoint x a c)
              (fareyFrac x a c) c (k : ℝ) y))) +
        (∫ y in (L₁ : ℝ)..(L₂ : ℝ),
          e (section7FourierPhase x h (fareyPoint x a c)
            (fareyFrac x a c) c (k : ℝ) y)) +
        (∫ y in (L₂ : ℝ)..(L₂ : ℝ) + 1,
          (((((L₂ : ℝ) + 1) - y : ℝ) : ℂ) *
            e (section7FourierPhase x h (fareyPoint x a c)
              (fareyFrac x a c) c (k : ℝ) y)))‖ ≤
        C * ((c : ℝ) ^ 2 / (k : ℝ) ^ 2) := by
    exact hSecond.trans (by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_right hC₂
        (div_nonneg (sq_nonneg _) (sq_nonneg _)))
  rw [mul_min_of_nonneg _ _ hCpos.le]
  exact le_min hFirstC hSecondC

end IwaniecMozzochiEq73Conclusion

/-- The exact combined catalogue statement (7.3)/(7.4), obtained from the
high-frequency theorem above and the uniform low-frequency estimate. -/
theorem iwaniecMozzochi_eq73_eq74_holds : iwaniecMozzochi_eq73_eq74 := by
  obtain ⟨k₀, Cₕ, hk₀, hCₕ, hhigh⟩ :=
    IwaniecMozzochiEq73Conclusion.iwaniecMozzochi_eq73_holds
  obtain ⟨Cₗ, hCₗ, hlow⟩ :=
    IwaniecMozzochiEq74Conclusion.exists_trapezoid_bound
  let C : ℝ := max Cₕ Cₗ
  have hC : 0 < C := hCₕ.trans_le (le_max_left Cₕ Cₗ)
  refine ⟨k₀, C, hk₀, hC, ?_⟩
  intro x H M a c h L₁ L₂ hmain hfarey hhmem h12 hpole hL₁ hL₂
  constructor
  · intro k hk
    have hh := hhigh x H M a c h L₁ L₂ hmain hfarey hhmem h12 hpole
      hL₁ hL₂ k hk
    have hminNonneg : 0 ≤
        min ((c : ℝ) / |(k : ℝ)|) ((c : ℝ) ^ 2 / (k : ℝ) ^ 2) := by
      apply le_min
      · exact div_nonneg (by positivity) (abs_nonneg _)
      · exact div_nonneg (sq_nonneg _) (sq_nonneg _)
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_left Cₕ Cₗ) hminNonneg)
  · intro k _hk
    have hh := hlow x H M a c h L₁ L₂ hmain hfarey hhmem h12 hpole hL₂ k
    have hx : 0 < x := zero_lt_one.trans_le hmain.1
    have hH : 0 < H := zero_lt_one.trans_le hmain.2.2.2.1
    have hM : 0 < M := (Real.rpow_pos_of_pos hx theta0).trans hmain.2.1
    have hscaleNonneg : 0 ≤
        (x * H * M ^ (-(3 : ℝ))) ^ (-(1 : ℝ) / 2) :=
      Real.rpow_nonneg (by positivity) _
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_right Cₕ Cₗ) hscaleNonneg)

end

end LeanProofs.IntegerPoints
