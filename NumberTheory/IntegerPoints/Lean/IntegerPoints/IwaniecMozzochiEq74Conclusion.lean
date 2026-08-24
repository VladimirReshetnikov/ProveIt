import IntegerPoints.IwaniecMozzochiEq73Eq74

/-!
# Iwaniec--Mozzochi (7.4): the low-frequency conclusion

The second derivative of the reciprocal phase is independent of the Fourier
frequency `k`.  On the complete padded support of the trapezoid, the main-range
and Farey-cell hypotheses give

`|(r(l) + kl/c)''| >= (1 / 4096) * x * H * M^(-3)`.

The unweighted Graham--Kolesnik second-derivative estimate therefore applies
uniformly to every subinterval of that support.  The two affine unit ramps
cannot be discarded with the crude bound `1`: the scale
`x * H * M^(-3)` need not be at most one.  Instead, an integration-by-parts
form of Abel summation bounds each ramp by the same uniform subinterval bound.
Together with the middle interval this costs only a factor of three.

Consequently the estimate actually holds for every `k`; the final theorem
retains the exact low-frequency quantifier and all hypotheses of the catalogue
statement.  No new analytic premise is introduced.
-/

open Real Set intervalIntegral MeasureTheory

namespace LeanProofs.IntegerPoints

open IwaniecMozzochiEq73Eq74 IMReductionEq75

noncomputable section

namespace IwaniecMozzochiEq74Conclusion

/-! ## Unit-ramp Abel estimates -/

/-- A left unit ramp is bounded by a uniform bound for all tail integrals.

This is continuous Abel summation with the tail primitive
`G(x) = - integral x..b f`, whose derivative is `f`. -/
theorem norm_left_unit_ramp_integral_le
    {a b B : ℝ} {f : ℝ → ℂ} (hf : Continuous f)
    (hab : b - a = 1)
    (hsub : ∀ p q : ℝ, a ≤ p → p ≤ q → q ≤ b →
      ‖∫ x in p..q, f x‖ ≤ B) :
    ‖∫ x in a..b, ((x - a : ℝ) : ℂ) * f x‖ ≤ B := by
  have hab_le : a ≤ b := by linarith
  have hu : ∀ x ∈ uIcc a b,
      HasDerivAt (fun y : ℝ => ((y - a : ℝ) : ℂ)) (1 : ℂ) x := by
    intro x _
    simpa using ((hasDerivAt_id x).sub_const a).ofReal_comp
  have hv : ∀ x ∈ uIcc a b,
      HasDerivAt (fun y : ℝ => -(∫ t in y..b, f t)) (f x) x := by
    intro x _
    convert! (intervalIntegral.integral_hasDerivAt_left
        (hf.intervalIntegrable x b)
        hf.aestronglyMeasurable.stronglyMeasurableAtFilter
        hf.continuousAt).neg using 1
    all_goals simp
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    (continuous_const.intervalIntegrable _ _) (hf.intervalIntegrable _ _)
  have hid :
      (∫ x in a..b, ((x - a : ℝ) : ℂ) * f x) =
        ∫ x in a..b, ∫ t in x..b, f t := by
    simpa only [intervalIntegral.integral_same, neg_zero, mul_zero, sub_self,
      Complex.ofReal_zero, zero_mul, one_mul, intervalIntegral.integral_neg,
      sub_zero, zero_sub, neg_neg] using hparts
  rw [hid]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (C := B)
    (f := fun x => ∫ t in x..b, f t) (fun x hx => by
      rw [uIoc_of_le hab_le] at hx
      exact hsub x b hx.1.le hx.2 le_rfl)
  simpa only [hab, abs_one, mul_one] using hbound

/-- A right unit ramp is bounded by a uniform bound for all prefix integrals.

Here the primitive is `F(x) = integral a..x f`; the endpoint terms vanish
because the affine weight vanishes at `b` and `F(a) = 0`. -/
theorem norm_right_unit_ramp_integral_le
    {a b B : ℝ} {f : ℝ → ℂ} (hf : Continuous f)
    (hab : b - a = 1)
    (hsub : ∀ p q : ℝ, a ≤ p → p ≤ q → q ≤ b →
      ‖∫ x in p..q, f x‖ ≤ B) :
    ‖∫ x in a..b, ((b - x : ℝ) : ℂ) * f x‖ ≤ B := by
  have hab_le : a ≤ b := by linarith
  have hu : ∀ x ∈ uIcc a b,
      HasDerivAt (fun y : ℝ => ((b - y : ℝ) : ℂ)) (-1 : ℂ) x := by
    intro x _
    simpa using ((hasDerivAt_const x b).sub (hasDerivAt_id x)).ofReal_comp
  have hv : ∀ x ∈ uIcc a b,
      HasDerivAt (fun y : ℝ => ∫ t in a..y, f t) (f x) x := by
    intro x _
    exact intervalIntegral.integral_hasDerivAt_right
      (hf.intervalIntegrable a x)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter
      hf.continuousAt
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    (continuous_const.intervalIntegrable _ _) (hf.intervalIntegrable _ _)
  have hid :
      (∫ x in a..b, ((b - x : ℝ) : ℂ) * f x) =
        ∫ x in a..b, ∫ t in a..x, f t := by
    simpa only [intervalIntegral.integral_same, Complex.ofReal_zero, zero_mul,
      mul_zero, sub_self, neg_mul, one_mul, intervalIntegral.integral_neg,
      sub_zero, zero_sub, neg_neg] using hparts
  rw [hid]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (C := B)
    (f := fun x => ∫ t in a..x, f t) (fun x hx => by
      rw [uIoc_of_le hab_le] at hx
      exact hsub a x le_rfl hx.1.le hx.2)
  simpa only [hab, abs_one, mul_one] using hbound

/-! ## Main-range geometry on the padded Farey cell -/

/-- The representative Farey length is strictly smaller than `M` in the main
range.  Indeed `M^2 < x <= x c H`, while `c,H >= 1`. -/
theorem fareyLength_lt_M
    {x H M : ℝ} {a c : ℕ}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c) :
    fareyLength x H M c < M := by
  have hx : 0 < x := zero_lt_one.trans_le hmain.1
  have hMone : 1 < M :=
    (Real.one_le_rpow hmain.1 (by norm_num [theta0])).trans_lt hmain.2.1
  have hM : 0 < M := zero_lt_one.trans hMone
  have hH : 0 < H := zero_lt_one.trans_le hmain.2.2.2.1
  have hroot : M < Real.sqrt x := by
    simpa only [Real.sqrt_eq_rpow] using hmain.2.2.1
  have hMtwo : M ^ 2 < x := by
    nlinarith [Real.sq_sqrt hx.le]
  have hc : (1 : ℝ) ≤ c := by exact_mod_cast hfarey.1
  have hcPos : (0 : ℝ) < c := zero_lt_one.trans_le hc
  have hxc : x ≤ x * (c : ℝ) := by
    calc
      x = x * 1 := by ring
      _ ≤ x * (c : ℝ) := mul_le_mul_of_nonneg_left hc hx.le
  have hxcH : x * (c : ℝ) ≤ x * (c : ℝ) * H := by
    calc
      x * (c : ℝ) = x * (c : ℝ) * 1 := by ring
      _ ≤ x * (c : ℝ) * H :=
        mul_le_mul_of_nonneg_left hmain.2.2.2.1 (mul_nonneg hx.le (by positivity))
  have hden : M ^ 2 < x * (c : ℝ) * H := hMtwo.trans_le (hxc.trans hxcH)
  have hdenPos : 0 < x * (c : ℝ) * H := by positivity
  unfold fareyLength
  apply (div_lt_iff₀ hdenPos).2
  calc
    M ^ 3 = M * M ^ 2 := by ring
    _ < M * (x * (c : ℝ) * H) := mul_lt_mul_of_pos_left hden hM

/-- The denominator `m + y` stays between `1/2` and `11M` throughout the
complete padded support `[L₁-1,L₂+1]`. -/
theorem padded_denominator_bounds
    {x H M : ℝ} {a c : ℕ} {L₁ L₂ : ℤ}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c)
    (hpole : -(fareyPoint x a c : ℝ) < (L₁ : ℝ) - 1)
    (hL₂ : (L₂ : ℝ) < 8 * fareyLength x H M c)
    {y : ℝ} (hy : y ∈ Icc ((L₁ : ℝ) - 1) ((L₂ : ℝ) + 1)) :
    1 / 2 < (fareyPoint x a c : ℝ) + y ∧
      (fareyPoint x a c : ℝ) + y ≤ 11 * M := by
  have hx : 0 < x := zero_lt_one.trans_le hmain.1
  have hMone : 1 < M :=
    (Real.one_le_rpow hmain.1 (by norm_num [theta0])).trans_lt hmain.2.1
  have hM : 0 < M := zero_lt_one.trans hMone
  obtain ⟨hmPos, hvNonneg, _hvLt, hsum, _hcoef, _hsqrtLower, hsqrtUpper⟩ :=
    fareyPoint_geometry hmain hfarey
  have hmUpper : (fareyPoint x a c : ℝ) ≤ 2 * M := by
    linarith
  have hunit := section7_one_le_pole_distance
    (m := fareyPoint x a c) (L₁ := L₁) hpole
  have hlamM := fareyLength_lt_M hmain hfarey
  constructor
  · linarith [hy.1]
  · have hyUpper : y < 8 * M + 1 := by
      linarith [hy.2]
    nlinarith

/-- Uniform curvature lower bound on the complete padded support.  The
generous factor `4096` absorbs `(m+y)^3 <= (11M)^3`. -/
theorem padded_curvature_lower
    {x H M : ℝ} {a c h : ℕ} {L₁ L₂ : ℤ}
    (hmain : InMainRange x H M) (hfarey : InFareySet x H M a c)
    (hh : h ∈ intRange H (4 * H))
    (hpole : -(fareyPoint x a c : ℝ) < (L₁ : ℝ) - 1)
    (hL₂ : (L₂ : ℝ) < 8 * fareyLength x H M c)
    {y : ℝ} (hy : y ∈ Icc ((L₁ : ℝ) - 1) ((L₂ : ℝ) + 1)) :
    (1 / 4096 : ℝ) * (x * H * M ^ (-(3 : ℝ))) ≤
      |section7ReciprocalPhaseDeriv2 x h (fareyPoint x a c)
        (fareyFrac x a c) y| := by
  have hx : 0 < x := zero_lt_one.trans_le hmain.1
  have hH : 0 < H := zero_lt_one.trans_le hmain.2.2.2.1
  have hMone : 1 < M :=
    (Real.one_le_rpow hmain.1 (by norm_num [theta0])).trans_lt hmain.2.1
  have hM : 0 < M := zero_lt_one.trans hMone
  have hhBounds := mem_intRange_four_mul hH hh
  have hhPos : (0 : ℝ) < h := hH.trans hhBounds.1
  obtain ⟨hdenLower, hdenUpper⟩ :=
    padded_denominator_bounds hmain hfarey hpole hL₂ hy
  have hdenPos : 0 < (fareyPoint x a c : ℝ) + y := by linarith
  have hdenCubeUpper :
      ((fareyPoint x a c : ℝ) + y) ^ 3 ≤ 4096 * M ^ 3 := by
    calc
      ((fareyPoint x a c : ℝ) + y) ^ 3 ≤ (11 * M) ^ 3 :=
        pow_le_pow_left₀ hdenPos.le hdenUpper 3
      _ = 1331 * M ^ 3 := by ring
      _ ≤ 4096 * M ^ 3 :=
        mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hM.le 3)
  have hnum : x * H ≤ 2 * x * (h : ℝ) := by
    have hxHlt : x * H < x * (h : ℝ) :=
      mul_lt_mul_of_pos_left hhBounds.1 hx
    have hxhnonneg : 0 ≤ x * (h : ℝ) := by positivity
    nlinarith
  have hMnegThree : M ^ (-(3 : ℝ)) = 1 / M ^ 3 := by
    calc
      M ^ (-(3 : ℝ)) = (M ^ (3 : ℝ))⁻¹ := Real.rpow_neg hM.le 3
      _ = (M ^ 3)⁻¹ := by
        convert! congrArg (fun z : ℝ => z⁻¹) (Real.rpow_natCast M 3) using 1
      _ = 1 / M ^ 3 := by rw [one_div]
  calc
    (1 / 4096 : ℝ) * (x * H * M ^ (-(3 : ℝ))) =
        x * H / (4096 * M ^ 3) := by
      rw [hMnegThree]
      field_simp [hM.ne']
    _ ≤ 2 * x * (h : ℝ) /
        ((fareyPoint x a c : ℝ) + y) ^ 3 :=
      div_le_div₀ (by positivity) hnum (pow_pos hdenPos 3) hdenCubeUpper
    _ = |section7ReciprocalPhaseDeriv2 x h (fareyPoint x a c)
          (fareyFrac x a c) y| := by
      unfold section7ReciprocalPhaseDeriv2
      rw [abs_of_pos]
      positivity

/-! ## Uniform unweighted subinterval estimate -/

/-- The Graham--Kolesnik estimate, specialized to every subinterval of the
padded Farey cell.  The output constant is absolute and positive. -/
theorem exists_mainRange_subinterval_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (x H M : ℝ) (a c h : ℕ) (L₁ L₂ : ℤ) (k : ℤ) (p q : ℝ),
        InMainRange x H M → InFareySet x H M a c →
        h ∈ intRange H (4 * H) →
        -(fareyPoint x a c : ℝ) < (L₁ : ℝ) - 1 →
        (L₂ : ℝ) < 8 * fareyLength x H M c →
        (L₁ : ℝ) - 1 ≤ p → p ≤ q → q ≤ (L₂ : ℝ) + 1 →
        ‖∫ y in p..q,
          e (section7FourierPhase x h (fareyPoint x a c)
            (fareyFrac x a c) c (k : ℝ) y)‖ ≤
          C * (x * H * M ^ (-(3 : ℝ))) ^ (-(1 : ℝ) / 2) := by
  obtain ⟨C₀, hC₀⟩ := exists_section7_unweighted_second_derivative_bound
  refine ⟨(|C₀| + 1) * (1 / 4096 : ℝ) ^ (-(1 : ℝ) / 2), ?_, ?_⟩
  · exact mul_pos (by linarith [abs_nonneg C₀])
      (Real.rpow_pos_of_pos (by norm_num) _)
  · intro x H M a c h L₁ L₂ k p q hmain hfarey hh hpole hL₂
      hp hq hqUpper
    have hx : 0 < x := zero_lt_one.trans_le hmain.1
    have hH : 0 < H := zero_lt_one.trans_le hmain.2.2.2.1
    have hM : 0 < M :=
      (Real.rpow_pos_of_pos hx theta0).trans hmain.2.1
    have hscale : 0 < x * H * M ^ (-(3 : ℝ)) := by positivity
    have hlam : 0 < (1 / 4096 : ℝ) *
        (x * H * M ^ (-(3 : ℝ))) := by positivity
    have hpad : ∀ y ∈ Icc p q,
        y ∈ Icc ((L₁ : ℝ) - 1) ((L₂ : ℝ) + 1) := by
      intro y hy
      exact ⟨hp.trans hy.1, hy.2.trans hqUpper⟩
    have hvdc := hC₀ x h (fareyPoint x a c) (fareyFrac x a c)
      c (k : ℝ) p q
      ((1 / 4096 : ℝ) * (x * H * M ^ (-(3 : ℝ)))) hq hlam
      (fun y hy => (padded_denominator_bounds hmain hfarey hpole hL₂
        (hpad y hy)).1)
      (fun y hy => padded_curvature_lower hmain hfarey hh hpole hL₂
        (hpad y hy))
    have hC₀le : C₀ ≤ |C₀| + 1 := by
      linarith [le_abs_self C₀]
    have henlarge :
        C₀ * ((1 / 4096 : ℝ) *
            (x * H * M ^ (-(3 : ℝ)))) ^ (-(1 : ℝ) / 2) ≤
          (|C₀| + 1) * ((1 / 4096 : ℝ) *
            (x * H * M ^ (-(3 : ℝ)))) ^ (-(1 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_right hC₀le (Real.rpow_nonneg hlam.le _)
    calc
      ‖∫ y in p..q,
          e (section7FourierPhase x h (fareyPoint x a c)
            (fareyFrac x a c) c (k : ℝ) y)‖ ≤
          (|C₀| + 1) * ((1 / 4096 : ℝ) *
            (x * H * M ^ (-(3 : ℝ)))) ^ (-(1 : ℝ) / 2) :=
        hvdc.trans henlarge
      _ = ((|C₀| + 1) *
            (1 / 4096 : ℝ) ^ (-(1 : ℝ) / 2)) *
          (x * H * M ^ (-(3 : ℝ))) ^ (-(1 : ℝ) / 2) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1 / 4096) hscale.le]
        ring

/-! ## The complete trapezoid and the exact (7.4) quantifiers -/

/-- The complete trapezoid satisfies the second-derivative bound uniformly in
`k`.  Each of its two unit ramps and its middle interval costs one copy of the
same subinterval constant. -/
theorem exists_trapezoid_bound :
    ∃ C : ℝ, 0 < C ∧
      ∀ (x H M : ℝ) (a c h : ℕ) (L₁ L₂ : ℤ),
        InMainRange x H M → InFareySet x H M a c →
        h ∈ intRange H (4 * H) → L₁ < L₂ →
        -(fareyPoint x a c : ℝ) < (L₁ : ℝ) - 1 →
        (L₂ : ℝ) < 8 * fareyLength x H M c →
        ∀ k : ℤ,
          ‖trapezoidIntegral x h (fareyPoint x a c) (fareyFrac x a c)
            L₁ L₂ c k‖ ≤
            C * (x * H * M ^ (-(3 : ℝ))) ^ (-(1 : ℝ) / 2) := by
  obtain ⟨C, hCpos, hsub⟩ := exists_mainRange_subinterval_bound
  refine ⟨3 * C, mul_pos (by norm_num) hCpos, ?_⟩
  intro x H M a c h L₁ L₂ hmain hfarey hh h12 hpole hL₂ k
  have h12R : (L₁ : ℝ) ≤ (L₂ : ℝ) := by exact_mod_cast h12.le
  have hleftOrder : (L₁ : ℝ) - 1 ≤ (L₁ : ℝ) := by linarith
  have hrightOrder : (L₂ : ℝ) ≤ (L₂ : ℝ) + 1 := by linarith
  have hgeometry := fareyPoint_geometry hmain hfarey
  have hm : (fareyPoint x a c : ℝ) ≠ 0 := by
    exact_mod_cast hgeometry.1.ne'
  have hM : 0 < M :=
    (Real.rpow_pos_of_pos (zero_lt_one.trans_le hmain.1) theta0).trans hmain.2.1
  have hmvPos : 0 < (fareyPoint x a c : ℝ) + fareyFrac x a c := by
    rw [hgeometry.2.2.2.1]
    exact hM.trans_le hgeometry.2.2.2.2.2.1
  have hmv : (fareyPoint x a c : ℝ) + fareyFrac x a c ≠ 0 := hmvPos.ne'
  let S : ℝ := (x * H * M ^ (-(3 : ℝ))) ^ (-(1 : ℝ) / 2)
  let B : ℝ := C * S
  let f : ℝ → ℂ := fun y =>
    e (section7SmoothFourierPhase x h (fareyPoint x a c)
      (fareyFrac x a c) c (k : ℝ) y)
  have hf : Continuous f := by
    exact PS.continuous_e_comp
      (section7SmoothFourierPhase_contDiff_three x h (fareyPoint x a c)
        (fareyFrac x a c) c (k : ℝ)).continuous
  have horiginal : ∀ p q : ℝ,
      (L₁ : ℝ) - 1 ≤ p → p ≤ q → q ≤ (L₂ : ℝ) + 1 →
      ‖∫ y in p..q,
        e (section7FourierPhase x h (fareyPoint x a c)
          (fareyFrac x a c) c (k : ℝ) y)‖ ≤ B := by
    intro p q hp hq hqUpper
    exact hsub x H M a c h L₁ L₂ k p q hmain hfarey hh hpole hL₂
      hp hq hqUpper
  have hsmooth : ∀ p q : ℝ,
      (L₁ : ℝ) - 1 ≤ p → p ≤ q → q ≤ (L₂ : ℝ) + 1 →
      ‖∫ y in p..q, f y‖ ≤ B := by
    intro p q hp hq hqUpper
    have heq :
        (∫ y in p..q, f y) =
          ∫ y in p..q,
            e (section7FourierPhase x h (fareyPoint x a c)
              (fareyFrac x a c) c (k : ℝ) y) := by
      apply integral_congr
      intro y hy
      have hy' : y ∈ Icc p q := by
        simpa only [uIcc_of_le hq] using hy
      have hypad : y ∈ Icc ((L₁ : ℝ) - 1) ((L₂ : ℝ) + 1) :=
        ⟨hp.trans hy'.1, hy'.2.trans hqUpper⟩
      simp only [f]
      rw [section7SmoothFourierPhase_eq
        (padded_denominator_bounds hmain hfarey hpole hL₂ hypad).1.le]
    rw [heq]
    exact horiginal p q hp hq hqUpper
  have hleftEq :
      (∫ y in (L₁ : ℝ) - 1..(L₁ : ℝ),
          ((y - ((L₁ : ℝ) - 1) : ℝ) : ℂ) *
            e (section7FourierPhase x h (fareyPoint x a c)
              (fareyFrac x a c) c (k : ℝ) y)) =
        ∫ y in (L₁ : ℝ) - 1..(L₁ : ℝ),
          ((y - ((L₁ : ℝ) - 1) : ℝ) : ℂ) * f y := by
    apply integral_congr
    intro y hy
    have hy' : y ∈ Icc ((L₁ : ℝ) - 1) (L₁ : ℝ) := by
      simpa only [uIcc_of_le hleftOrder] using hy
    have hypad : y ∈ Icc ((L₁ : ℝ) - 1) ((L₂ : ℝ) + 1) :=
      ⟨hy'.1, hy'.2.trans (h12R.trans hrightOrder)⟩
    simp only [f]
    rw [section7SmoothFourierPhase_eq
      (padded_denominator_bounds hmain hfarey hpole hL₂ hypad).1.le]
  have hrightEq :
      (∫ y in (L₂ : ℝ)..(L₂ : ℝ) + 1,
          ((((L₂ : ℝ) + 1) - y : ℝ) : ℂ) *
            e (section7FourierPhase x h (fareyPoint x a c)
              (fareyFrac x a c) c (k : ℝ) y)) =
        ∫ y in (L₂ : ℝ)..(L₂ : ℝ) + 1,
          ((((L₂ : ℝ) + 1) - y : ℝ) : ℂ) * f y := by
    apply integral_congr
    intro y hy
    have hy' : y ∈ Icc (L₂ : ℝ) ((L₂ : ℝ) + 1) := by
      simpa only [uIcc_of_le hrightOrder] using hy
    have hypad : y ∈ Icc ((L₁ : ℝ) - 1) ((L₂ : ℝ) + 1) :=
      ⟨hleftOrder.trans (h12R.trans hy'.1), hy'.2⟩
    simp only [f]
    rw [section7SmoothFourierPhase_eq
      (padded_denominator_bounds hmain hfarey hpole hL₂ hypad).1.le]
  have hleft :
      ‖∫ y in (L₁ : ℝ) - 1..(L₁ : ℝ),
          ((y - ((L₁ : ℝ) - 1) : ℝ) : ℂ) *
            e (section7FourierPhase x h (fareyPoint x a c)
              (fareyFrac x a c) c (k : ℝ) y)‖ ≤ B := by
    rw [hleftEq]
    apply norm_left_unit_ramp_integral_le hf (by ring)
    intro p q hp hq hqUpper
    exact hsmooth p q hp hq (hqUpper.trans (h12R.trans hrightOrder))
  have hmiddle :
      ‖∫ y in (L₁ : ℝ)..(L₂ : ℝ),
        e (section7FourierPhase x h (fareyPoint x a c)
          (fareyFrac x a c) c (k : ℝ) y)‖ ≤ B := by
    exact horiginal (L₁ : ℝ) (L₂ : ℝ) hleftOrder h12R hrightOrder
  have hright :
      ‖∫ y in (L₂ : ℝ)..(L₂ : ℝ) + 1,
          ((((L₂ : ℝ) + 1) - y : ℝ) : ℂ) *
            e (section7FourierPhase x h (fareyPoint x a c)
              (fareyFrac x a c) c (k : ℝ) y)‖ ≤ B := by
    rw [hrightEq]
    apply norm_right_unit_ramp_integral_le hf (by ring)
    intro p q hp hq hqUpper
    exact hsmooth p q (hleftOrder.trans (h12R.trans hp)) hq hqUpper
  rw [section7_trapezoidIntegral_eq_three_intervals hm hmv h12 hpole]
  calc
    ‖(∫ y in (L₁ : ℝ) - 1..(L₁ : ℝ),
          ((y - ((L₁ : ℝ) - 1) : ℝ) : ℂ) *
            e (section7FourierPhase x h (fareyPoint x a c)
              (fareyFrac x a c) c (k : ℝ) y)) +
        (∫ y in (L₁ : ℝ)..(L₂ : ℝ),
          e (section7FourierPhase x h (fareyPoint x a c)
            (fareyFrac x a c) c (k : ℝ) y)) +
        (∫ y in (L₂ : ℝ)..(L₂ : ℝ) + 1,
          ((((L₂ : ℝ) + 1) - y : ℝ) : ℂ) *
            e (section7FourierPhase x h (fareyPoint x a c)
              (fareyFrac x a c) c (k : ℝ) y))‖ ≤ B + B + B := by
      exact norm_add₃_le.trans
        (add_le_add (add_le_add hleft hmiddle) hright)
    _ = (3 * C) *
        (x * H * M ^ (-(3 : ℝ))) ^ (-(1 : ℝ) / 2) := by
      simp only [B, S]
      ring

end IwaniecMozzochiEq74Conclusion

/-- **Iwaniec--Mozzochi (7.4).**  This is the low-frequency half of the
catalogue statement, with the same quantifier order and every range, cell, and
endpoint hypothesis retained.  In fact the proof above is uniform in `k`, so
the harmless choice `k₀ = 1` only presents it in the paper's stated form. -/
theorem iwaniecMozzochi_eq74_holds :
    ∃ k₀ C : ℝ, 0 < k₀ ∧ 0 < C ∧
      ∀ (x H M : ℝ) (a c h : ℕ) (L₁ L₂ : ℤ),
        InMainRange x H M → InFareySet x H M a c →
        h ∈ intRange H (4 * H) → L₁ < L₂ →
        -(fareyPoint x a c : ℝ) < (L₁ : ℝ) - 1 →
        -fareyLength x H M c < L₁ →
        (L₂ : ℝ) < 8 * fareyLength x H M c →
        ∀ k : ℤ, |(k : ℝ)| < k₀ →
          ‖trapezoidIntegral x h (fareyPoint x a c) (fareyFrac x a c)
            L₁ L₂ c k‖ ≤
            C * (x * H * M ^ (-(3 : ℝ))) ^ (-(1 : ℝ) / 2) := by
  obtain ⟨C, hCpos, hC⟩ :=
    IwaniecMozzochiEq74Conclusion.exists_trapezoid_bound
  refine ⟨1, C, zero_lt_one, hCpos, ?_⟩
  intro x H M a c h L₁ L₂ hmain hfarey hh h12 hpole _hL₁ hL₂ k _hk
  exact hC x H M a c h L₁ L₂ hmain hfarey hh h12 hpole hL₂ k

end

end LeanProofs.IntegerPoints
