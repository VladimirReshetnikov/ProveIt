import IntegerPoints.GKBProcessAux
import IntegerPoints.GKBProcessGeometry
import IntegerPoints.GKLegendreExtension

/-!
# Graham--Kolesnik B-process: stationary amplitudes

The stationary-phase main term carries the weight

`1 / sqrt |f''(x_nu)|`.

On the open derivative interval, differentiating the inverse equation and the
Legendre identity identifies this weight with `sqrt (-phi''(nu))`.  The latter
is the useful form for Abel summation: a third-order Graham--Kolesnik class
estimate makes `phi''` increasing, hence `sqrt (-phi'')` antitone.  The exact
inverse identity is not asserted at the endpoint frequencies.  Instead, the
curvature lower bound from `GKBProcessGeometry` gives a uniform estimate for
those at-most-two terms.

The final section records the fixed-phase and conjugation identities in the
literal form used for prefixes of the dual exponential sum.
-/

open scoped BigOperators Topology ContDiff
open Real Finset Set Filter

namespace LeanProofs.IntegerPoints

namespace GKB

/-! ## The two forms of the stationary weight -/

/-- The amplitude occurring literally in the stationary-phase sum. -/
noncomputable def stationaryWeight (f x : ℝ → ℝ) (nu : ℝ) : ℝ :=
  1 / Real.sqrt |iteratedDeriv 2 f (x nu)|

/-- The same amplitude expressed through the Legendre phase on the open
derivative interval. -/
noncomputable def dualWeight (phi : ℝ → ℝ) (nu : ℝ) : ℝ :=
  Real.sqrt (-iteratedDeriv 2 phi nu)

theorem stationaryWeight_pos_of_ne {f x : ℝ → ℝ} {nu : ℝ}
    (hcurv : iteratedDeriv 2 f (x nu) ≠ 0) :
    0 < stationaryWeight f x nu := by
  unfold stationaryWeight
  exact one_div_pos.mpr (Real.sqrt_pos.2 (abs_pos.mpr hcurv))

theorem dualWeight_pos_of_second_deriv_neg {phi : ℝ → ℝ} {nu : ℝ}
    (hphi2 : iteratedDeriv 2 phi nu < 0) :
    0 < dualWeight phi nu := by
  unfold dualWeight
  exact Real.sqrt_pos.2 (neg_pos.mpr hphi2)

/-! ## Differentiating the inverse and Legendre identities -/

/-- On the open derivative interval, the second derivative of the Legendre
phase is the reciprocal curvature of the original phase. -/
theorem iteratedDeriv_two_legendre_eq_inv
    {N s y eps a b : ℝ} {P : ℕ} {f x phi : ℝ → ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y)
    (hP : 2 ≤ P) (heps : 0 < eps) (heps_half : eps < 1 / 2)
    (hf : InGKClass N P s y eps a b f) (hab : a < b)
    (hx : ∀ nu ∈ Icc (deriv f b) (deriv f a),
      x nu ∈ Icc a b ∧ deriv f (x nu) = nu)
    (hphi : ∀ nu ∈ Icc (deriv f b) (deriv f a),
      phi nu = nu * x nu - f (x nu))
    {nu : ℝ} (hnu : nu ∈ Ioo (deriv f b) (deriv f a)) :
    iteratedDeriv 2 phi nu = (iteratedDeriv 2 f (x nu))⁻¹ := by
  have hnu_closed : nu ∈ Icc (deriv f b) (deriv f a) :=
    ⟨hnu.1.le, hnu.2.le⟩
  have hxnu := hx nu hnu_closed
  have hP_pred_ne : (((P - 1 : ℕ) : WithTop ℕ∞)) ≠ 0 := by
    exact_mod_cast (by omega : P - 1 ≠ 0)
  have hx_cd : ContDiffAt ℝ (P - 1) x nu :=
    GK39.inverse_contDiffAt hN hs hy hP heps heps_half hf hab hx hnu
  have hx_deriv : HasDerivAt x (deriv x nu) nu :=
    (hx_cd.differentiableAt hP_pred_ne).hasDerivAt
  have hf2 : ContDiff ℝ 2 f := GK39.contDiff_two hP hf
  have hf_deriv_cd : ContDiff ℝ 1 (deriv f) :=
    (contDiff_succ_iff_deriv.mp (show ContDiff ℝ (1 + 1) f from hf2)).2.2
  have houter : HasDerivAt (deriv f) (deriv (deriv f) (x nu)) (x nu) :=
    (hf_deriv_cd.differentiable one_ne_zero (x nu)).hasDerivAt
  have hcomp_deriv :
      HasDerivAt (fun v => deriv f (x v))
        (deriv (deriv f) (x nu) * deriv x nu) nu :=
    houter.comp nu hx_deriv
  have hinverse_eventually : (fun v => deriv f (x v)) =ᶠ[nhds nu] id := by
    filter_upwards [Ioo_mem_nhds hnu.1 hnu.2] with v hv
    simpa only [id_eq] using (hx v ⟨hv.1.le, hv.2.le⟩).2
  have hproduct : deriv (deriv f) (x nu) * deriv x nu = 1 := by
    calc
      deriv (deriv f) (x nu) * deriv x nu =
          deriv (fun v => deriv f (x v)) nu := hcomp_deriv.deriv.symm
      _ = deriv id nu := Filter.EventuallyEq.deriv_eq hinverse_eventually
      _ = 1 := by simp
  have hf2neg : deriv (deriv f) (x nu) < 0 :=
    GK39.deriv_deriv_neg_of_mem_Icc hN hs hy hP heps heps_half hf hxnu.1
  have hx_inv : deriv x nu = (deriv (deriv f) (x nu))⁻¹ := by
    apply (mul_eq_one_iff_eq_inv₀ hf2neg.ne).1
    rw [mul_comm]
    exact hproduct
  have hphi_eventually : deriv phi =ᶠ[nhds nu] x := by
    filter_upwards [Ioo_mem_nhds hnu.1 hnu.2] with v hv
    exact GK39.deriv_phi_eq_inverse hN hs hy hP heps heps_half hf hab hx hphi hv
  rw [GK34.iteratedDeriv_two phi, GK34.iteratedDeriv_two f,
    Filter.EventuallyEq.deriv_eq hphi_eventually, hx_inv]

/-- Away from the two endpoint frequencies, the literal stationary-phase
weight equals the square-root weight of the Legendre phase. -/
theorem stationaryWeight_eq_dualWeight
    {N s y eps a b : ℝ} {P : ℕ} {f x phi : ℝ → ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y)
    (hP : 2 ≤ P) (heps : 0 < eps) (heps_half : eps < 1 / 2)
    (hf : InGKClass N P s y eps a b f) (hab : a < b)
    (hx : ∀ nu ∈ Icc (deriv f b) (deriv f a),
      x nu ∈ Icc a b ∧ deriv f (x nu) = nu)
    (hphi : ∀ nu ∈ Icc (deriv f b) (deriv f a),
      phi nu = nu * x nu - f (x nu))
    {nu : ℝ} (hnu : nu ∈ Ioo (deriv f b) (deriv f a)) :
    stationaryWeight f x nu = dualWeight phi nu := by
  have hnu_closed : nu ∈ Icc (deriv f b) (deriv f a) :=
    ⟨hnu.1.le, hnu.2.le⟩
  have hxnu := hx nu hnu_closed
  have hcurv : iteratedDeriv 2 f (x nu) < 0 :=
    GK39.iteratedDeriv_two_neg_of_mem_Icc
      hN hs hy hP heps heps_half hf hxnu.1
  have hphi2 := iteratedDeriv_two_legendre_eq_inv
    hN hs hy hP heps heps_half hf hab hx hphi hnu
  unfold stationaryWeight dualWeight
  rw [hphi2, abs_of_neg hcurv]
  have hneg_inv : -(iteratedDeriv 2 f (x nu))⁻¹ =
      (-iteratedDeriv 2 f (x nu))⁻¹ := by
    rw [neg_inv]
  rw [hneg_inv, Real.sqrt_inv]
  simp only [one_div]

/-- Closed-interval membership together with exclusion of the two endpoints
is the open-interval hypothesis required by `stationaryWeight_eq_dualWeight`.
-/
theorem stationaryWeight_eq_dualWeight_of_mem_ne
    {N s y eps a b : ℝ} {P : ℕ} {f x phi : ℝ → ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y)
    (hP : 2 ≤ P) (heps : 0 < eps) (heps_half : eps < 1 / 2)
    (hf : InGKClass N P s y eps a b f) (hab : a < b)
    (hx : ∀ nu ∈ Icc (deriv f b) (deriv f a),
      x nu ∈ Icc a b ∧ deriv f (x nu) = nu)
    (hphi : ∀ nu ∈ Icc (deriv f b) (deriv f a),
      phi nu = nu * x nu - f (x nu))
    {nu : ℝ} (hnu : nu ∈ Icc (deriv f b) (deriv f a))
    (hnu_left : nu ≠ deriv f b) (hnu_right : nu ≠ deriv f a) :
    stationaryWeight f x nu = dualWeight phi nu := by
  apply stationaryWeight_eq_dualWeight
    hN hs hy hP heps heps_half hf hab hx hphi
  exact ⟨lt_of_le_of_ne hnu.1 hnu_left.symm,
    lt_of_le_of_ne hnu.2 hnu_right⟩

/-! ## Positivity and antitonicity from a third-order dual class -/

/-- The order-one class estimate forces negative second derivative when the
relative error is at most `1/4`. -/
theorem class_second_derivative_neg
    {J sigma eta delta c d : ℝ} {P : ℕ} {phi : ℝ → ℝ}
    (hJ : 0 < J) (hsigma : 0 < sigma) (heta : 0 < eta)
    (hP : 3 ≤ P) (hdelta : delta ≤ 1 / 4)
    (hphi : InGKClass J P sigma eta delta c d phi) :
    ∀ nu ∈ Icc c d, iteratedDeriv 2 phi nu < 0 := by
  intro nu hnu
  have hnu0 : 0 < nu := GK39.point_pos hJ hphi hnu
  have hmodel : 0 < sigma * eta * nu ^ (-sigma - 1) := by positivity
  have hbound := GKB.neg_bounds_of_abs_add_model_lt hmodel.le hdelta
    (GKB.abs_iteratedDeriv_two_add_model_lt (by omega) hphi hnu)
  linarith [hbound.1]

/-- At order two the same class estimate forces positive third derivative. -/
theorem class_third_derivative_pos
    {J sigma eta delta c d : ℝ} {P : ℕ} {phi : ℝ → ℝ}
    (hJ : 0 < J) (hsigma : 0 < sigma) (heta : 0 < eta)
    (hP : 3 ≤ P) (hdelta : delta ≤ 1 / 4)
    (hphi : InGKClass J P sigma eta delta c d phi) :
    ∀ nu ∈ Icc c d, 0 < iteratedDeriv 3 phi nu := by
  intro nu hnu
  have hnu0 : 0 < nu := GK39.point_pos hJ hphi hnu
  have hmodel : 0 < sigma * (sigma + 1) * eta * nu ^ (-sigma - 2) := by
    positivity
  have happrox := abs_lt.mp
    (GKB.abs_iteratedDeriv_three_sub_model_lt hP hphi hnu)
  have hsmall : delta *
      (sigma * (sigma + 1) * eta * nu ^ (-sigma - 2)) ≤
      1 / 4 * (sigma * (sigma + 1) * eta * nu ^ (-sigma - 2)) :=
    mul_le_mul_of_nonneg_right hdelta hmodel.le
  linarith

/-- On a third-order dual class, the Legendre amplitude is positive and
antitone throughout the full closed dyadic interval. -/
theorem dualWeight_pos_antitone
    {J sigma eta delta c d : ℝ} {P : ℕ} {phi : ℝ → ℝ}
    (hJ : 0 < J) (hsigma : 0 < sigma) (heta : 0 < eta)
    (hP : 3 ≤ P) (hdelta : delta ≤ 1 / 4)
    (hphi : InGKClass J P sigma eta delta c d phi) :
    (∀ nu ∈ Icc c d, 0 < dualWeight phi nu) ∧
      AntitoneOn (dualWeight phi) (Icc c d) := by
  have hphi_cd : ContDiff ℝ P phi := hphi.2.2.2.1
  have hD2_diff : Differentiable ℝ (iteratedDeriv 2 phi) :=
    hphi_cd.differentiable_iteratedDeriv 2 (by
      exact_mod_cast (show 2 < P by omega))
  have hD2_mono : MonotoneOn (iteratedDeriv 2 phi) (Icc c d) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc c d)
      hD2_diff.continuous.continuousOn hD2_diff.differentiableOn ?_
    intro nu hnu
    rw [← iteratedDeriv_succ]
    exact (class_third_derivative_pos hJ hsigma heta hP hdelta hphi nu
      (interior_subset hnu)).le
  constructor
  · intro nu hnu
    exact dualWeight_pos_of_second_deriv_neg
      (class_second_derivative_neg hJ hsigma heta hP hdelta hphi nu hnu)
  · intro u hu v hv huv
    unfold dualWeight
    exact Real.sqrt_le_sqrt (neg_le_neg (hD2_mono hu hv huv))

/-! ## Uniform treatment of endpoint frequencies -/

/-- The curvature scale that bounds every stationary weight, including at the
two endpoint frequencies where the inverse identity is not used. -/
noncomputable def curvatureWeightBound (N s y : ℝ) : ℝ :=
  1 / Real.sqrt
    (GKB.curvatureLower s * GKB.phaseScale N s y * N ^ (-(2 : ℝ)))

theorem curvatureWeightBound_pos {N s y : ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y) :
    0 < curvatureWeightBound N s y := by
  unfold curvatureWeightBound
  have hc := (GKB.curvatureConstants_pos hs).1
  have hF := GKB.phaseScale_pos (s := s) hN hy
  positivity

/-- The endpoint bound has the expected B-process dimension
`c(s)^(-1/2) F^(-1/2) N`. -/
theorem curvatureWeightBound_eq {N s y : ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y) :
    curvatureWeightBound N s y =
      GKB.curvatureLower s ^ (-(1 : ℝ) / 2) *
        GKB.phaseScale N s y ^ (-(1 : ℝ) / 2) * N := by
  have hc : 0 < GKB.curvatureLower s := (GKB.curvatureConstants_pos hs).1
  have hF : 0 < GKB.phaseScale N s y := GKB.phaseScale_pos (s := s) hN hy
  let q : ℝ := GKB.curvatureLower s * GKB.phaseScale N s y * N ^ (-(2 : ℝ))
  have hq : 0 < q := by dsimp [q]; positivity
  have hsqrt_inv : (Real.sqrt q)⁻¹ = q ^ (-(1 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, show -(1 : ℝ) / 2 = -(1 / 2) by ring,
      Real.rpow_neg hq.le]
  unfold curvatureWeightBound
  change 1 / Real.sqrt q = _
  rw [one_div, hsqrt_inv]
  dsimp only [q]
  exact GK36.inverse_sqrt_scale hc hF hN

/-- Curvature controls the literal stationary weight uniformly on the whole
closed frequency interval. -/
theorem stationaryWeight_le_curvatureWeightBound
    {N s y eps a b : ℝ} {P : ℕ} {f x : ℝ → ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y)
    (hP : 4 ≤ P) (heps : eps ≤ 1 / 4)
    (hf : InGKClass N P s y eps a b f)
    (hx : ∀ nu ∈ Icc (deriv f b) (deriv f a),
      x nu ∈ Icc a b ∧ deriv f (x nu) = nu)
    {nu : ℝ} (hnu : nu ∈ Icc (deriv f b) (deriv f a)) :
    stationaryWeight f x nu ≤ curvatureWeightBound N s y := by
  have hxnu := hx nu hnu
  have hcurv := GKB.second_derivative_bounds hN hs hy hP heps hf (x nu) hxnu.1
  have hneg := GKB.second_derivative_neg hN hs hy hP heps hf (x nu) hxnu.1
  have hlower :
      0 < GKB.curvatureLower s * GKB.phaseScale N s y * N ^ (-(2 : ℝ)) := by
    have hc := (GKB.curvatureConstants_pos hs).1
    have hF := GKB.phaseScale_pos (s := s) hN hy
    positivity
  unfold stationaryWeight curvatureWeightBound
  rw [abs_of_neg hneg]
  exact one_div_le_one_div_of_le (Real.sqrt_pos.2 hlower)
    (Real.sqrt_le_sqrt hcurv.1)

/-- In particular, both possible endpoint-frequency terms satisfy the same
curvature bound and can be removed before Abel summation. -/
theorem endpoint_stationaryWeights_le
    {N s y eps a b : ℝ} {P : ℕ} {f x : ℝ → ℝ}
    (hN : 0 < N) (hs : 0 < s) (hy : 0 < y)
    (hP : 4 ≤ P) (heps : eps ≤ 1 / 4)
    (hf : InGKClass N P s y eps a b f)
    (hx : ∀ nu ∈ Icc (deriv f b) (deriv f a),
      x nu ∈ Icc a b ∧ deriv f (x nu) = nu) :
    stationaryWeight f x (deriv f b) ≤ curvatureWeightBound N s y ∧
      stationaryWeight f x (deriv f a) ≤ curvatureWeightBound N s y := by
  have hendpoints := GKB.endpoint_derivative_bounds hN hs hy hP heps hf
  exact ⟨
    stationaryWeight_le_curvatureWeightBound hN hs hy hP heps hf hx
      ⟨le_rfl, hendpoints.2.2.2.1⟩,
    stationaryWeight_le_curvatureWeightBound hN hs hy hP heps hf hx
      ⟨hendpoints.2.2.2.1, le_rfl⟩⟩

/-! ## The dual phase in exponent-pair form -/

/-- Substituting the Legendre identity turns the stationary phase into
`-phi - 1/8`. -/
theorem stationary_phase_eq_neg_legendre {f x phi : ℝ → ℝ} {nu : ℝ}
    (hphi : phi nu = nu * x nu - f (x nu)) :
    f (x nu) - nu * x nu - 1 / 8 = -phi nu - 1 / 8 := by
  rw [hphi]
  ring

/-- Every prefix of `e(-phi-1/8)` has exactly the norm of the corresponding
exponent-pair sum for `phi`: `-1/8` is a fixed phase and negation is complex
conjugation. -/
theorem norm_sum_intRange_e_neg_phi_sub_eighth (A T : ℝ) (phi : ℝ → ℝ) :
    ‖∑ n ∈ intRange A T, e (-phi n - 1 / 8)‖ =
      ‖∑ n ∈ intRange A T, e (phi n)‖ := by
  have hphase : ∀ n : ℕ,
      -phi (n : ℝ) - 1 / 8 = -(1 / 8 : ℝ) - phi (n : ℝ) := by
    intro n
    ring
  simpa only [hphase] using
    GKB.norm_sum_e_const_sub
      (intRange A T) (fun n : ℕ => phi (n : ℝ)) (-(1 / 8 : ℝ))

end GKB

end LeanProofs.IntegerPoints
