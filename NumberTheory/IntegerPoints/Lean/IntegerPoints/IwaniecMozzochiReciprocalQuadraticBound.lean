import IntegerPoints.GKLemma32
import IntegerPoints.Lemma9Tools
import IntegerPoints.SP2Parts

/-!
# A uniform bound for reciprocal-quadratic oscillatory integrals

This file supplies the cancellation estimate needed when the lower cutoff in
the generalized reciprocal-Bessel transform is removed.  The normalized
phase is

```
  Q q u = -u^2 - q/u^2.
```

The estimate is uniform in both the real parameter `q` and the finite upper
endpoint.  For `q >= 0`, the second derivative has absolute value at least
`2`.  For `q = -r < 0`, small `r` is treated trivially below `u = 2` and by
the second-derivative test above it.  When `r >= 1`, the first derivative has
absolute value at least `2`; its reciprocal is monotone on each side of the
unique inflection point `(3r)^(1/4)`.

The Graham--Kolesnik APIs ask for a globally `C^2` phase.  Since `Q` has a
pole at zero, applications on `[eta,U]` use the standard positive smooth
denominator `L9.hfun`, rescaled so that the extension agrees with `Q` on the
whole interval.  This is an implementation detail: the exported theorem is
about the literal reciprocal phase.
-/

open Real Set MeasureTheory intervalIntegral

noncomputable section

namespace LeanProofs.IntegerPoints

namespace ReciprocalQuadratic

/-- The literal normalized reciprocal-quadratic phase. -/
noncomputable def phase (q u : Real) : Real :=
  -(u ^ 2) - q / u ^ 2

private def phaseDeriv (q u : Real) : Real :=
  -2 * u + 2 * q / u ^ 3

private def phaseDeriv2 (q u : Real) : Real :=
  -2 - 6 * q / u ^ 4

private theorem phase_hasDerivAt {q u : Real} (hu : u ≠ 0) :
    HasDerivAt (phase q) (phaseDeriv q u) u := by
  unfold phase phaseDeriv
  have hquot := (hasDerivAt_const u q).div ((hasDerivAt_id' u).pow 2)
    (pow_ne_zero 2 hu)
  apply (((hasDerivAt_id' u).pow 2).neg.sub hquot).congr_deriv
  simp only [Pi.pow_apply]
  field_simp [hu]
  ring

private theorem phaseDeriv_hasDerivAt {q u : Real} (hu : u ≠ 0) :
    HasDerivAt (phaseDeriv q) (phaseDeriv2 q u) u := by
  unfold phaseDeriv phaseDeriv2
  have hquot := (hasDerivAt_const u (2 * q)).div
    ((hasDerivAt_id' u).pow 3) (pow_ne_zero 3 hu)
  apply (((hasDerivAt_id' u).const_mul (-2)).add hquot).congr_deriv
  simp only [Pi.pow_apply]
  field_simp [hu]
  ring

private theorem phase_deriv {q u : Real} (hu : u ≠ 0) :
    deriv (phase q) u = phaseDeriv q u :=
  (phase_hasDerivAt hu).deriv

private theorem phase_iteratedDeriv_two {q u : Real} (hu : 0 < u) :
    iteratedDeriv 2 (phase q) u = phaseDeriv2 q u := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hderiv : deriv (phase q) =ᶠ[nhds u] phaseDeriv q := by
    filter_upwards [eventually_ne_nhds hu.ne'] with v hv
    exact phase_deriv hv
  rw [hderiv.deriv_eq]
  exact (phaseDeriv_hasDerivAt hu.ne').deriv

private theorem measurable_phase (q : Real) : Measurable (fun u => e (phase q u)) := by
  unfold phase e
  fun_prop

private theorem intervalIntegrable_phase (q p U : Real) :
    IntervalIntegrable (fun u => e (phase q u)) volume p U := by
  apply SP.intervalIntegrable_of_bounded_on_complex (measurable_phase q)
  intro u _
  rw [norm_e]

private theorem phase_piece_trivial {q p U : Real} (hpU : p <= U) :
    norm (∫ u in p..U, e (phase q u)) <= U - p := by
  have h := norm_integral_le_of_norm_le_const
    (a := p) (b := U) (C := 1) (f := fun u => e (phase q u))
    (fun u _ => by rw [norm_e])
  rw [one_mul, abs_of_nonneg (sub_nonneg.mpr hpU)] at h
  exact h

/-! ## A globally smooth extension away from the pole -/

private noncomputable def safeRadius (eta u : Real) : Real :=
  eta * L9.hfun (u / eta)

private noncomputable def safePhase (q eta u : Real) : Real :=
  -(u ^ 2) - q / (safeRadius eta u) ^ 2

private theorem safeRadius_ne {eta : Real} (heta : 0 < eta) (u : Real) :
    safeRadius eta u ≠ 0 := by
  unfold safeRadius
  exact mul_ne_zero heta.ne' (L9.hfun_pos _).ne'

private theorem safePhase_contDiff {q eta : Real} (heta : 0 < eta) :
    ContDiff Real 2 (safePhase q eta) := by
  have hquot : ContDiff Real 2 (fun u : Real => u / eta) :=
    contDiff_id.div contDiff_const (fun _ => heta.ne')
  have hradius : ContDiff Real 2 (safeRadius eta) := by
    unfold safeRadius
    exact contDiff_const.mul ((L9.hfun_contDiff_nat 2).comp hquot)
  unfold safePhase
  exact (contDiff_id.pow 2).neg.sub
    (contDiff_const.div (hradius.pow 2)
      (fun u => pow_ne_zero 2 (safeRadius_ne heta u)))

private theorem safePhase_eq {q eta u : Real} (heta : 0 < eta)
    (hu : eta / 2 <= u) :
    safePhase q eta u = phase q u := by
  have hratio : (1 / 2 : Real) <= u / eta := by
    rw [le_div_iff₀ heta]
    linarith
  unfold safePhase safeRadius phase
  rw [L9.hfun_eq hratio]
  field_simp [heta.ne']

private theorem safePhase_eventuallyEq {q eta u : Real} (heta : 0 < eta)
    (hu : eta / 2 < u) :
    safePhase q eta =ᶠ[nhds u] phase q := by
  filter_upwards [Ioi_mem_nhds hu] with v hv
  exact safePhase_eq heta hv.le

private theorem safePhase_deriv {q eta u : Real} (heta : 0 < eta)
    (hu : eta / 2 < u) :
    deriv (safePhase q eta) u = phaseDeriv q u := by
  rw [(safePhase_eventuallyEq heta hu).deriv_eq]
  exact phase_deriv (by linarith)

private theorem safePhase_iteratedDeriv_two {q eta u : Real}
    (heta : 0 < eta) (hu : eta / 2 < u) :
    iteratedDeriv 2 (safePhase q eta) u = phaseDeriv2 q u := by
  rw [(safePhase_eventuallyEq heta hu).iteratedDeriv_eq 2]
  exact phase_iteratedDeriv_two (by linarith)

private theorem safePhase_second_deriv {q eta u : Real}
    (heta : 0 < eta) (hu : eta / 2 < u) :
    deriv (deriv (safePhase q eta)) u = phaseDeriv2 q u := by
  have h := safePhase_iteratedDeriv_two (q := q) heta hu
  rw [show (2 : Nat) = 1 + 1 by norm_num, iteratedDeriv_succ,
    iteratedDeriv_one] at h
  exact h

private theorem intervalIntegral_safe_eq {q eta p U : Real}
    (heta : 0 < eta) (hpU : p <= U) (hp : eta / 2 <= p) :
    (∫ u in p..U, e (safePhase q eta u)) =
      ∫ u in p..U, e (phase q u) := by
  apply intervalIntegral.integral_congr
  intro u hu
  rw [Set.uIcc_of_le hpU] at hu
  change e (safePhase q eta u) = e (phase q u)
  rw [safePhase_eq heta (hp.trans hu.1)]

/-! ## The two derivative-test pieces -/

private theorem secondDerivativePiece
    {C₂ q eta p U lam₂ : Real}
    (h₂ : forall (a b lam : Real) (f : Real -> Real), a <= b -> 0 < lam ->
      ContDiff Real 2 f ->
      (∀ x ∈ Icc a b, lam <= |iteratedDeriv 2 f x|) ->
      norm (∫ x in a..b, e (f x)) <= C₂ * lam ^ (-(1 : Real) / 2))
    (heta : 0 < eta) (hpU : p <= U) (hp : eta <= p)
    (hlam₂ : 0 < lam₂)
    (hcurv : ∀ u ∈ Icc p U, lam₂ <= |phaseDeriv2 q u|) :
    norm (∫ u in p..U, e (phase q u)) <=
      C₂ * lam₂ ^ (-(1 : Real) / 2) := by
  have hsmooth := safePhase_contDiff (q := q) heta
  have hbound := h₂ p U lam₂ (safePhase q eta) hpU hlam₂ hsmooth
    (fun u hu => by
      rw [safePhase_iteratedDeriv_two heta (by linarith [hp, hu.1])]
      exact hcurv u hu)
  rwa [intervalIntegral_safe_eq heta hpU
    (by linarith : eta / 2 <= p)] at hbound

private theorem firstDerivativeIncreasingPiece
    {C₁ q eta p U lam : Real}
    (h₁ : GK32.L31 C₁) (heta : 0 < eta) (hpU : p <= U)
    (hp : eta <= p) (hlam : 0 < lam)
    (hcurv : ∀ u ∈ Icc p U, 0 <= phaseDeriv2 q u)
    (hbig : ∀ u ∈ Icc p U, lam <= |phaseDeriv q u|) :
    norm (∫ u in p..U, e (phase q u)) <= C₁ / lam := by
  have hsmooth := safePhase_contDiff (q := q) heta
  have hbound := GK32.piece_bound h₁ hpU hlam hsmooth
    (fun u hu => by
      rw [safePhase_second_deriv heta (by linarith [hp, hu.1])]
      exact hcurv u hu)
    (fun u hu => by
      rw [safePhase_deriv heta (by linarith [hp, hu.1])]
      exact hbig u hu)
  rwa [intervalIntegral_safe_eq heta hpU
    (by linarith : eta / 2 <= p)] at hbound

private theorem firstDerivativeDecreasingPiece
    {C₁ q eta p U lam : Real}
    (h₁ : GK32.L31 C₁) (heta : 0 < eta) (hpU : p <= U)
    (hp : eta <= p) (hlam : 0 < lam)
    (hcurv : ∀ u ∈ Icc p U, phaseDeriv2 q u <= 0)
    (hbig : ∀ u ∈ Icc p U, lam <= |phaseDeriv q u|) :
    norm (∫ u in p..U, e (phase q u)) <= C₁ / lam := by
  have hsmooth := safePhase_contDiff (q := q) heta
  have hnegSmooth : ContDiff Real 2 (-safePhase q eta) := hsmooth.neg
  have hbound := GK32.piece_bound h₁ hpU hlam hnegSmooth
    (fun u hu => by
      have hsecond : deriv (deriv (-safePhase q eta)) u =
          -phaseDeriv2 q u := by
        have hderiv : deriv (-safePhase q eta) = -deriv (safePhase q eta) := by
          funext v
          exact deriv.neg
        rw [hderiv, deriv.neg,
          safePhase_second_deriv heta (by linarith [hp, hu.1])]
      rw [hsecond]
      linarith [hcurv u hu])
    (fun u hu => by
      have hderiv : deriv (-safePhase q eta) u = -phaseDeriv q u := by
        rw [deriv.neg, safePhase_deriv heta (by linarith [hp, hu.1])]
      rw [hderiv, abs_neg]
      exact hbig u hu)
  have hconj := GK32.integral_e_neg (safePhase q eta) p U
  change norm (∫ x in p..U, e (-safePhase q eta x)) <= C₁ / lam at hbound
  rw [hconj, Complex.norm_conj,
    intervalIntegral_safe_eq heta hpU
      (by linarith : eta / 2 <= p)] at hbound
  exact hbound

/-! ## Phase geometry -/

private theorem phaseDeriv_abs_ge_two_of_large_negative
    {r u : Real} (hr : 1 <= r) (hu : 0 < u) :
    2 <= |phaseDeriv (-r) u| := by
  have hsum : 1 <= u + r / u ^ 3 := by
    rcases le_or_gt 1 u with hu1 | hu1
    · have hnonneg : 0 <= r / u ^ 3 := by positivity
      linarith
    · have hu3 : u ^ 3 < 1 := by
        simpa using pow_lt_pow_left₀ hu1 hu.le (by norm_num : (3 : Nat) ≠ 0)
      have hfrac : 1 < r / u ^ 3 := by
        rw [lt_div_iff₀ (pow_pos hu 3)]
        nlinarith
      linarith
  unfold phaseDeriv
  have hfracPos : 0 < r / u ^ 3 := by positivity
  have hneg : -2 * u + 2 * (-r) / u ^ 3 < 0 := by
    have heq : -2 * u + 2 * (-r) / u ^ 3 =
        -2 * (u + r / u ^ 3) := by
      field_simp [hu.ne']
      ring
    rw [heq]
    nlinarith
  rw [abs_of_neg hneg]
  have heq : -(-2 * u + 2 * (-r) / u ^ 3) =
      2 * (u + r / u ^ 3) := by
    field_simp [hu.ne']
    ring
  rw [heq]
  nlinarith

private noncomputable def inflection (r : Real) : Real :=
  Real.sqrt (Real.sqrt (3 * r))

private theorem inflection_pos {r : Real} (hr : 0 < r) :
    0 < inflection r := by
  unfold inflection
  positivity

private theorem inflection_pow_four {r : Real} (hr : 0 <= r) :
    inflection r ^ 4 = 3 * r := by
  unfold inflection
  have hthree : 0 <= 3 * r := by positivity
  have hsqrt : 0 <= Real.sqrt (3 * r) := Real.sqrt_nonneg _
  calc
    Real.sqrt (Real.sqrt (3 * r)) ^ 4 =
        (Real.sqrt (Real.sqrt (3 * r)) ^ 2) ^ 2 := by ring
    _ = Real.sqrt (3 * r) ^ 2 := by rw [Real.sq_sqrt hsqrt]
    _ = 3 * r := Real.sq_sqrt hthree

private theorem phaseDeriv2_nonneg_before_inflection
    {r u : Real} (hr : 0 < r) (hu : 0 < u)
    (hus : u <= inflection r) :
    0 <= phaseDeriv2 (-r) u := by
  have hs0 := inflection_pos hr
  have hpow : u ^ 4 <= inflection r ^ 4 :=
    pow_le_pow_left₀ hu.le hus 4
  rw [inflection_pow_four hr.le] at hpow
  have hfrac : 2 <= 6 * r / u ^ 4 := by
    rw [le_div_iff₀ (pow_pos hu 4)]
    nlinarith
  unfold phaseDeriv2
  have heq : -2 - 6 * (-r) / u ^ 4 = -2 + 6 * r / u ^ 4 := by ring
  rw [heq]
  linarith

private theorem phaseDeriv2_nonpos_after_inflection
    {r u : Real} (hr : 0 < r) (hu : 0 < u)
    (hsu : inflection r <= u) :
    phaseDeriv2 (-r) u <= 0 := by
  have hs0 := inflection_pos hr
  have hpow : inflection r ^ 4 <= u ^ 4 :=
    pow_le_pow_left₀ hs0.le hsu 4
  rw [inflection_pow_four hr.le] at hpow
  have hfrac : 6 * r / u ^ 4 <= 2 := by
    rw [div_le_iff₀ (pow_pos hu 4)]
    nlinarith
  unfold phaseDeriv2
  have heq : -2 - 6 * (-r) / u ^ 4 = -2 + 6 * r / u ^ 4 := by ring
  rw [heq]
  linarith

private theorem phaseDeriv2_abs_ge_one_of_small_negative_tail
    {r u : Real} (hr : r <= 1) (hu : 2 <= u) :
    1 <= |phaseDeriv2 (-r) u| := by
  have hu0 : 0 < u := by linarith
  have hu2 : 4 <= u ^ 2 := by nlinarith [sq_nonneg (u - 2)]
  have hu4 : 16 <= u ^ 4 := by
    nlinarith [sq_nonneg (u ^ 2 - 4)]
  have hfrac : 6 * r / u ^ 4 <= 1 := by
    rw [div_le_one (pow_pos hu0 4)]
    nlinarith
  unfold phaseDeriv2
  have heq : -2 - 6 * (-r) / u ^ 4 = -2 + 6 * r / u ^ 4 := by ring
  rw [heq, abs_of_nonpos (by linarith)]
  linarith

/-! ## Uniform normalized estimate -/

/-- There is an absolute bound for every finite partial integral of the
normalized reciprocal-quadratic phase. -/
theorem exists_uniform_intervalIntegral_bound :
    exists B : Real, 0 <= B ∧
      forall (q U : Real), 0 <= U ->
        norm (∫ u in (0 : Real)..U, e (phase q u)) <= B := by
  obtain ⟨C₁, h₁⟩ := gk_lemma31_holds
  obtain ⟨C₂, h₂⟩ := gk_lemma32_holds
  have h₁' : GK32.L31 C₁ := h₁
  let B : Real := 2 + |C₂| + 2 * |C₁|
  have hB : 0 <= B := by
    dsimp only [B]
    positivity
  refine ⟨B, hB, ?_⟩
  intro q U hU
  rcases eq_or_lt_of_le hU with rfl | hUpos
  · rw [intervalIntegral.integral_same, norm_zero]
    exact hB
  rcases le_or_gt 0 q with hq | hq
  · -- Positive reciprocal parameter: `|Q''| >= 2` away from zero.
    have htarget : norm (∫ u in (0 : Real)..U, e (phase q u)) <= |C₂| := by
      refine le_of_forall_pos_le_add (fun epsilon hepsilon => ?_)
      let eta : Real := min (U / 2) epsilon
      have heta : 0 < eta := lt_min (by linarith) hepsilon
      have hetaU : eta <= U := by
        exact (min_le_left _ _).trans (by linarith)
      have hsmall : norm (∫ u in (0 : Real)..eta, e (phase q u)) <= eta := by
        simpa only [sub_zero] using
          phase_piece_trivial (q := q) (p := (0 : Real)) heta.le
      have hlarge := secondDerivativePiece h₂ heta hetaU le_rfl
        (by norm_num : (0 : Real) < 2) (fun u hu => by
          unfold phaseDeriv2
          have hu0 : 0 < u := heta.trans_le hu.1
          have hnonneg : 0 <= 6 * q / u ^ 4 := by positivity
          rw [abs_of_nonpos (by linarith)]
          linarith)
      have hsplit := integral_add_adjacent_intervals
        (intervalIntegrable_phase q 0 eta)
        (intervalIntegrable_phase q eta U)
      rw [← hsplit]
      calc
        norm ((∫ u in (0 : Real)..eta, e (phase q u)) +
            ∫ u in eta..U, e (phase q u)) <=
            norm (∫ u in (0 : Real)..eta, e (phase q u)) +
              norm (∫ u in eta..U, e (phase q u)) := norm_add_le _ _
        _ <= eta + C₂ * 2 ^ (-(1 : Real) / 2) :=
          add_le_add hsmall hlarge
        _ <= epsilon + |C₂| := by
          have hfactor0 : 0 <= (2 : Real) ^ (-(1 : Real) / 2) :=
            Real.rpow_nonneg (by norm_num) _
          have hfactor1 : (2 : Real) ^ (-(1 : Real) / 2) <= 1 :=
            Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
          have hetaeps : eta <= epsilon := min_le_right _ _
          calc
            eta + C₂ * 2 ^ (-(1 : Real) / 2) <=
                epsilon + |C₂| * 2 ^ (-(1 : Real) / 2) := by
              gcongr
              exact le_abs_self C₂
            _ <= epsilon + |C₂| := by
              simpa only [mul_one] using add_le_add_right
                (mul_le_mul_of_nonneg_left hfactor1 (abs_nonneg C₂)) epsilon
        _ = |C₂| + epsilon := by ring
    exact htarget.trans (by
      dsimp only [B]
      linarith [abs_nonneg C₁, abs_nonneg C₂])
  · -- Negative reciprocal parameter.
    let r : Real := -q
    have hr : 0 < r := by dsimp only [r]; linarith
    have hqr : q = -r := by
      dsimp only [r]
      ring
    rcases le_or_gt r 1 with hrSmall | hrLarge
    · rcases le_or_gt U 2 with hU2 | hU2
      · exact (phase_piece_trivial (q := q) (p := (0 : Real)) hU).trans (by
          dsimp only [B]
          linarith [abs_nonneg C₁, abs_nonneg C₂])
      · have hfirst : norm (∫ u in (0 : Real)..2, e (phase q u)) <= 2 := by
          simpa only [sub_zero] using phase_piece_trivial (q := q)
            (p := (0 : Real)) (U := (2 : Real)) (by norm_num)
        have htail := secondDerivativePiece h₂ (q := q)
          (eta := (2 : Real)) (p := (2 : Real)) (U := U) (lam₂ := (1 : Real))
          (by norm_num) hU2.le le_rfl (by norm_num)
          (fun u hu => by
            rw [hqr]
            exact phaseDeriv2_abs_ge_one_of_small_negative_tail
              hrSmall hu.1)
        have hsplit := integral_add_adjacent_intervals
          (intervalIntegrable_phase q 0 2)
          (intervalIntegrable_phase q 2 U)
        rw [← hsplit]
        calc
          norm ((∫ u in (0 : Real)..2, e (phase q u)) +
              ∫ u in (2 : Real)..U, e (phase q u)) <=
              norm (∫ u in (0 : Real)..2, e (phase q u)) +
                norm (∫ u in (2 : Real)..U, e (phase q u)) := norm_add_le _ _
          _ <= 2 + C₂ * 1 ^ (-(1 : Real) / 2) :=
            add_le_add hfirst htail
          _ <= B := by
            simp only [one_rpow, mul_one]
            dsimp only [B]
            linarith [le_abs_self C₂, abs_nonneg C₁]
    · have hrOne : 1 <= r := hrLarge.le
      have htarget : norm (∫ u in (0 : Real)..U, e (phase q u)) <=
          2 * |C₁| := by
        refine le_of_forall_pos_le_add (fun epsilon hepsilon => ?_)
        let eta : Real := min (U / 2) epsilon
        have heta : 0 < eta := lt_min (by linarith) hepsilon
        have hetaU : eta <= U := (min_le_left _ _).trans (by linarith)
        have hsmall : norm (∫ u in (0 : Real)..eta, e (phase q u)) <= eta := by
          simpa only [sub_zero] using
            phase_piece_trivial (q := q) (p := (0 : Real)) heta.le
        have hbig : ∀ u ∈ Icc eta U, 2 <= |phaseDeriv q u| := by
          intro u hu
          rw [hqr]
          exact phaseDeriv_abs_ge_two_of_large_negative hrOne
            (heta.trans_le hu.1)
        let s : Real := inflection r
        have hs0 : 0 < s := inflection_pos hr
        have hosc :
            norm (∫ u in eta..U, e (phase q u)) <= 2 * |C₁| := by
          rcases le_or_gt U s with hUs | hUs
          · have hone := firstDerivativeIncreasingPiece h₁' heta hetaU
                le_rfl (by norm_num : (0 : Real) < 2)
                (fun u hu => by
                  rw [hqr]
                  exact phaseDeriv2_nonneg_before_inflection hr
                    (heta.trans_le hu.1) (hu.2.trans hUs)) hbig
            exact hone.trans (by
              have hC : C₁ / 2 <= |C₁| := by
                nlinarith [le_abs_self C₁, abs_nonneg C₁]
              linarith [hC, abs_nonneg C₁])
          rcases le_or_gt s eta with hsEta | hsEta
          · have hone := firstDerivativeDecreasingPiece h₁' heta hetaU
                le_rfl (by norm_num : (0 : Real) < 2)
                (fun u hu => by
                  rw [hqr]
                  exact phaseDeriv2_nonpos_after_inflection hr
                    (heta.trans_le hu.1) (hsEta.trans hu.1)) hbig
            exact hone.trans (by
              have hC : C₁ / 2 <= |C₁| := by
                nlinarith [le_abs_self C₁, abs_nonneg C₁]
              linarith [hC, abs_nonneg C₁])
          · have hetaS : eta <= s := hsEta.le
            have hsU : s <= U := hUs.le
            have hleft := firstDerivativeIncreasingPiece h₁' heta hetaS
              le_rfl (by norm_num : (0 : Real) < 2)
              (fun u hu => by
                rw [hqr]
                exact phaseDeriv2_nonneg_before_inflection hr
                  (heta.trans_le hu.1) hu.2)
              (fun u hu => hbig u ⟨hu.1, hu.2.trans hsU⟩)
            have hright := firstDerivativeDecreasingPiece h₁' heta hsU
              hetaS (by norm_num : (0 : Real) < 2)
              (fun u hu => by
                rw [hqr]
                exact phaseDeriv2_nonpos_after_inflection hr
                  (hs0.trans_le hu.1) hu.1)
              (fun u hu => hbig u ⟨hetaS.trans hu.1, hu.2⟩)
            have hsplit := integral_add_adjacent_intervals
              (intervalIntegrable_phase q eta s)
              (intervalIntegrable_phase q s U)
            rw [← hsplit]
            calc
              norm ((∫ u in eta..s, e (phase q u)) +
                  ∫ u in s..U, e (phase q u)) <=
                  norm (∫ u in eta..s, e (phase q u)) +
                    norm (∫ u in s..U, e (phase q u)) := norm_add_le _ _
              _ <= C₁ / 2 + C₁ / 2 := add_le_add hleft hright
              _ <= 2 * |C₁| := by
                nlinarith [le_abs_self C₁, abs_nonneg C₁]
        have hsplit := integral_add_adjacent_intervals
          (intervalIntegrable_phase q 0 eta)
          (intervalIntegrable_phase q eta U)
        rw [← hsplit]
        calc
          norm ((∫ u in (0 : Real)..eta, e (phase q u)) +
              ∫ u in eta..U, e (phase q u)) <=
              norm (∫ u in (0 : Real)..eta, e (phase q u)) +
                norm (∫ u in eta..U, e (phase q u)) := norm_add_le _ _
          _ <= eta + 2 * |C₁| := add_le_add hsmall hosc
          _ <= 2 * |C₁| + epsilon := by
            have := min_le_right (U / 2) epsilon
            dsimp only [eta] at this ⊢
            linarith
      exact htarget.trans (by
        dsimp only [B]
        linarith [abs_nonneg C₁, abs_nonneg C₂])

end ReciprocalQuadratic

end LeanProofs.IntegerPoints
