import FabiusFunction.FabiusLambertFormalLog
import FabiusFunction.FabiusLambertSaddle
import FabiusFunction.SaddleLogExpansionPowerSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Arbitrary-order lower-Lambert expansion

This module upgrades the formal coefficient recurrence for the lower-Lambert
phase to a rigorous asymptotic expansion of every finite order.  It proves
the formal logarithmic cancellations using the full formal identities from
`FabiusLambertFormalLog` through their coefficient and finite-truncation
consequences, bounds the varying-coefficient real Taylor remainder, and then
uses stability of `u - log u / log 2` on the large positive branch to compare
the explicit truncation with the exact Lambert phase.  The imported identities
are purely formal and make no convergence claim; analytic estimates begin
only after a finite truncation is evaluated at the large parameter.
-/

set_option autoImplicit false

open scoped BigOperators
open Filter Asymptotics Polynomial Finset

namespace Fabius

private theorem powerSeries_trunc_subst_left
    {R : Type*} [CommRing R] (f g : PowerSeries R)
    (hg0 : PowerSeries.constantCoeff g = 0) (n : ℕ) :
    PowerSeries.trunc n
        ((PowerSeries.trunc n f : PowerSeries R).subst g) =
      PowerSeries.trunc n (f.subst g) := by
  have hg := PowerSeries.HasSubst.of_constantCoeff_zero' hg0
  ext m
  rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc]
  split_ifs with hm
  · rw [PowerSeries.coeff_subst' hg, PowerSeries.coeff_subst' hg]
    apply finsum_congr
    intro d
    rw [Polynomial.coeff_coe, PowerSeries.coeff_trunc]
    split_ifs with hd
    · rfl
    · have hdm : m < d := lt_of_lt_of_le hm (Nat.le_of_not_gt hd)
      have horder : (d : ENat) ≤ (g ^ d).order :=
        PowerSeries.le_order_pow_of_constantCoeff_eq_zero d hg0
      have hz : PowerSeries.coeff m (g ^ d) = 0 :=
        PowerSeries.coeff_of_lt_order m
          (lt_of_lt_of_le (ENat.coe_lt_coe.mpr hdm) horder)
      rw [hz, smul_zero, smul_zero]
  · rfl

private theorem powerSeries_trunc_subst_right
    {R : Type*} [CommRing R] (f g h : PowerSeries R)
    (hg0 : PowerSeries.constantCoeff g = 0)
    (hh0 : PowerSeries.constantCoeff h = 0) (n : ℕ)
    (htrunc : PowerSeries.trunc n g = PowerSeries.trunc n h) :
    PowerSeries.trunc n (f.subst g) =
      PowerSeries.trunc n (f.subst h) := by
  have hg := PowerSeries.HasSubst.of_constantCoeff_zero' hg0
  have hh := PowerSeries.HasSubst.of_constantCoeff_zero' hh0
  ext m
  rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc]
  split_ifs with hm
  · rw [PowerSeries.coeff_subst' hg, PowerSeries.coeff_subst' hh]
    apply finsum_congr
    intro d
    congr 1
    have heq : PowerSeries.trunc n (g ^ d) =
        PowerSeries.trunc n (h ^ d) := by
      rw [← PowerSeries.trunc_trunc_pow g n d,
        ← PowerSeries.trunc_trunc_pow h n d, htrunc]
    have hc := congrArg (fun p : Polynomial R => p.coeff m) heq
    simpa only [PowerSeries.coeff_trunc, if_pos hm] using hc
  · rfl

private theorem coe_eval₂_C_eq_subst_coe
    {R : Type*} [CommRing R] (p q : Polynomial R)
    (hq0 : q.coeff 0 = 0) :
    ((p.eval₂ Polynomial.C q : Polynomial R) : PowerSeries R) =
      (p : PowerSeries R).subst (q : PowerSeries R) := by
  have hqps : PowerSeries.constantCoeff (q : PowerSeries R) = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      Polynomial.coeff_coe, hq0]
  rw [PowerSeries.subst_coe
    (PowerSeries.HasSubst.of_constantCoeff_zero' hqps)]
  induction p using Polynomial.induction_on' with
  | add p r hp hr =>
      simp only [Polynomial.eval₂_add, Polynomial.coe_add, map_add, hp, hr]
  | monomial n c =>
      simp [Polynomial.eval₂_monomial, Polynomial.aeval_def]

private theorem polynomial_eval_log_isBigO_id (p : Polynomial ℝ) :
    (fun t : ℝ => p.eval (Real.log t)) =O[atTop] (fun t : ℝ => t) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [eval_add] using hp.add hq
  | monomial n c =>
      have h := (Real.isLittleO_pow_log_id_atTop (n := n)).isBigO.const_mul_left c
      apply h.congr_left
      intro t
      rw [eval_monomial]

private theorem polynomial_eval_log_isLittleO_id (p : Polynomial ℝ) :
    (fun t : ℝ => p.eval (Real.log t)) =o[atTop] (fun t : ℝ => t) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [eval_add] using hp.add hq
  | monomial n c =>
      have h := (Real.isLittleO_pow_log_id_atTop (n := n)).const_mul_left c
      apply h.congr_left
      intro t
      rw [eval_monomial]

/-- Evaluate the outer variable at `1/t` and the coefficient variable at
`log t`. -/
private noncomputable def nestedLambertEval
    (p : Polynomial (Polynomial ℝ)) (t : ℝ) : ℝ :=
  p.eval₂ (Polynomial.evalRingHom (Real.log t)) t⁻¹

private theorem inv_pow_isBigO_one (n : ℕ) :
    (fun t : ℝ => t⁻¹ ^ n) =O[atTop] (fun _ : ℝ => (1 : ℝ)) := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  simp only [Real.norm_eq_abs, abs_pow,
    abs_of_pos (inv_pos.mpr (zero_lt_one.trans_le ht)), abs_one, mul_one]
  exact pow_le_one₀ (inv_nonneg.mpr (zero_le_one.trans ht))
    (inv_le_one_of_one_le₀ ht)

private theorem nestedLambertEval_isBigO_id
    (p : Polynomial (Polynomial ℝ)) :
    nestedLambertEval p =O[atTop] (fun t : ℝ => t) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      apply (hp.add hq).congr_left
      intro t
      simp [nestedLambertEval]
  | monomial n c =>
      have h := (polynomial_eval_log_isBigO_id c).mul (inv_pow_isBigO_one n)
      apply h.congr'
      · filter_upwards with t
        simp [nestedLambertEval, eval₂_monomial]
      · filter_upwards with t
        simp

private theorem nestedLambertEval_isLittleO_id
    (p : Polynomial (Polynomial ℝ)) :
    nestedLambertEval p =o[atTop] (fun t : ℝ => t) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      apply (hp.add hq).congr_left
      intro t
      simp [nestedLambertEval]
  | monomial n c =>
      have h := (polynomial_eval_log_isLittleO_id c).mul_isBigO
        (inv_pow_isBigO_one n)
      apply h.congr'
      · filter_upwards with t
        simp [nestedLambertEval, eval₂_monomial]
      · filter_upwards with t
        simp

private theorem nestedLambertEval_mul_inv_pow_isBigO
    (p : Polynomial (Polynomial ℝ)) (N : ℕ) :
    (fun t : ℝ => t⁻¹ ^ (N + 1) * nestedLambertEval p t) =O[atTop]
      (fun t : ℝ => t⁻¹ ^ N) := by
  have h := (isBigO_refl (fun t : ℝ => t⁻¹ ^ (N + 1)) atTop).mul
    (nestedLambertEval_isBigO_id p)
  apply h.congr' Filter.EventuallyEq.rfl
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
  rw [pow_succ]
  field_simp

private noncomputable def dyadicLambertDisplacementTruncation
    (N : ℕ) : Polynomial (Polynomial ℝ) :=
  PowerSeries.trunc (N + 1) dyadicLambertDisplacementSeries

private noncomputable def dyadicLambertComposedLogTaylor
    (N : ℕ) : Polynomial (Polynomial ℝ) :=
  (PowerSeries.trunc (N + 1) (PowerSeries.log (Polynomial ℝ))).eval₂
    Polynomial.C
      (Polynomial.X * dyadicLambertDisplacementTruncation N)

private theorem trunc_dyadicLambertComposedLogTaylor (N : ℕ) :
    PowerSeries.trunc (N + 1)
        (dyadicLambertComposedLogTaylor N :
          PowerSeries (Polynomial ℝ)) =
      PowerSeries.trunc (N + 1)
        (SaddleExpansion.logSeries
          dyadicLambertUnitSeriesCoefficient) := by
  let P : Polynomial (Polynomial ℝ) :=
    dyadicLambertDisplacementTruncation N
  let q : Polynomial (Polynomial ℝ) :=
    PowerSeries.trunc (N + 1) (PowerSeries.log (Polynomial ℝ))
  let gN : PowerSeries (Polynomial ℝ) :=
    PowerSeries.X * (P : PowerSeries (Polynomial ℝ))
  let g : PowerSeries (Polynomial ℝ) :=
    PowerSeries.X * dyadicLambertDisplacementSeries
  have hgN0 : PowerSeries.constantCoeff gN = 0 := by
    dsimp [gN]
    simp
  have hg0 : PowerSeries.constantCoeff g = 0 := by
    dsimp [g]
    simp
  have houter0 :
      (Polynomial.X * P).coeff 0 = 0 := by simp
  have hcoe :
      (dyadicLambertComposedLogTaylor N :
          PowerSeries (Polynomial ℝ)) =
        (q : PowerSeries (Polynomial ℝ)).subst gN := by
    have h := coe_eval₂_C_eq_subst_coe q (Polynomial.X * P) houter0
    simpa [dyadicLambertComposedLogTaylor, P, q, gN] using h
  have hgtrunc : PowerSeries.trunc (N + 1) gN =
      PowerSeries.trunc (N + 1) g := by
    apply Polynomial.ext
    intro m
    rw [PowerSeries.coeff_trunc, PowerSeries.coeff_trunc]
    split_ifs with hm
    · cases m with
      | zero => simp [gN, g]
      | succ m =>
          rw [show m + 1 = Nat.succ m by omega]
          simp only [gN, g, PowerSeries.coeff_succ_X_mul,
            Polynomial.coeff_coe]
          dsimp [P]
          rw [dyadicLambertDisplacementTruncation,
            PowerSeries.coeff_trunc, if_pos (by omega)]
    · rfl
  rw [hcoe]
  calc
    PowerSeries.trunc (N + 1)
        ((q : PowerSeries (Polynomial ℝ)).subst gN) =
        PowerSeries.trunc (N + 1)
          ((PowerSeries.log (Polynomial ℝ)).subst gN) := by
      exact powerSeries_trunc_subst_left
        (PowerSeries.log (Polynomial ℝ)) gN hgN0 (N + 1)
    _ = PowerSeries.trunc (N + 1)
          ((PowerSeries.log (Polynomial ℝ)).subst g) := by
      exact powerSeries_trunc_subst_right
        (PowerSeries.log (Polynomial ℝ)) gN g hgN0 hg0
          (N + 1) hgtrunc
    _ = PowerSeries.trunc (N + 1)
          (PowerSeries.logOf
            (SaddleExpansion.massSeries
              dyadicLambertUnitSeriesCoefficient)) := by
      have harg :
          SaddleExpansion.massSeries
                dyadicLambertUnitSeriesCoefficient - 1 = g := by
        rw [massSeries_dyadicLambertUnitSeriesCoefficient]
        dsimp [g]
        ring
      rw [PowerSeries.logOf_eq, harg]
    _ = PowerSeries.trunc (N + 1)
          (SaddleExpansion.logSeries
            dyadicLambertUnitSeriesCoefficient) := by
      rw [SaddleExpansion.logSeries_eq_logOf
        dyadicLambertUnitSeriesCoefficient (by rfl)]

private noncomputable def dyadicLambertAlgebraicResidual
    (N : ℕ) : Polynomial (Polynomial ℝ) :=
  dyadicLambertDisplacementTruncation N -
      Polynomial.C (dyadicLambertDisplacementPolynomial 0) -
    Polynomial.C (Polynomial.C (Real.log 2)⁻¹) *
      dyadicLambertComposedLogTaylor N

private theorem X_pow_dvd_dyadicLambertAlgebraicResidual (N : ℕ) :
    Polynomial.X ^ (N + 1) ∣ dyadicLambertAlgebraicResidual N := by
  rw [Polynomial.X_pow_dvd_iff]
  intro m hm
  have hcomp := congrArg (fun p : Polynomial (Polynomial ℝ) => p.coeff m)
    (trunc_dyadicLambertComposedLogTaylor N)
  simp only [PowerSeries.coeff_trunc, if_pos hm,
    Polynomial.coeff_coe] at hcomp
  have htrunc :
      (dyadicLambertDisplacementTruncation N).coeff m =
        dyadicLambertDisplacementPolynomial m := by
    rw [dyadicLambertDisplacementTruncation,
      PowerSeries.coeff_trunc, if_pos hm,
      coeff_dyadicLambertDisplacementSeries]
  rw [dyadicLambertAlgebraicResidual, Polynomial.coeff_sub,
    Polynomial.coeff_sub, Polynomial.coeff_C_mul, htrunc, hcomp,
    SaddleExpansion.coeff_logSeries,
    dyadicLambertDisplacementPolynomial_eq_logCoeff]
  by_cases hm0 : m = 0
  · subst m
    simp
  · simp [Polynomial.coeff_C, hm0]

private theorem dyadicLambertAlgebraicResidual_isBigO (N : ℕ) :
    (fun t : ℝ => nestedLambertEval
      (dyadicLambertAlgebraicResidual N) t) =O[atTop]
        (fun t : ℝ => t⁻¹ ^ N) := by
  obtain ⟨Q, hQ⟩ := X_pow_dvd_dyadicLambertAlgebraicResidual N
  have h := nestedLambertEval_mul_inv_pow_isBigO Q N
  apply h.congr_left
  intro t
  rw [hQ]
  simp [nestedLambertEval]

private noncomputable def realLogOnePlusTaylor (N : ℕ) (z : ℝ) : ℝ :=
  -∑ i ∈ Finset.range N, (-z) ^ (i + 1) / (i + 1)

private theorem eval₂_trunc_log_eq_realLogOnePlusTaylor
    (N : ℕ) (ell z : ℝ) :
    (PowerSeries.trunc (N + 1)
        (PowerSeries.log (Polynomial ℝ))).eval₂
          (Polynomial.evalRingHom ell) z =
      realLogOnePlusTaylor N z := by
  rw [PowerSeries.eval₂_trunc_eq_sum_range]
  rw [Finset.sum_range_succ']
  simp only [PowerSeries.coeff_log]
  simp only [Nat.succ_ne_zero, ↓reduceIte, map_zero, zero_mul,
    pow_zero, add_zero]
  unfold realLogOnePlusTaylor
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  norm_num
  ring

private theorem nestedLambertEval_composedLogTaylor (N : ℕ) (t : ℝ) :
    nestedLambertEval (dyadicLambertComposedLogTaylor N) t =
      realLogOnePlusTaylor N
        (t⁻¹ * nestedLambertEval
          (dyadicLambertDisplacementTruncation N) t) := by
  unfold nestedLambertEval dyadicLambertComposedLogTaylor
  change (Polynomial.eval₂RingHom
      (Polynomial.evalRingHom (Real.log t)) t⁻¹)
        ((PowerSeries.trunc (N + 1)
          (PowerSeries.log (Polynomial ℝ))).eval₂ Polynomial.C
            (Polynomial.X * dyadicLambertDisplacementTruncation N)) = _
  rw [Polynomial.hom_eval₂]
  have hc :
      (Polynomial.eval₂RingHom
          (Polynomial.evalRingHom (Real.log t)) t⁻¹).comp
          Polynomial.C = Polynomial.evalRingHom (Real.log t) := by
    ext p
    · simp [Polynomial.evalRingHom]
    · change Polynomial.eval₂ (Polynomial.evalRingHom (Real.log t)) t⁻¹
          (Polynomial.C Polynomial.X) =
        Polynomial.eval (Real.log t) Polynomial.X
      simp
  have hz :
      (Polynomial.eval₂RingHom
          (Polynomial.evalRingHom (Real.log t)) t⁻¹)
            (Polynomial.X * dyadicLambertDisplacementTruncation N) =
        t⁻¹ * (dyadicLambertDisplacementTruncation N).eval₂
          (Polynomial.evalRingHom (Real.log t)) t⁻¹ := by
    simp
  rw [hc, hz]
  rw [eval₂_trunc_log_eq_realLogOnePlusTaylor]

private theorem abs_log_one_add_sub_taylor_le
    (N : ℕ) {z : ℝ} (hz : |z| < 1) :
    |Real.log (1 + z) - realLogOnePlusTaylor N z| ≤
      |z| ^ (N + 1) / (1 - |z|) := by
  have h := Real.abs_log_sub_add_sum_range_le
    (x := -z) (by simpa using hz) N
  simpa [realLogOnePlusTaylor, abs_neg, add_comm, sub_eq_add_neg]
    using h

private theorem dyadicLambertTruncatedPerturbation_tendsto_zero (N : ℕ) :
    Tendsto (fun t : ℝ => t⁻¹ * nestedLambertEval
      (dyadicLambertDisplacementTruncation N) t) atTop (nhds 0) := by
  have h := nestedLambertEval_isLittleO_id
    (dyadicLambertDisplacementTruncation N)
  apply h.tendsto_div_nhds_zero.congr'
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with t ht
  field_simp

private theorem dyadicLambertPerturbation_pow_isBigO (N : ℕ) :
    (fun t : ℝ =>
      (t⁻¹ * nestedLambertEval
        (dyadicLambertDisplacementTruncation N) t) ^ (N + 1)) =O[atTop]
        (fun t : ℝ => t⁻¹ ^ N) := by
  have h := nestedLambertEval_mul_inv_pow_isBigO
    ((dyadicLambertDisplacementTruncation N) ^ (N + 1)) N
  apply h.congr_left
  intro t
  unfold nestedLambertEval
  rw [Polynomial.eval₂_pow, mul_pow]

private theorem dyadicLambertLogTaylorError_isBigO (N : ℕ) :
    (fun t : ℝ =>
      Real.log (1 + t⁻¹ * nestedLambertEval
        (dyadicLambertDisplacementTruncation N) t) -
      nestedLambertEval (dyadicLambertComposedLogTaylor N) t) =O[atTop]
        (fun t : ℝ => t⁻¹ ^ N) := by
  let z : ℝ → ℝ := fun t => t⁻¹ * nestedLambertEval
    (dyadicLambertDisplacementTruncation N) t
  have hz : Tendsto z atTop (nhds 0) := by
    simpa [z] using dyadicLambertTruncatedPerturbation_tendsto_zero N
  have hzsmall : ∀ᶠ t in atTop, |z t| < (1 / 2 : ℝ) := by
    have hopen : {x : ℝ | |x| < (1 / 2 : ℝ)} ∈ nhds 0 := by
      have hb := Metric.ball_mem_nhds (0 : ℝ)
        (by norm_num : (0 : ℝ) < 1 / 2)
      convert hb using 1
      ext x
      rw [Metric.mem_ball, Real.dist_0_eq_abs]
      rfl
    exact hz.eventually hopen
  have hTaylor :
      (fun t : ℝ => Real.log (1 + z t) - realLogOnePlusTaylor N (z t))
        =O[atTop] (fun t : ℝ => z t ^ (N + 1)) := by
    apply IsBigO.of_bound 2
    filter_upwards [hzsmall] with t ht
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
    have hb := abs_log_one_add_sub_taylor_le N (lt_trans ht (by norm_num))
    calc
      |Real.log (1 + z t) - realLogOnePlusTaylor N (z t)| ≤
          |z t| ^ (N + 1) / (1 - |z t|) := hb
      _ ≤ 2 * |z t| ^ (N + 1) := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [pow_nonneg (abs_nonneg (z t)) (N + 1)]
  have hTaylor' := hTaylor.trans (by
    simpa only [z] using dyadicLambertPerturbation_pow_isBigO N)
  apply hTaylor'.congr'
  · filter_upwards with t
    rw [nestedLambertEval_composedLogTaylor]
  · exact Filter.EventuallyEq.rfl

private noncomputable def dyadicLambertApproximationDefect
    (N : ℕ) (t : ℝ) : ℝ :=
  nestedLambertEval (dyadicLambertDisplacementTruncation N) t -
      Real.log t / Real.log 2 -
    Real.log (1 + t⁻¹ * nestedLambertEval
      (dyadicLambertDisplacementTruncation N) t) / Real.log 2

private theorem nestedLambertEval_algebraicResidual (N : ℕ) (t : ℝ) :
    nestedLambertEval (dyadicLambertAlgebraicResidual N) t =
      nestedLambertEval (dyadicLambertDisplacementTruncation N) t -
        Real.log t / Real.log 2 -
      (Real.log 2)⁻¹ *
        nestedLambertEval (dyadicLambertComposedLogTaylor N) t := by
  unfold dyadicLambertAlgebraicResidual nestedLambertEval
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_C]
  rw [dyadicLambertDisplacementPolynomial_zero]
  simp only [Polynomial.coe_evalRingHom, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  ring

private theorem dyadicLambertApproximationDefect_isBigO (N : ℕ) :
    dyadicLambertApproximationDefect N =O[atTop]
      (fun t : ℝ => t⁻¹ ^ N) := by
  have hAlg := dyadicLambertAlgebraicResidual_isBigO N
  have hTaylor := (dyadicLambertLogTaylorError_isBigO N).const_mul_left
    (Real.log 2)⁻¹
  have h := hAlg.sub hTaylor
  apply h.congr' _ Filter.EventuallyEq.rfl
  filter_upwards with t
  rw [nestedLambertEval_algebraicResidual]
  unfold dyadicLambertApproximationDefect
  ring

private noncomputable def dyadicLambertTruncatedDisplacement
    (N : ℕ) (t : ℝ) : ℝ :=
  nestedLambertEval (dyadicLambertDisplacementTruncation N) t

private noncomputable def dyadicLambertTruncatedPhase
    (N : ℕ) (t : ℝ) : ℝ :=
  t + dyadicLambertTruncatedDisplacement N t

private theorem dyadicLambertTruncatedDisplacement_eq_sum
    (N : ℕ) (t : ℝ) :
    dyadicLambertTruncatedDisplacement N t =
      ∑ n ∈ Finset.range (N + 1),
        dyadicLambertDisplacementCoefficient n (Real.log t) / t ^ n := by
  unfold dyadicLambertTruncatedDisplacement nestedLambertEval
  rw [dyadicLambertDisplacementTruncation,
    PowerSeries.eval₂_trunc_eq_sum_range]
  apply Finset.sum_congr rfl
  intro n hn
  rw [coeff_dyadicLambertDisplacementSeries]
  simp only [Polynomial.coe_evalRingHom]
  unfold dyadicLambertDisplacementCoefficient
  rw [div_eq_mul_inv, inv_pow]

private theorem dyadicLambertPhaseApproximation_eq_truncatedPhase
    (N : ℕ) :
    dyadicLambertPhaseApproximation N = dyadicLambertTruncatedPhase N := by
  funext t
  rw [dyadicLambertPhaseApproximation,
    dyadicLambertTruncatedPhase,
    dyadicLambertTruncatedDisplacement_eq_sum]

private theorem dyadicLambertTruncatedPhase_tendsto_atTop (N : ℕ) :
    Tendsto (dyadicLambertTruncatedPhase N) atTop atTop := by
  have hD : dyadicLambertTruncatedDisplacement N =o[atTop]
      (fun t : ℝ => t) := by
    apply (nestedLambertEval_isLittleO_id
      (dyadicLambertDisplacementTruncation N)).congr_left
    intro t
    rfl
  have heq : dyadicLambertTruncatedPhase N ~[atTop] (fun t : ℝ => t) := by
    have h := (IsEquivalent.refl :
      (fun t : ℝ => t) ~[atTop] (fun t : ℝ => t)).add_isLittleO hD
    apply h.congr_left
    filter_upwards with t
    rfl
  exact heq.tendsto_atTop_iff.mpr tendsto_id

private noncomputable def dyadicLambertFixedPointDefect
    (N : ℕ) (t : ℝ) : ℝ :=
  dyadicLambertTruncatedPhase N t -
      Real.log (dyadicLambertTruncatedPhase N t) / Real.log 2 - t

private theorem dyadicLambertFixedPointDefect_eventuallyEq (N : ℕ) :
    dyadicLambertFixedPointDefect N =ᶠ[atTop]
      dyadicLambertApproximationDefect N := by
  filter_upwards [eventually_gt_atTop (0 : ℝ),
      (dyadicLambertTruncatedPhase_tendsto_atTop N).eventually
        (eventually_gt_atTop (0 : ℝ))] with t ht hA
  let D := dyadicLambertTruncatedDisplacement N t
  have hfactor : 1 + t⁻¹ * D = dyadicLambertTruncatedPhase N t / t := by
    unfold dyadicLambertTruncatedPhase
    dsimp [D]
    field_simp
  have hfactorPos : 0 < 1 + t⁻¹ * D := by
    rw [hfactor]
    positivity
  have hlog : Real.log (dyadicLambertTruncatedPhase N t) =
      Real.log t + Real.log (1 + t⁻¹ * D) := by
    rw [show dyadicLambertTruncatedPhase N t =
        t * (1 + t⁻¹ * D) by
      rw [hfactor]
      field_simp]
    exact Real.log_mul ht.ne' hfactorPos.ne'
  dsimp [D] at hlog
  unfold dyadicLambertFixedPointDefect
  rw [hlog]
  unfold dyadicLambertApproximationDefect
  unfold dyadicLambertTruncatedPhase dyadicLambertTruncatedDisplacement
  ring

private theorem dyadicLambertFixedPointDefect_isBigO (N : ℕ) :
    dyadicLambertFixedPointDefect N =O[atTop]
      (fun t : ℝ => t⁻¹ ^ N) :=
  (dyadicLambertApproximationDefect_isBigO N).congr'
    (dyadicLambertFixedPointDefect_eventuallyEq N).symm
      Filter.EventuallyEq.rfl

/-- **The logarithm is `K⁻¹`-Lipschitz on the ray `[K, ∞)`.**  A quantitative
mean-value bound with no Fabius content: for `a, b ≥ K > 0`,
`|log a - log b| ≤ |a - b| / K`.  The proof needs only `log t ≤ t - 1`, applied
to the ratio of the two arguments, so no derivative appears. -/
theorem abs_log_sub_log_le_div
    {K a b : ℝ} (hK : 0 < K) (ha : K ≤ a) (hb : K ≤ b) :
    |Real.log a - Real.log b| ≤ |a - b| / K := by
  have ha0 : 0 < a := hK.trans_le ha
  have hb0 : 0 < b := hK.trans_le hb
  rcases le_total a b with hab | hba
  · have hlog : Real.log a ≤ Real.log b := Real.log_le_log ha0 hab
    calc
      |Real.log a - Real.log b| = Real.log b - Real.log a := by
        rw [abs_of_nonpos (sub_nonpos.mpr hlog)]
        ring
      _ = Real.log (b / a) := (Real.log_div hb0.ne' ha0.ne').symm
      _ ≤ b / a - 1 := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
      _ = (b - a) / a := by field_simp
      _ ≤ (b - a) / K :=
        div_le_div_of_nonneg_left (sub_nonneg.mpr hab) hK ha
      _ = |a - b| / K := by
        rw [abs_of_nonpos (sub_nonpos.mpr hab)]
        ring
  · have hlog : Real.log b ≤ Real.log a := Real.log_le_log hb0 hba
    calc
      |Real.log a - Real.log b| = Real.log a - Real.log b := by
        rw [abs_of_nonneg (sub_nonneg.mpr hlog)]
      _ = Real.log (a / b) := (Real.log_div ha0.ne' hb0.ne').symm
      _ ≤ a / b - 1 := Real.log_le_sub_one_of_pos (div_pos ha0 hb0)
      _ = (a - b) / b := by field_simp
      _ ≤ (a - b) / K :=
        div_le_div_of_nonneg_left (sub_nonneg.mpr hba) hK hb
      _ = |a - b| / K := by
        rw [abs_of_nonneg (sub_nonneg.mpr hba)]

private theorem truncatedPhase_sub_dyadicLambertPhase_abs_le
    (N : ℕ) {t : ℝ}
    (hsmall : Real.log 2 * (2 : ℝ) ^ (-t) < Real.exp (-1))
    (hA : 2 / Real.log 2 ≤ dyadicLambertTruncatedPhase N t)
    (hlam : 2 / Real.log 2 ≤ dyadicLambertPhase t) :
    |dyadicLambertTruncatedPhase N t - dyadicLambertPhase t| ≤
      2 * |dyadicLambertFixedPointDefect N t| := by
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hK : 0 < 2 / Real.log 2 := div_pos (by norm_num) hL
  have hlog := abs_log_sub_log_le_div hK hA hlam
  have hfixed := dyadicLambertPhase_fixedPoint hsmall
  have hfixed' :
      dyadicLambertPhase t - t - (Real.log 2)⁻¹ *
        Real.log (dyadicLambertPhase t) = 0 := by
    rw [div_eq_mul_inv] at hfixed
    linarith
  have heq :
      dyadicLambertTruncatedPhase N t - dyadicLambertPhase t =
        dyadicLambertFixedPointDefect N t +
          (Real.log (dyadicLambertTruncatedPhase N t) -
            Real.log (dyadicLambertPhase t)) / Real.log 2 := by
    unfold dyadicLambertFixedPointDefect
    rw [div_eq_mul_inv]
    ring_nf at hfixed' ⊢
    linarith
  have htriangle :
      |dyadicLambertTruncatedPhase N t - dyadicLambertPhase t| ≤
        |dyadicLambertFixedPointDefect N t| +
          |Real.log (dyadicLambertTruncatedPhase N t) -
            Real.log (dyadicLambertPhase t)| / Real.log 2 := by
    rw [heq]
    calc
      |dyadicLambertFixedPointDefect N t +
          (Real.log (dyadicLambertTruncatedPhase N t) -
            Real.log (dyadicLambertPhase t)) / Real.log 2| ≤
          |dyadicLambertFixedPointDefect N t| +
            |(Real.log (dyadicLambertTruncatedPhase N t) -
              Real.log (dyadicLambertPhase t)) / Real.log 2| := abs_add_le _ _
      _ = |dyadicLambertFixedPointDefect N t| +
          |Real.log (dyadicLambertTruncatedPhase N t) -
            Real.log (dyadicLambertPhase t)| / Real.log 2 := by
        rw [abs_div, abs_of_pos hL]
  have hscaled :
      |Real.log (dyadicLambertTruncatedPhase N t) -
          Real.log (dyadicLambertPhase t)| / Real.log 2 ≤
        |dyadicLambertTruncatedPhase N t - dyadicLambertPhase t| / 2 := by
    calc
      |Real.log (dyadicLambertTruncatedPhase N t) -
          Real.log (dyadicLambertPhase t)| / Real.log 2 ≤
          (|dyadicLambertTruncatedPhase N t - dyadicLambertPhase t| /
            (2 / Real.log 2)) / Real.log 2 := by
        exact div_le_div_of_nonneg_right hlog hL.le
      _ = |dyadicLambertTruncatedPhase N t - dyadicLambertPhase t| / 2 := by
        field_simp [hL.ne']
  linarith

/-- Arbitrary-order lower-Lambert expansion on the dyadic logarithmic
scale.  The coefficient polynomials are the recursive
`dyadicLambertDisplacementPolynomial`; logarithmic factors in the first
omitted term are absorbed by the displayed `O(t⁻ᴺ)` remainder. -/
theorem dyadicLambertAllOrderRemainder_isBigO (N : ℕ) :
    dyadicLambertAllOrderRemainder N =O[atTop]
      (fun t : ℝ => t⁻¹ ^ N) := by
  have hstability :
      (fun t : ℝ => dyadicLambertTruncatedPhase N t -
        dyadicLambertPhase t) =O[atTop]
          (dyadicLambertFixedPointDefect N) := by
    apply IsBigO.of_bound 2
    filter_upwards [eventually_dyadicLambertPhase_domain,
        (dyadicLambertTruncatedPhase_tendsto_atTop N).eventually
          (eventually_ge_atTop (2 / Real.log 2)),
        tendsto_dyadicLambertPhase_atTop.eventually
          (eventually_ge_atTop (2 / Real.log 2))] with t hsmall hA hlam
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact truncatedPhase_sub_dyadicLambertPhase_abs_le N hsmall hA hlam
  have h := hstability.trans (dyadicLambertFixedPointDefect_isBigO N)
  apply h.neg_left.congr' _ Filter.EventuallyEq.rfl
  filter_upwards with t
  rw [dyadicLambertAllOrderRemainder,
    dyadicLambertPhaseApproximation_eq_truncatedPhase]
  ring

end Fabius
