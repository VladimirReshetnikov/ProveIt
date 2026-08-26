import FabiusFunction.FabiusSaddleCoefficientRecurrence

/-!
# Smoothness of the negative-Laplace periodic correction to all orders

This module upgrades the four-derivative API in `PeriodicRegularity` to
`C∞`.  The `(k+1)`st derivative of a forward logarithmic summand is encoded
by a recursively generated polynomial in `z = exp (-s 2^n)`.  On every
positive half-line these polynomials give a summable superexponential
majorant, so every derivative of the forward tail may be taken termwise.  The
first three quotient polynomials are evaluated explicitly, identifying the
unified second through fourth derivatives with the formulas from
`PeriodicRegularity`.

The resulting smoothness of the exact correction and its centered
normalization is then propagated through the concrete saddle-jet recurrence.
Thus every periodic jet, and every bounded exponent jet, is smooth,
one-periodic, and globally bounded.  The termwise forward-tail sequence is
identified with the ordinary iterated derivatives on `(0, ∞)`, and generic
lemmas propagate smooth periodicity to every iterated derivative.  Specialized
corollaries give continuous, one-periodic, globally bounded derivatives of
all orders for both the exact correction and its centered normalization.
-/

set_option autoImplicit false

open scoped BigOperators ContDiff Topology
open Set Filter Polynomial

namespace Fabius

/-- The polynomial quotient controlling the `(k+1)`st derivative of a
forward logarithmic term. -/
noncomputable def forwardDerivativeQuotientPolynomial : ℕ → Polynomial ℝ
  | 0 => 1
  | k + 1 =>
      -((1 - X) * (forwardDerivativeQuotientPolynomial k +
          X * (forwardDerivativeQuotientPolynomial k).derivative) +
        C (k + 1 : ℝ) * X * forwardDerivativeQuotientPolynomial k)

/-- Unified derivative sequence for one forward-tail summand. -/
noncomputable def negativeLaplaceForwardTermDeriv : ℕ → ℝ → ℕ → ℝ
  | 0 => negativeLaplaceForwardTerm
  | k + 1 => fun s n =>
      let a := (2 : ℝ) ^ n
      let z := Real.exp (-(s * a))
      a ^ (k + 1) * z *
          (forwardDerivativeQuotientPolynomial k).eval z /
        (1 - z) ^ (k + 1)

@[simp] lemma negativeLaplaceForwardTermDeriv_zero :
    negativeLaplaceForwardTermDeriv 0 = negativeLaplaceForwardTerm := by
  rfl

lemma negativeLaplaceForwardTermDeriv_succ (k : ℕ) (s : ℝ) (n : ℕ) :
    negativeLaplaceForwardTermDeriv (k + 1) s n =
      let a := (2 : ℝ) ^ n
      let z := Real.exp (-(s * a))
      a ^ (k + 1) * z *
          (forwardDerivativeQuotientPolynomial k).eval z /
        (1 - z) ^ (k + 1) := by
  rfl

@[simp] lemma negativeLaplaceForwardTermDeriv_one (s : ℝ) (n : ℕ) :
    negativeLaplaceForwardTermDeriv 1 s n =
      negativeLaplaceForwardTermFirst s n := by
  rw [show 1 = 0 + 1 by omega,
    negativeLaplaceForwardTermDeriv_succ]
  simp [forwardDerivativeQuotientPolynomial,
    negativeLaplaceForwardTermFirst]

/-- The first recursively generated forward-derivative quotient polynomial. -/
@[simp] theorem forwardDerivativeQuotientPolynomial_one :
    forwardDerivativeQuotientPolynomial 1 = -1 := by
  apply Polynomial.funext
  intro x
  simp [forwardDerivativeQuotientPolynomial]

/-- The second recursively generated forward-derivative quotient polynomial. -/
@[simp] theorem forwardDerivativeQuotientPolynomial_two :
    forwardDerivativeQuotientPolynomial 2 = 1 + X := by
  apply Polynomial.funext
  intro x
  simp [forwardDerivativeQuotientPolynomial]
  ring

/-- The third recursively generated forward-derivative quotient polynomial. -/
@[simp] theorem forwardDerivativeQuotientPolynomial_three :
    forwardDerivativeQuotientPolynomial 3 = -(1 + C 4 * X + X ^ 2) := by
  apply Polynomial.funext
  intro x
  simp [forwardDerivativeQuotientPolynomial]
  ring

/-- The unified second-derivative summand agrees with the explicit one. -/
@[simp] lemma negativeLaplaceForwardTermDeriv_two (s : ℝ) (n : ℕ) :
    negativeLaplaceForwardTermDeriv 2 s n =
      negativeLaplaceForwardTermSecond s n := by
  simp only [negativeLaplaceForwardTermDeriv,
    forwardDerivativeQuotientPolynomial_one, eval_neg, eval_one,
    negativeLaplaceForwardTermSecond]
  all_goals ring

/-- The unified third-derivative summand agrees with the explicit one. -/
@[simp] lemma negativeLaplaceForwardTermDeriv_three (s : ℝ) (n : ℕ) :
    negativeLaplaceForwardTermDeriv 3 s n =
      negativeLaplaceForwardTermThird s n := by
  simp only [negativeLaplaceForwardTermDeriv,
    forwardDerivativeQuotientPolynomial_two, eval_add, eval_one, eval_X,
    negativeLaplaceForwardTermThird]

/-- The unified fourth-derivative summand agrees with the explicit one. -/
@[simp] lemma negativeLaplaceForwardTermDeriv_four (s : ℝ) (n : ℕ) :
    negativeLaplaceForwardTermDeriv 4 s n =
      negativeLaplaceForwardTermFourth s n := by
  simp only [negativeLaplaceForwardTermDeriv,
    forwardDerivativeQuotientPolynomial_three, eval_neg, eval_add,
    eval_mul, eval_one, eval_C, eval_X, eval_pow,
    negativeLaplaceForwardTermFourth]
  all_goals ring

theorem negativeLaplaceForwardTermDeriv_hasDerivAt
    (k : ℕ) (s : ℝ) (hs : 0 < s) (n : ℕ) :
    HasDerivAt (fun x : ℝ => negativeLaplaceForwardTermDeriv k x n)
      (negativeLaplaceForwardTermDeriv (k + 1) s n) s := by
  cases k with
  | zero =>
      have h := negativeLaplaceForwardTerm_hasDerivAt s hs n
      convert h using 1
      · rfl
      · simpa only [zero_add] using negativeLaplaceForwardTermDeriv_one s n
  | succ k =>
      let a := (2 : ℝ) ^ n
      let z := Real.exp (-(s * a))
      let p := forwardDerivativeQuotientPolynomial k
      have hz : HasDerivAt (fun x : ℝ => Real.exp (-(x * a))) (-a * z) s := by
        simpa [a, z] using hasDerivAt_exp_neg_mul_two_pow s n
      have hp : HasDerivAt
          (fun x : ℝ => p.eval (Real.exp (-(x * a))))
          (p.derivative.eval z * (-a * z)) s := by
        exact (p.hasDerivAt z).comp s hz
      have hu := (hasDerivAt_const s (1 : ℝ)).sub hz
      have hune : 1 - z ≠ 0 := sub_ne_zero.mpr (by
        simpa [a, z] using (exp_neg_mul_two_pow_ne_one s hs.ne' n).symm)
      have hnum :=
        (((hz.const_mul (a ^ (k + 1))).mul hp))
      have hbase := hnum.div (hu.pow (k + 1)) (pow_ne_zero _ hune)
      change HasDerivAt
        (fun x : ℝ => a ^ (k + 1) * Real.exp (-(x * a)) *
          p.eval (Real.exp (-(x * a))) /
            (1 - Real.exp (-(x * a))) ^ (k + 1))
        (a ^ (k + 2) * z *
          (forwardDerivativeQuotientPolynomial (k + 1)).eval z /
            (1 - z) ^ (k + 2)) s
      refine (hbase.congr_deriv ?_).congr_of_eventuallyEq ?_
      · simp only [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply]
        rw [show Real.exp (-(s * a)) = z by rfl]
        dsimp [p]
        simp only [forwardDerivativeQuotientPolynomial, eval_neg, eval_add,
          eval_mul, eval_sub, eval_one, eval_X, eval_C,
          Nat.cast_add, Nat.cast_one]
        field_simp [hune]
        ring
      · filter_upwards with x
        rfl

lemma exists_bound_abs_forwardDerivativeQuotientPolynomial (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Icc (0 : ℝ) 1,
      |(forwardDerivativeQuotientPolynomial k).eval z| ≤ C := by
  let p := forwardDerivativeQuotientPolynomial k
  obtain ⟨z, hz, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1))
    p.continuous.abs.continuousOn
  refine ⟨|p.eval z|, abs_nonneg _, ?_⟩
  intro y hy
  exact hmax hy

theorem exists_norm_negativeLaplaceForwardTermDeriv_succ_le
    (a : ℝ) (ha : 0 < a) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, a ≤ s → ∀ n : ℕ,
      ‖negativeLaplaceForwardTermDeriv (k + 1) s n‖ ≤
        C * (((2 : ℝ) ^ n) ^ (k + 1) *
          Real.exp (-(a * (2 : ℝ) ^ n))) := by
  obtain ⟨B, hB0, hB⟩ :=
    exists_bound_abs_forwardDerivativeQuotientPolynomial k
  let d := 1 - Real.exp (-a)
  have hd : 0 < d := by
    dsimp [d]
    rw [sub_pos, ← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  refine ⟨B / d ^ (k + 1), div_nonneg hB0 (pow_nonneg hd.le _), ?_⟩
  intro s has n
  have hs : 0 < s := ha.trans_le has
  let A := (2 : ℝ) ^ n
  let z := Real.exp (-(s * A))
  let za := Real.exp (-(a * A))
  have hA : 0 < A := by dsimp [A]; positivity
  have hA1 : 1 ≤ A := by
    dsimp [A]
    exact one_le_pow₀ (by norm_num)
  have hz0 : 0 ≤ z := by dsimp [z]; positivity
  have hz1 : z ≤ 1 := by
    dsimp [z]
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (neg_nonpos.mpr (mul_nonneg hs.le hA.le))
  have hzza : z ≤ za := by
    simpa [A, z, za] using exp_neg_mul_two_pow_le_of_le has n
  have hpoly : |(forwardDerivativeQuotientPolynomial k).eval z| ≤ B :=
    hB z ⟨hz0, hz1⟩
  have hden : d ≤ 1 - z := by
    have hza : za ≤ Real.exp (-a) := by
      dsimp [za]
      apply Real.exp_le_exp.mpr
      nlinarith
    dsimp [d]
    exact sub_le_sub_left (hzza.trans hza) 1
  have hdenz : 0 < 1 - z := by
    dsimp [z, A]
    exact one_sub_exp_neg_mul_two_pow_pos s hs n
  rw [negativeLaplaceForwardTermDeriv_succ]
  dsimp only
  change ‖A ^ (k + 1) * z *
      (forwardDerivativeQuotientPolynomial k).eval z /
        (1 - z) ^ (k + 1)‖ ≤ _
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul,
    abs_of_pos (pow_pos hA _), abs_of_nonneg hz0,
    abs_pow, abs_of_pos hdenz]
  calc
    A ^ (k + 1) * z *
          |(forwardDerivativeQuotientPolynomial k).eval z| /
          (1 - z) ^ (k + 1) ≤
        A ^ (k + 1) * za * B / d ^ (k + 1) := by
      apply div_le_div₀
      · positivity
      · gcongr
      · positivity
      · exact pow_le_pow_left₀ hd.le hden _
    _ = (B / d ^ (k + 1)) * (A ^ (k + 1) * za) := by ring

/-- The `k`th derivative tail, defined by termwise differentiation. -/
noncomputable def negativeLaplaceForwardTailDeriv (k : ℕ) (s : ℝ) : ℝ :=
  ∑' n : ℕ, negativeLaplaceForwardTermDeriv k s n

@[simp] lemma negativeLaplaceForwardTailDeriv_zero (s : ℝ) :
    negativeLaplaceForwardTailDeriv 0 s =
      negativeLaplaceForwardTail s := by
  rfl

theorem summable_negativeLaplaceForwardTermDeriv
    (k : ℕ) (s : ℝ) (hs : 0 < s) :
    Summable (negativeLaplaceForwardTermDeriv k s) := by
  cases k with
  | zero =>
      simpa only [negativeLaplaceForwardTermDeriv_zero] using
        summable_negativeLaplaceForwardTerm s hs
  | succ k =>
      obtain ⟨C, _hC0, hC⟩ :=
        exists_norm_negativeLaplaceForwardTermDeriv_succ_le s hs k
      have hmajor :=
        (summable_forward_derivative_majorant s hs (k + 1)).mul_left C
      exact hmajor.of_norm_bounded (hC s le_rfl)

theorem negativeLaplaceForwardTailDeriv_hasDerivAt
    (k : ℕ) (s : ℝ) (hs : 0 < s) :
    HasDerivAt (negativeLaplaceForwardTailDeriv k)
      (negativeLaplaceForwardTailDeriv (k + 1) s) s := by
  let a := s / 2
  have ha : 0 < a := by dsimp [a]; positivity
  obtain ⟨C, _hC0, hC⟩ :=
    exists_norm_negativeLaplaceForwardTermDeriv_succ_le a ha k
  let u : ℕ → ℝ := fun n =>
    C * (((2 : ℝ) ^ n) ^ (k + 1) *
      Real.exp (-(a * (2 : ℝ) ^ n)))
  have hu : Summable u :=
    (summable_forward_derivative_majorant a ha (k + 1)).mul_left C
  change HasDerivAt
    (fun y : ℝ => ∑' n : ℕ, negativeLaplaceForwardTermDeriv k y n)
    (∑' n : ℕ, negativeLaplaceForwardTermDeriv (k + 1) s n) s
  refine hasDerivAt_tsum_of_isPreconnected
    (g := fun (n : ℕ) (y : ℝ) => negativeLaplaceForwardTermDeriv k y n)
    (g' := fun (n : ℕ) (y : ℝ) =>
      negativeLaplaceForwardTermDeriv (k + 1) y n)
    (u := u) (t := Ioi a) (y₀ := s) (y := s)
    hu isOpen_Ioi isPreconnected_Ioi ?_ ?_ ?_ ?_ ?_
  · intro n y hy
    exact negativeLaplaceForwardTermDeriv_hasDerivAt k y (ha.trans hy) n
  · intro n y hy
    exact hC y hy.le n
  · exact show a < s by dsimp [a]; linarith
  · exact summable_negativeLaplaceForwardTermDeriv k s hs
  · exact show a < s by dsimp [a]; linarith

/-- On the positive half-line, the termwise `k`th forward-tail series is
exactly the ordinary `k`th iterated derivative of the forward tail.  The case
`k = 0` is included. -/
theorem iteratedDeriv_negativeLaplaceForwardTail_eq
    (k : ℕ) (s : ℝ) (hs : 0 < s) :
    iteratedDeriv k negativeLaplaceForwardTail s =
      negativeLaplaceForwardTailDeriv k s := by
  induction k generalizing s with
  | zero =>
      change negativeLaplaceForwardTail s =
        negativeLaplaceForwardTailDeriv 0 s
      exact (negativeLaplaceForwardTailDeriv_zero s).symm
  | succ k ih =>
      rw [iteratedDeriv_succ]
      have heq : iteratedDeriv k negativeLaplaceForwardTail =ᶠ[𝓝 s]
          negativeLaplaceForwardTailDeriv k := by
        filter_upwards [isOpen_Ioi.mem_nhds hs] with y hy
        exact ih y hy
      exact ((negativeLaplaceForwardTailDeriv_hasDerivAt k s hs).congr_of_eventuallyEq
        heq).deriv

theorem contDiffOn_negativeLaplaceForwardTailDeriv_nat
    (m k : ℕ) :
    ContDiffOn ℝ m (negativeLaplaceForwardTailDeriv k) (Ioi 0) := by
  induction m generalizing k with
  | zero =>
      change ContDiffOn ℝ (0 : ℕ∞ω)
        (negativeLaplaceForwardTailDeriv k) (Ioi 0)
      rw [contDiffOn_zero]
      intro s hs
      exact (negativeLaplaceForwardTailDeriv_hasDerivAt k s hs).continuousAt.continuousWithinAt
  | succ m ih =>
      rw [show ((m + 1 : ℕ) : ℕ∞ω) = (m : ℕ∞ω) + 1 by simp,
        contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
      refine ⟨?_, by simp, ?_⟩
      · intro s hs
        exact (negativeLaplaceForwardTailDeriv_hasDerivAt k s hs).differentiableAt.differentiableWithinAt
      · exact (ih (k + 1)).congr fun s hs =>
          (negativeLaplaceForwardTailDeriv_hasDerivAt k s hs).deriv

/-- The forward logarithmic tail is smooth to every order on `(0,∞)`. -/
theorem contDiffOn_infty_negativeLaplaceForwardTail :
    ContDiffOn ℝ ∞ negativeLaplaceForwardTail (Ioi 0) := by
  rw [contDiffOn_infty]
  intro m
  have heq : negativeLaplaceForwardTailDeriv 0 =
      negativeLaplaceForwardTail := by
    funext s
    exact negativeLaplaceForwardTailDeriv_zero s
  rw [← heq]
  exact contDiffOn_negativeLaplaceForwardTailDeriv_nat m 0

theorem contDiff_infty_fabiusLaplaceMoment
    (F : BoundedFabius) (hF : IsFabius F) (k : ℕ) :
    ContDiff ℝ ∞ (fabiusLaplaceMoment F k) := by
  rw [contDiff_infty]
  intro n
  exact contDiff_fabiusLaplaceMoment_nat F hF n k

theorem contDiff_infty_negativeLaplaceLog_two_rpow :
    ContDiff ℝ ∞ (fun t : ℝ => negativeLaplaceLog ((2 : ℝ) ^ t)) := by
  let F : BoundedFabius := Existence.boundedCandidate
  have hF : IsFabius F := Existence.boundedCandidate_isFabius
  have hM : ContDiff ℝ ∞ (fabiusLaplaceMoment F 0) :=
    contDiff_infty_fabiusLaplaceMoment F hF 0
  have hpow : ContDiff ℝ ∞ (fun t : ℝ => (2 : ℝ) ^ t) := by
    fun_prop (disch := norm_num)
  have hcomp : ContDiff ℝ ∞
      (fun t : ℝ => fabiusLaplaceMoment F 0 ((2 : ℝ) ^ t)) :=
    hM.comp hpow
  have hlog : ContDiff ℝ ∞
      (fun t : ℝ => Real.log (fabiusLaplaceMoment F 0 ((2 : ℝ) ^ t))) :=
    hcomp.log fun t => (fabiusLaplaceMoment_zero_pos F hF
      (Real.rpow_pos_of_pos (by norm_num) t)).ne'
  have heq : (fun t : ℝ => negativeLaplaceLog ((2 : ℝ) ^ t)) =
      fun t : ℝ => Real.log (fabiusLaplaceMoment F 0 ((2 : ℝ) ^ t)) := by
    funext t
    exact negativeLaplaceLog_eq_log_laplaceMoment F hF
      (Real.rpow_pos_of_pos (by norm_num) t)
  rw [heq]
  exact hlog

theorem contDiff_infty_negativeLaplaceForwardTail_two_rpow :
    ContDiff ℝ ∞
      (fun t : ℝ => negativeLaplaceForwardTail ((2 : ℝ) ^ t)) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  have htail : ContDiffAt ℝ ∞ negativeLaplaceForwardTail ((2 : ℝ) ^ t) :=
    contDiffOn_infty_negativeLaplaceForwardTail.contDiffAt
      (isOpen_Ioi.mem_nhds (Real.rpow_pos_of_pos (by norm_num) t))
  have hpow : ContDiffAt ℝ ∞ (fun u : ℝ => (2 : ℝ) ^ u) t := by
    fun_prop (disch := norm_num)
  exact htail.comp t hpow

/-- The exact one-periodic negative-Laplace correction is `C∞`. -/
theorem contDiff_infty_negativeLaplacePeriodicCorrection :
    ContDiff ℝ ∞ negativeLaplacePeriodicCorrection := by
  have heq : negativeLaplacePeriodicCorrection = fun t : ℝ =>
      negativeLaplaceLog ((2 : ℝ) ^ t) +
        Real.log 2 / 2 * (t ^ 2 - t) +
          negativeLaplaceForwardTail ((2 : ℝ) ^ t) := by
    funext t
    exact negativeLaplacePeriodicCorrection_eq_components t
  rw [heq]
  exact (contDiff_infty_negativeLaplaceLog_two_rpow.add
    (contDiff_const.mul ((contDiff_id.pow 2).sub contDiff_id))).add
      contDiff_infty_negativeLaplaceForwardTail_two_rpow

/-- The zero-mean periodic correction is `C∞`. -/
theorem contDiff_infty_negativeLaplacePsi :
    ContDiff ℝ ∞ negativeLaplacePsi := by
  unfold negativeLaplacePsi
  exact contDiff_infty_negativeLaplacePeriodicCorrection.sub contDiff_const

lemma contDiff_infty_deriv
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (deriv f) := by
  apply ContDiff.deriv'
  simpa using hf

/-- Every iterated derivative of a smooth real function is again smooth. -/
lemma contDiff_infty_iteratedDeriv
    {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv n f) := by
  induction n with
  | zero =>
      change ContDiff ℝ ∞ f
      exact hf
  | succ n ih =>
      have heq : iteratedDeriv (n + 1) f =
          deriv (iteratedDeriv n f) := by
        funext x
        rw [iteratedDeriv_succ]
      rw [heq]
      exact contDiff_infty_deriv ih

lemma periodic_deriv_of_contDiff_infty
    {f : ℝ → ℝ} (hp : Function.Periodic f 1)
    (hf : ContDiff ℝ ∞ f) :
    Function.Periodic (deriv f) 1 := by
  intro t
  have hderiv (u : ℝ) : HasDerivAt f (deriv f u) u :=
    (hf.differentiable (by simp) u).hasDerivAt
  have hshift := (hderiv (t + 1)).comp t
    ((hasDerivAt_id t).add_const 1)
  have heq : f =ᶠ[𝓝 t] f ∘ (fun u : ℝ => id u + 1) :=
    Eventually.of_forall fun u => (hp u).symm
  simpa using (hshift.congr_of_eventuallyEq heq).unique (hderiv t)

/-- Every iterated derivative of a smooth one-periodic real function is
one-periodic, including derivative order zero. -/
lemma periodic_iteratedDeriv_of_contDiff_infty
    {f : ℝ → ℝ} (hp : Function.Periodic f 1)
    (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    Function.Periodic (iteratedDeriv n f) 1 := by
  induction n with
  | zero =>
      change Function.Periodic f 1
      exact hp
  | succ n ih =>
      have heq : iteratedDeriv (n + 1) f =
          deriv (iteratedDeriv n f) := by
        funext x
        rw [iteratedDeriv_succ]
      rw [heq]
      exact periodic_deriv_of_contDiff_infty ih
        (contDiff_infty_iteratedDeriv hf n)

/-- Every iterated derivative of the exact correction is smooth. -/
theorem contDiff_infty_iteratedDeriv_negativeLaplacePeriodicCorrection
    (n : ℕ) :
    ContDiff ℝ ∞
      (iteratedDeriv n negativeLaplacePeriodicCorrection) :=
  contDiff_infty_iteratedDeriv
    contDiff_infty_negativeLaplacePeriodicCorrection n

/-- Every iterated derivative of the exact correction is one-periodic. -/
theorem negativeLaplacePeriodicCorrection_iteratedDeriv_periodic
    (n : ℕ) :
    Function.Periodic
      (iteratedDeriv n negativeLaplacePeriodicCorrection) 1 :=
  periodic_iteratedDeriv_of_contDiff_infty
    negativeLaplacePeriodicCorrection_periodic
    contDiff_infty_negativeLaplacePeriodicCorrection n

/-- Every iterated derivative of the exact correction is continuous. -/
theorem continuous_iteratedDeriv_negativeLaplacePeriodicCorrection
    (n : ℕ) :
    Continuous (iteratedDeriv n negativeLaplacePeriodicCorrection) :=
  (contDiff_infty_iteratedDeriv_negativeLaplacePeriodicCorrection n).continuous

/-- Every iterated derivative of the exact correction has globally bounded
range. -/
theorem isBounded_range_iteratedDeriv_negativeLaplacePeriodicCorrection
    (n : ℕ) :
    Bornology.IsBounded
      (range (iteratedDeriv n negativeLaplacePeriodicCorrection)) :=
  (negativeLaplacePeriodicCorrection_iteratedDeriv_periodic n).isBounded_of_continuous
    one_ne_zero
    (continuous_iteratedDeriv_negativeLaplacePeriodicCorrection n)

/-- Every iterated derivative of the centered correction is smooth. -/
theorem contDiff_infty_iteratedDeriv_negativeLaplacePsi (m : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv m negativeLaplacePsi) :=
  contDiff_infty_iteratedDeriv contDiff_infty_negativeLaplacePsi m

/-- Every iterated derivative of the centered correction is one-periodic. -/
theorem negativeLaplacePsi_iteratedDeriv_periodic (m : ℕ) :
    Function.Periodic (iteratedDeriv m negativeLaplacePsi) 1 :=
  periodic_iteratedDeriv_of_contDiff_infty
    negativeLaplacePsi_periodic contDiff_infty_negativeLaplacePsi m

/-- Every iterated derivative of the centered correction is continuous. -/
theorem continuous_iteratedDeriv_negativeLaplacePsi (n : ℕ) :
    Continuous (iteratedDeriv n negativeLaplacePsi) :=
  (contDiff_infty_iteratedDeriv_negativeLaplacePsi n).continuous

/-- Every iterated derivative of the centered correction has globally
bounded range. -/
theorem isBounded_range_iteratedDeriv_negativeLaplacePsi (n : ℕ) :
    Bornology.IsBounded (range (iteratedDeriv n negativeLaplacePsi)) :=
  (negativeLaplacePsi_iteratedDeriv_periodic n).isBounded_of_continuous
    one_ne_zero (continuous_iteratedDeriv_negativeLaplacePsi n)

/-- Every periodic jet in the concrete saddle recurrence is `C∞`. -/
theorem contDiff_infty_negativeLaplacePeriodicJet (n : ℕ) :
    ContDiff ℝ ∞ (negativeLaplacePeriodicJet n) := by
  induction n with
  | zero =>
      simp only [negativeLaplacePeriodicJet]
      exact contDiff_const.add
        ((contDiff_infty_deriv contDiff_infty_negativeLaplacePsi).div_const _)
  | succ n ih =>
      simp only [negativeLaplacePeriodicJet]
      exact ((contDiff_infty_deriv ih).div_const _).sub
        (contDiff_const.mul ih) |>.add contDiff_const

/-- Every jet in the concrete saddle recurrence is one-periodic. -/
theorem negativeLaplacePeriodicJet_periodic (n : ℕ) :
    Function.Periodic (negativeLaplacePeriodicJet n) 1 := by
  induction n with
  | zero => exact negativeLaplacePeriodicJet_zero_periodic
  | succ n ih =>
      exact negativeLaplacePeriodicJet_succ_periodic n ih
        (periodic_deriv_of_contDiff_infty ih
          (contDiff_infty_negativeLaplacePeriodicJet n))

/-- Every concrete periodic jet has globally bounded range. -/
theorem isBounded_range_negativeLaplacePeriodicJet (n : ℕ) :
    Bornology.IsBounded (range (negativeLaplacePeriodicJet n)) :=
  (negativeLaplacePeriodicJet_periodic n).isBounded_of_continuous one_ne_zero
    (contDiff_infty_negativeLaplacePeriodicJet n).continuous

theorem negativeLaplaceBoundedExponentJet_periodic (n : ℕ) :
    Function.Periodic (negativeLaplaceBoundedExponentJet n) 1 := by
  intro t
  simp only [negativeLaplaceBoundedExponentJet]
  rw [negativeLaplacePeriodicJet_periodic n t]

theorem contDiff_infty_negativeLaplaceBoundedExponentJet (n : ℕ) :
    ContDiff ℝ ∞ (negativeLaplaceBoundedExponentJet n) := by
  unfold negativeLaplaceBoundedExponentJet
  exact (contDiff_infty_negativeLaplacePeriodicJet n).add contDiff_const

theorem isBounded_range_negativeLaplaceBoundedExponentJet (n : ℕ) :
    Bornology.IsBounded (range (negativeLaplaceBoundedExponentJet n)) :=
  (negativeLaplaceBoundedExponentJet_periodic n).isBounded_of_continuous
    one_ne_zero
    (contDiff_infty_negativeLaplaceBoundedExponentJet n).continuous

end Fabius
