/-
# The Mercator logarithm and the existence of the BCH logarithm

This file formalizes Proposition 7.1 (Mercator logarithm) and Corollary 7.2
(existence of the BCH logarithm) of the accompanying article
(`docs/combined`, Section 7.1), which together form the analytic core of
Theorem 7.3(i): in a real or complex unital Banach algebra,

* for `‖U‖ < 1` the Mercator series `log(1 + U) = ∑_{k ≥ 1} (-1)^{k-1} U^k / k`
  converges absolutely, `‖log(1 + U)‖ ≤ -log(1 - ‖U‖)`, and
  `exp(log(1 + U)) = 1 + U`;
* if `s = ‖X‖ + ‖Y‖ < log 2`, then `U = e^X e^Y - 1` satisfies
  `‖U‖ ≤ e^s - 1 < 1`, and `Z = log(1 + U)` satisfies `e^Z = e^X e^Y` and
  `‖Z‖ ≤ -log(2 - e^s)`.

## Method

The identity `exp(log(1 + U)) = 1 + U` is proved by the zero-derivative device
of the other files: with `L(s) = log(1 + sU)`, the function
`h(s) = exp(-L(s)) (1 + sU)` has zero derivative on a disc of radius `> 1`,
because `L'(s)(1 + sU) = U` (a geometric series identity). Two ingredients are
established on the way: termwise differentiation of the Mercator series
(Mathlib's `hasDerivAt_tsum_of_isPreconnected`), and a chain rule for
`s ↦ exp(L(s))` when the values of `L` commute pairwise, obtained from
Mathlib's `HasFDerivAt exp 1 0` and the factorization
`exp(L(s)) = exp(L(t)) exp(L(s) - L(t))`.
-/
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecificLimits.Normed
import BCH.Central

open NormedSpace Filter Topology

namespace BCH

section ChainRule

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

/-- Chain rule for the exponential along a curve whose values commute with the value at
the base point: if `L' = L'(t)` and `L(t)` commutes with every `L(s)`, then
`d/ds exp(L(s)) = exp(L(t)) L'` at `s = t`. -/
theorem hasDerivAt_exp_comp_of_commute {L : 𝕂 → 𝔸} {L' : 𝔸} {t : 𝕂}
    (hL : HasDerivAt L L' t) (hcomm : ∀ s, Commute (L t) (L s)) :
    HasDerivAt (fun s => exp (L s)) (exp (L t) * L') t := by
  let +nondep : NormedAlgebra ℚ 𝔸 := .restrictScalars ℚ 𝕂 𝔸
  have hfact : ∀ s, exp (L s) = exp (L t) * exp (L s - L t) := by
    intro s
    rw [← exp_add_of_commute ((hcomm s).sub_right (Commute.refl _)), add_sub_cancel]
  have hΔ : HasDerivAt (fun s => L s - L t) L' t := hL.sub_const (L t)
  have hE : HasDerivAt (fun s => exp (L s - L t)) L' t := by
    have h0 : HasFDerivAt exp (1 : 𝔸 →L[𝕂] 𝔸) (L t - L t) := by
      rw [sub_self]; exact hasFDerivAt_exp_zero
    have := h0.comp_hasDerivAt t hΔ
    simpa [Function.comp_def] using this
  have h := hE.const_mul (exp (L t))
  exact h.congr_of_eventuallyEq (Eventually.of_forall hfact)

end ChainRule

section Mercator

variable (𝕂 : Type*) {𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]
  [CompleteSpace 𝔸]

/-- The `n`-th term of the Mercator series, `(-1)^n U^(n+1) / (n+1)`. -/
noncomputable def mlogTerm (U : 𝔸) (n : ℕ) : 𝔸 :=
  ((-1 : 𝕂) ^ n * ((n + 1 : ℕ) : 𝕂)⁻¹) • U ^ (n + 1)

/-- The Mercator series `log(1 + U) = ∑_{k ≥ 1} (-1)^{k-1} U^k / k`. -/
noncomputable def mlog (U : 𝔸) : 𝔸 := ∑' n : ℕ, mlogTerm 𝕂 U n

variable {𝕂}

lemma norm_mlogTerm_scalar (n : ℕ) :
    ‖(-1 : 𝕂) ^ n * ((n + 1 : ℕ) : 𝕂)⁻¹‖ = ((n + 1 : ℕ) : ℝ)⁻¹ := by
  rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_inv, RCLike.norm_natCast]

omit [CompleteSpace 𝔸] in
lemma norm_mlogTerm_le (U : 𝔸) (n : ℕ) :
    ‖mlogTerm 𝕂 U n‖ ≤ ((n + 1 : ℕ) : ℝ)⁻¹ * ‖U‖ ^ (n + 1) := by
  rw [mlogTerm, norm_smul, norm_mlogTerm_scalar]
  exact mul_le_mul_of_nonneg_left (norm_pow_le' U n.succ_pos) (by positivity)

omit [CompleteSpace 𝔸] in
lemma norm_mlogTerm_le' (U : 𝔸) (n : ℕ) : ‖mlogTerm 𝕂 U n‖ ≤ ‖U‖ ^ (n + 1) := by
  refine (norm_mlogTerm_le U n).trans ?_
  have h1 : ((n + 1 : ℕ) : ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]; right; exact_mod_cast Nat.succ_pos n
  calc ((n + 1 : ℕ) : ℝ)⁻¹ * ‖U‖ ^ (n + 1) ≤ 1 * ‖U‖ ^ (n + 1) :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = ‖U‖ ^ (n + 1) := one_mul _

omit [CompleteSpace 𝔸] in
lemma summable_pow_succ_of_norm_lt_one {U : 𝔸} (hU : ‖U‖ < 1) :
    Summable fun n : ℕ => ‖U‖ ^ (n + 1) := by
  simpa [pow_succ] using (summable_geometric_of_lt_one (norm_nonneg U) hU).mul_right ‖U‖

/-- Absolute convergence of the Mercator series for `‖U‖ < 1`. -/
lemma summable_mlogTerm {U : 𝔸} (hU : ‖U‖ < 1) : Summable (mlogTerm 𝕂 U) :=
  Summable.of_norm_bounded (summable_pow_succ_of_norm_lt_one hU) (norm_mlogTerm_le' U)

omit [CompleteSpace 𝔸] in
lemma mlogTerm_zero (n : ℕ) : mlogTerm 𝕂 (0 : 𝔸) n = 0 := by
  simp [mlogTerm]

omit [CompleteSpace 𝔸] in
lemma mlog_zero : mlog 𝕂 (0 : 𝔸) = 0 := by
  simp [mlog, mlogTerm_zero]

omit [CompleteSpace 𝔸] in
/-- **Mercator logarithm, norm bound:** `‖log(1 + U)‖ ≤ -log(1 - ‖U‖)` for `‖U‖ < 1`. -/
theorem norm_mlog_le {U : 𝔸} (hU : ‖U‖ < 1) : ‖mlog 𝕂 U‖ ≤ -Real.log (1 - ‖U‖) := by
  have hlog : HasSum (fun n : ℕ => ‖U‖ ^ (n + 1) / (n + 1)) (-Real.log (1 - ‖U‖)) :=
    Real.hasSum_pow_div_log_of_abs_lt_one (by rw [abs_norm]; exact hU)
  have hnorm : Summable fun n => ‖mlogTerm 𝕂 U n‖ :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) (norm_mlogTerm_le' U)
      (summable_pow_succ_of_norm_lt_one hU)
  calc ‖mlog 𝕂 U‖ ≤ ∑' n, ‖mlogTerm 𝕂 U n‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, ‖U‖ ^ (n + 1) / (n + 1) := by
        refine hnorm.tsum_le_tsum (fun n => ?_) hlog.summable
        rw [div_eq_inv_mul]
        exact_mod_cast norm_mlogTerm_le U n
    _ = -Real.log (1 - ‖U‖) := hlog.tsum_eq

omit [CompleteSpace 𝔸] in
/-- Values of the Mercator series at different multiples of `U` commute. -/
lemma commute_mlog_smul (U : 𝔸) (a b : 𝕂) : Commute (mlog 𝕂 (a • U)) (mlog 𝕂 (b • U)) := by
  refine Commute.tsum_left _ fun n => Commute.tsum_right _ fun m => ?_
  simp only [mlogTerm, smul_pow]
  exact (((Commute.refl U).pow_pow (n + 1) (m + 1)).smul_left _).smul_right _
    |>.smul_left _ |>.smul_right _

/-- **Mercator logarithm, main identity:** `exp(log(1 + U)) = 1 + U` for `‖U‖ < 1`. -/
theorem exp_mlog {U : 𝔸} (hU : ‖U‖ < 1) : exp (mlog 𝕂 U) = 1 + U := by
  let +nondep : NormedAlgebra ℚ 𝔸 := .restrictScalars ℚ 𝕂 𝔸
  -- a disc of radius `r > 1` on which `‖s U‖ < 1`
  set r : ℝ := 2 / (1 + ‖U‖) with hr
  have hr1 : 1 < r := by
    rw [hr, lt_div_iff₀ (by positivity)]; linarith
  have hrU : r * ‖U‖ < 1 := by
    rw [hr, div_mul_eq_mul_div, div_lt_one (by positivity)]; linarith
  have hr0 : 0 < r := by linarith
  set B : Set 𝕂 := Metric.ball (0 : 𝕂) r with hB
  have hBopen : IsOpen B := Metric.isOpen_ball
  have hBconn : IsPreconnected B := (convex_ball (0 : 𝕂) r).isPreconnected
  have h0B : (0 : 𝕂) ∈ B := Metric.mem_ball_self hr0
  have h1B : (1 : 𝕂) ∈ B := by
    rw [hB, Metric.mem_ball, dist_zero_right, norm_one]; exact hr1
  have hsU : ∀ s ∈ B, ‖s • U‖ < 1 := by
    intro s hs
    rw [hB, Metric.mem_ball, dist_zero_right] at hs
    rw [norm_smul]
    calc ‖s‖ * ‖U‖ ≤ r * ‖U‖ := mul_le_mul_of_nonneg_right hs.le (norm_nonneg _)
      _ < 1 := hrU
  -- the series `L(s) = log(1 + sU)` written with explicit powers of `s`
  let g : ℕ → 𝕂 → 𝔸 := fun n s => ((-1 : 𝕂) ^ n * ((n + 1 : ℕ) : 𝕂)⁻¹ * s ^ (n + 1)) • U ^ (n + 1)
  let g' : ℕ → 𝕂 → 𝔸 := fun n s => ((-1 : 𝕂) ^ n * s ^ n) • U ^ (n + 1)
  have hg_eq : ∀ n s, g n s = mlogTerm 𝕂 (s • U) n := by
    intro n s
    simp only [g, mlogTerm, smul_pow, smul_smul]
  have hL : ∀ s, mlog 𝕂 (s • U) = ∑' n, g n s := by
    intro s; simp only [mlog, hg_eq]
  have hg : ∀ n s, s ∈ B → HasDerivAt (g n) (g' n s) s := by
    intro n s _
    have h := ((hasDerivAt_pow (n + 1) s).const_mul ((-1 : 𝕂) ^ n * ((n + 1 : ℕ) : 𝕂)⁻¹)).smul_const
      (U ^ (n + 1))
    refine h.congr_deriv ?_
    congr 1
    rw [Nat.add_sub_cancel]
    have hn : ((n + 1 : ℕ) : 𝕂) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
    field_simp
  let u : ℕ → ℝ := fun n => ‖U‖ * (r * ‖U‖) ^ n
  have hu : Summable u :=
    (summable_geometric_of_lt_one (by positivity) hrU).mul_left ‖U‖
  have hg' : ∀ n s, s ∈ B → ‖g' n s‖ ≤ u n := by
    intro n s hs
    rw [hB, Metric.mem_ball, dist_zero_right] at hs
    simp only [g', u, norm_smul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    calc ‖s‖ ^ n * ‖U ^ (n + 1)‖ ≤ r ^ n * ‖U‖ ^ (n + 1) :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hs.le n) (norm_pow_le' U n.succ_pos)
            (norm_nonneg _) (by positivity)
      _ = ‖U‖ * (r * ‖U‖) ^ n := by rw [mul_pow]; ring
  have hg0 : Summable fun n => g n 0 := by
    simp only [g, zero_pow (Nat.succ_ne_zero _), mul_zero, zero_smul]
    exact summable_zero
  have hLderiv : ∀ s ∈ B, HasDerivAt (fun z => ∑' n, g n z) (∑' n, g' n s) s :=
    fun s hs => hasDerivAt_tsum_of_isPreconnected hu hBopen hBconn hg hg' h0B hg0 hs
  -- the derivative satisfies `L'(s) (1 + sU) = U`
  have hD : ∀ s ∈ B, (∑' n, g' n s) * (1 + s • U) = U := by
    intro s hs
    have hx : ‖-(s • U)‖ < 1 := by rw [norm_neg]; exact hsU s hs
    have hgeom : (∑' n : ℕ, (-(s • U)) ^ n) * (1 - -(s • U)) = 1 := geom_series_mul_neg _ hx
    have hterm : ∀ n : ℕ, g' n s = U * (-(s • U)) ^ n := by
      intro n
      simp only [g']
      rw [← neg_smul, smul_pow, mul_smul_comm, ← pow_succ', neg_pow s n]
    have hsum : Summable fun n : ℕ => (-(s • U)) ^ n := summable_geometric_of_norm_lt_one hx
    calc (∑' n, g' n s) * (1 + s • U)
        = (U * ∑' n : ℕ, (-(s • U)) ^ n) * (1 - -(s • U)) := by
          simp only [hterm]
          rw [hsum.tsum_mul_left, sub_neg_eq_add]
      _ = U := by rw [mul_assoc, hgeom, mul_one]
  -- the function `h(s) = exp(-L(s)) (1 + sU)` has zero derivative on `B`
  let h : 𝕂 → 𝔸 := fun s => exp (-(∑' n, g n s)) * (1 + s • U)
  have hcommL : ∀ s s', Commute (-(∑' n, g n s)) (-(∑' n, g n s')) := by
    intro s s'
    have := commute_mlog_smul U s s'
    rw [hL, hL] at this
    exact this.neg_left.neg_right
  have hderiv : ∀ s ∈ B, HasDerivAt h 0 s := by
    intro s hs
    have h1 : HasDerivAt (fun z => -(∑' n, g n z)) (-(∑' n, g' n s)) s := (hLderiv s hs).neg
    have h2 : HasDerivAt (fun z => exp (-(∑' n, g n z)))
        (exp (-(∑' n, g n s)) * -(∑' n, g' n s)) s :=
      hasDerivAt_exp_comp_of_commute h1 (hcommL s)
    have h3 : HasDerivAt (fun z : 𝕂 => 1 + z • U) U s := by
      simpa using ((hasDerivAt_id s).smul_const U).const_add (1 : 𝔸)
    have h4 := h2.mul h3
    refine h4.congr_deriv ?_
    rw [mul_assoc, neg_mul, hD s hs, mul_neg, neg_add_cancel]
  have hdiff : DifferentiableOn 𝕂 h B :=
    fun s hs => (hderiv s hs).differentiableAt.differentiableWithinAt
  have hd0 : B.EqOn (deriv h) 0 := fun s hs => (hderiv s hs).deriv
  have hconst : h 1 = h 0 := hBopen.is_const_of_deriv_eq_zero hBconn hdiff hd0 h1B h0B
  have hh0 : h 0 = 1 := by
    have hsum0 : (∑' n, g n 0) = 0 := by
      simp only [g, zero_pow (Nat.succ_ne_zero _), mul_zero, zero_smul, tsum_zero]
    simp only [h, hsum0, neg_zero, exp_zero, zero_smul, add_zero, mul_one]
  have hh1 : h 1 = exp (-(mlog 𝕂 U)) * (1 + U) := by
    simp only [h, one_smul]
    rw [← hL, one_smul]
  rw [hh1, hh0] at hconst
  calc exp (mlog 𝕂 U) = exp (mlog 𝕂 U) * (exp (-(mlog 𝕂 U)) * (1 + U)) := by
        rw [hconst, mul_one]
    _ = (exp (mlog 𝕂 U) * exp (-(mlog 𝕂 U))) * (1 + U) := by rw [mul_assoc]
    _ = 1 + U := by rw [exp_mul_exp_neg, one_mul]

end Mercator

section RealSeries

/-- The real exponential series without its constant term. -/
lemma hasSum_pow_succ_div_factorial (x : ℝ) :
    HasSum (fun n : ℕ => x ^ (n + 1) / ((n + 1).factorial : ℝ)) (Real.exp x - 1) := by
  have h : HasSum (fun n : ℕ => x ^ n / (n.factorial : ℝ)) (Real.exp x) := by
    have hs := (Real.summable_pow_div_factorial x).hasSum
    rwa [Real.exp_eq_exp_ℝ, exp_eq_tsum_div]
  have := (hasSum_nat_add_iff' 1).mpr h
  simpa using this

end RealSeries

section BCHLog

variable (𝕂 : Type*) {𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸]
  [CompleteSpace 𝔸]

include 𝕂

/-- `‖e^X - 1‖ ≤ e^{‖X‖} - 1`. The scalar field is an explicit argument because it does
not occur in the statement. -/
theorem norm_exp_sub_one_le (X : 𝔸) :
    ‖exp X - 1‖ ≤ Real.exp ‖X‖ - 1 := by
  let +nondep : NormedAlgebra ℚ 𝔸 := .restrictScalars ℚ 𝕂 𝔸
  have hsum : Summable fun n : ℕ => ((n.factorial : 𝕂)⁻¹ : 𝕂) • X ^ n :=
    expSeries_summable' (𝕂 := 𝕂) X
  have hexp : exp X = ∑' n : ℕ, ((n.factorial : 𝕂)⁻¹ : 𝕂) • X ^ n := by
    rw [exp_eq_tsum 𝕂]
  rw [hexp, hsum.tsum_eq_zero_add]
  simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero, one_smul, add_sub_cancel_left]
  refine tsum_of_norm_bounded (hasSum_pow_succ_div_factorial ‖X‖) fun n => ?_
  rw [norm_smul, norm_inv, RCLike.norm_natCast, div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left (norm_pow_le' X n.succ_pos) (by positivity)

/-- `‖e^X e^Y - 1‖ ≤ e^{‖X‖ + ‖Y‖} - 1`. -/
theorem norm_exp_mul_exp_sub_one_le (X Y : 𝔸) :
    ‖exp X * exp Y - 1‖ ≤ Real.exp (‖X‖ + ‖Y‖) - 1 := by
  have hX := norm_exp_sub_one_le 𝕂 X
  have hY := norm_exp_sub_one_le 𝕂 Y
  have hX0 : 0 ≤ Real.exp ‖X‖ - 1 := by linarith [Real.add_one_le_exp ‖X‖, norm_nonneg X]
  have hY0 : 0 ≤ Real.exp ‖Y‖ - 1 := by linarith [Real.add_one_le_exp ‖Y‖, norm_nonneg Y]
  have hid : exp X * exp Y - 1 = (exp X - 1) * (exp Y - 1) + (exp X - 1) + (exp Y - 1) := by
    noncomm_ring
  rw [hid, Real.exp_add]
  calc ‖(exp X - 1) * (exp Y - 1) + (exp X - 1) + (exp Y - 1)‖
      ≤ ‖(exp X - 1) * (exp Y - 1)‖ + ‖exp X - 1‖ + ‖exp Y - 1‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ‖exp X - 1‖ * ‖exp Y - 1‖ + ‖exp X - 1‖ + ‖exp Y - 1‖ :=
        add_le_add (add_le_add (norm_mul_le _ _) le_rfl) le_rfl
    _ ≤ (Real.exp ‖X‖ - 1) * (Real.exp ‖Y‖ - 1) + (Real.exp ‖X‖ - 1) + (Real.exp ‖Y‖ - 1) :=
        add_le_add (add_le_add (mul_le_mul hX hY (norm_nonneg _) hX0) hX) hY
    _ = Real.exp ‖X‖ * Real.exp ‖Y‖ - 1 := by ring

/-- **Existence of the BCH logarithm (Corollary of the Mercator proposition).**
If `‖X‖ + ‖Y‖ < log 2`, then `U = e^X e^Y - 1` has `‖U‖ < 1`, the Mercator logarithm
`Z = log(1 + U)` satisfies `e^Z = e^X e^Y`, and `‖Z‖ ≤ -log(2 - e^{‖X‖ + ‖Y‖})`. -/
theorem exp_mlog_exp_mul_exp {X Y : 𝔸} (hs : ‖X‖ + ‖Y‖ < Real.log 2) :
    ‖exp X * exp Y - 1‖ < 1 ∧
    exp (mlog 𝕂 (exp X * exp Y - 1)) = exp X * exp Y ∧
    ‖mlog 𝕂 (exp X * exp Y - 1)‖ ≤ -Real.log (2 - Real.exp (‖X‖ + ‖Y‖)) := by
  have hUle : ‖exp X * exp Y - 1‖ ≤ Real.exp (‖X‖ + ‖Y‖) - 1 :=
    norm_exp_mul_exp_sub_one_le 𝕂 X Y
  have hexp2 : Real.exp (‖X‖ + ‖Y‖) < 2 := by
    have := Real.exp_lt_exp.mpr hs
    rwa [Real.exp_log (by norm_num)] at this
  have hU1 : ‖exp X * exp Y - 1‖ < 1 := by linarith
  refine ⟨hU1, ?_, ?_⟩
  · rw [exp_mlog hU1, add_sub_cancel]
  · refine (norm_mlog_le hU1).trans ?_
    rw [neg_le_neg_iff]
    exact Real.log_le_log (by linarith) (by linarith)

end BCHLog

end BCH
