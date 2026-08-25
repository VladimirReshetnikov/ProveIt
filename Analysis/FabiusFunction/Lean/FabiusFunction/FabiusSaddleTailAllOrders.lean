import FabiusFunction.FabiusSaddleTail

/-!
# All-order complementary tails for the Fabius saddle kernel

`FabiusSaddleTail` bounds the normalized saddle-kernel integral outside the
standard window `|v| ≤ √(32 log b)` by `O(1/b)`.  One inverse power is not
enough for a Poincaré expansion, in which the discarded contour must be flat
against every retained coefficient.  This module widens the window in
proportion to the requested order,

`A_N(b) = √(32 (N+1) log b)`,

and shows that the omitted contour is then `O(b⁻¹ ^ (N+1))` for each fixed
`N`.

The two-region splitting of the parent module is reused unchanged.  In the
intermediate region the enlarged radius turns `exp (-(mA/(2b)) A)` into
`b⁻¹ ^ (4 (N+1))` once `b/4 ≤ m`, four times the decay actually asked for;
in the far region the geometric weight `2⁻⁽ᵐ⁻¹⁾ √b π` is majorized by
`2 π b exp (-(log 2 / 4) b)`, and exponential decay beats every fixed
inverse power.

## Main results

* `fabiusSaddleCentralRadiusOrder`, with `fabiusSaddleCentralRadiusOrder_pos`,
  `sq_fabiusSaddleCentralRadiusOrder` and
  `one_le_fabiusSaddleCentralRadiusOrder` — the order-dependent radius.  This
  definition is the module's most widely used export: it fixes the common
  window of `FabiusSaddleCentralRadiusAsymptotics`,
  `GaussianPolynomialTailAllOrders` and `FabiusSaddleMassAllOrders`.
* `ordered_intermediate_tail_le_inv_pow` — intermediate region, explicit
  bound `16 * b⁻¹ ^ (N+1)`, for any `1 ≤ b` and any radius `1 ≤ A` with
  `A² = 32 (N+1) log b`.
* `geometric_tail_isBigO_inv_pow` — far region, along an arbitrary filter on
  which `b → atTop` and `b/4 ≤ m`.
* `integral_norm_fabius_scaledSaddleKernel_orderRadius_isBigO` — the export
  consumed by `FabiusSaddleMassAllOrders`.

`N` is fixed throughout; no statement here is uniform in `N`.  The standing
hypotheses match the parent module: `0 < r` eventually, `b → atTop`, at least
`2m ≥ b/2` extracted dyadic Laplace factors (written `b/4 ≤ m`), and a
minor-arc constant `negativeLaplaceMinorArcConstant r (2m)` that is `O(1)`.
The constant `16` and the fourfold exponent slack are sufficient, not sharp.
-/

set_option autoImplicit false

open Filter Set MeasureTheory Asymptotics
open scoped Topology

namespace Fabius

/-- Order-dependent central radius.  The factor `N+1` makes the Gaussian
tail smaller than the requested `b^(-(N+1))` rate. -/
noncomputable def fabiusSaddleCentralRadiusOrder (N : ℕ) (b : ℝ) : ℝ :=
  Real.sqrt (32 * (N + 1 : ℝ) * Real.log b)

lemma fabiusSaddleCentralRadiusOrder_pos (N : ℕ) {b : ℝ} (hb : 1 < b) :
    0 < fabiusSaddleCentralRadiusOrder N b := by
  unfold fabiusSaddleCentralRadiusOrder
  exact Real.sqrt_pos.2 (mul_pos
    (mul_pos (by norm_num) (by positivity)) (Real.log_pos hb))

lemma sq_fabiusSaddleCentralRadiusOrder (N : ℕ) {b : ℝ} (hb : 1 ≤ b) :
    fabiusSaddleCentralRadiusOrder N b ^ 2 =
      32 * (N + 1 : ℝ) * Real.log b := by
  unfold fabiusSaddleCentralRadiusOrder
  rw [Real.sq_sqrt]
  exact mul_nonneg (mul_nonneg (by norm_num) (by positivity))
    (Real.log_nonneg hb)

lemma one_le_fabiusSaddleCentralRadiusOrder
    (N : ℕ) {b : ℝ} (hb : Real.exp 1 ≤ b) :
    1 ≤ fabiusSaddleCentralRadiusOrder N b := by
  have hbpos : 0 < b := (Real.exp_pos 1).trans_le hb
  have hlog : 1 ≤ Real.log b :=
    (Real.le_log_iff_exp_le hbpos).2 hb
  unfold fabiusSaddleCentralRadiusOrder
  apply (Real.le_sqrt (by norm_num) (by positivity)).2
  have hN : (1 : ℝ) ≤ N + 1 := by
    exact_mod_cast Nat.le_add_left 1 N
  nlinarith

lemma ordered_intermediate_tail_le_inv_pow
    (N : ℕ) (b A : ℝ) (m : ℕ)
    (hb : 1 ≤ b) (hA : 1 ≤ A)
    (hm : b / 4 ≤ (m : ℝ))
    (hA_sq : A ^ 2 = 32 * (N + 1 : ℝ) * Real.log b) :
    2 * Real.exp (-((m : ℝ) * A / (2 * b)) * A) /
        ((m : ℝ) * A / (2 * b)) ≤
      16 * b⁻¹ ^ (N + 1) := by
  have hbpos : 0 < b := zero_lt_one.trans_le hb
  have hmdiv : (1 / 4 : ℝ) ≤ (m : ℝ) / b := by
    rw [le_div_iff₀ hbpos]
    simpa [div_eq_mul_inv, mul_comm] using hm
  let lam : ℝ := (m : ℝ) * A / (2 * b)
  have hlam_lower : (1 / 8 : ℝ) ≤ lam := by
    dsimp [lam]
    calc
      (1 / 8 : ℝ) = (1 / 4 : ℝ) * 1 / 2 := by ring
      _ ≤ ((m : ℝ) / b) * A / 2 := by gcongr
      _ = (m : ℝ) * A / (2 * b) := by ring
  have hlam : 0 < lam := (by norm_num : (0 : ℝ) < 1 / 8).trans_le hlam_lower
  have hlamA : 4 * (N + 1 : ℝ) * Real.log b ≤ lam * A := by
    dsimp [lam]
    have hfac : 0 ≤ 16 * (N + 1 : ℝ) * Real.log b := by
      exact mul_nonneg (mul_nonneg (by norm_num) (by positivity))
        (Real.log_nonneg hb)
    have hmul := mul_le_mul_of_nonneg_right hmdiv hfac
    have hlogeq : (N + 1 : ℝ) * Real.log b = A ^ 2 / 32 := by
      nlinarith [hA_sq]
    have hscale : 16 * (N + 1 : ℝ) * Real.log b = A ^ 2 / 2 := by
      nlinarith [hA_sq]
    calc
      4 * (N + 1 : ℝ) * Real.log b =
          16 * (1 / 4 : ℝ) * (N + 1 : ℝ) * Real.log b := by ring
      _ ≤ 16 * ((m : ℝ) / b) * (N + 1 : ℝ) * Real.log b := by
        nlinarith
      _ = ((m : ℝ) / b) * (A ^ 2 / 2) := by
        rw [show 16 * ((m : ℝ) / b) * (N + 1 : ℝ) * Real.log b =
          ((m : ℝ) / b) * (16 * (N + 1 : ℝ) * Real.log b) by ring,
          hscale]
      _ = ((m : ℝ) * A / (2 * b)) * A := by
        field_simp [hbpos.ne']
  have hexp : Real.exp (-(lam * A)) ≤ b⁻¹ ^ (4 * (N + 1)) := by
    calc
      Real.exp (-(lam * A)) ≤
          Real.exp (-(4 * (N + 1 : ℝ) * Real.log b)) :=
        Real.exp_le_exp.mpr (neg_le_neg hlamA)
      _ = b⁻¹ ^ (4 * (N + 1)) := by
        rw [show 4 * (N + 1 : ℝ) = ((4 * (N + 1) : ℕ) : ℝ) by
          push_cast; ring]
        rw [show -((4 * (N + 1) : ℕ) * Real.log b) =
          -((4 * (N + 1) : ℕ) * Real.log b) by rfl,
          Real.exp_neg, Real.exp_nat_mul, Real.exp_log hbpos, inv_pow]
  have hcoeff : 2 / lam ≤ 16 := by
    rw [div_le_iff₀ hlam]
    nlinarith
  have hinv0 : 0 ≤ b⁻¹ := by positivity
  have hinv1 : b⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hb
  have hpow : b⁻¹ ^ (4 * (N + 1)) ≤ b⁻¹ ^ (N + 1) := by
    exact pow_le_pow_of_le_one hinv0 hinv1 (by omega)
  calc
    2 * Real.exp (-((m : ℝ) * A / (2 * b)) * A) /
        ((m : ℝ) * A / (2 * b)) =
        (2 / lam) * Real.exp (-(lam * A)) := by
      dsimp [lam]
      ring_nf
    _ ≤ 16 * b⁻¹ ^ (4 * (N + 1)) :=
      mul_le_mul hcoeff hexp (Real.exp_nonneg _) (by norm_num)
    _ ≤ 16 * b⁻¹ ^ (N + 1) :=
      mul_le_mul_of_nonneg_left hpow (by norm_num)

private lemma geometric_majorant_isBigO_inv_pow (N : ℕ) :
    (fun b : ℝ => 2 * Real.pi * b *
      Real.exp (-(Real.log 2 / 4) * b)) =O[atTop]
        (fun b : ℝ => b⁻¹ ^ (N + 1)) := by
  have hc : 0 < Real.log 2 / 4 := by positivity
  have hexp := (isLittleO_exp_neg_mul_rpow_atTop hc
    (-(N + 2 : ℝ))).isBigO
  have hmul := (isBigO_refl (fun b : ℝ => b) atTop).mul hexp
  have hscaled := hmul.const_mul_left (2 * Real.pi)
  apply hscaled.congr' (Filter.Eventually.of_forall fun b => by ring) ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with b hb
  rw [Real.rpow_neg (le_of_lt hb)]
  have hcast : (N : ℝ) + 2 = ((N + 2 : ℕ) : ℝ) := by norm_num
  rw [hcast, Real.rpow_natCast]
  rw [inv_pow]
  rw [show N + 2 = (N + 1) + 1 by omega, pow_succ]
  field_simp [hb.ne']

lemma geometric_tail_isBigO_inv_pow
    {α : Type*} (l : Filter α) (N : ℕ)
    (b : α → ℝ) (m : α → ℕ)
    (hb : Tendsto b l atTop)
    (hm : ∀ᶠ i in l, b i / 4 ≤ (m i : ℝ)) :
    (fun i => ((2 : ℝ) ^ (m i - 1))⁻¹ *
      (Real.sqrt (b i) * Real.pi)) =O[l]
        (fun i => (b i)⁻¹ ^ (N + 1)) := by
  have hmajorComp :
      (fun i => 2 * Real.pi * b i *
        Real.exp (-(Real.log 2 / 4) * b i)) =O[l]
          (fun i => (b i)⁻¹ ^ (N + 1)) := by
    simpa [Function.comp_def] using
      (geometric_majorant_isBigO_inv_pow N).comp_tendsto hb
  apply (IsBigO.of_bound 1 ?_).trans hmajorComp
  filter_upwards [hb.eventually_ge_atTop (1 : ℝ), hm] with i hbi hmi
  have hbpos : 0 < b i := zero_lt_one.trans_le hbi
  have hmR : 0 < (m i : ℝ) := by linarith
  have hm1 : 1 ≤ m i := by exact_mod_cast hmR
  have hsqrt : Real.sqrt (b i) ≤ b i := by
    rw [Real.sqrt_le_iff]
    exact ⟨hbpos.le, by nlinarith⟩
  have hlog : Real.log 2 / 4 * b i ≤ (m i : ℝ) * Real.log 2 := by
    have hL : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
    nlinarith
  have hpowexp : ((2 : ℝ) ^ (m i - 1))⁻¹ ≤
      2 * Real.exp (-(Real.log 2 / 4) * b i) := by
    have hpowid : ((2 : ℝ) ^ (m i - 1))⁻¹ =
        2 * ((2 : ℝ) ^ (m i))⁻¹ := by
      have hp : (2 : ℝ) ^ (m i) = (2 : ℝ) ^ (m i - 1) * 2 := by
        rw [← pow_succ, Nat.sub_add_cancel hm1]
      rw [hp]
      field_simp
    have hident : ((2 : ℝ) ^ (m i))⁻¹ =
        Real.exp (-((m i : ℝ) * Real.log 2)) := by
      rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num)]
    rw [hpowid, hident]
    gcongr
    nlinarith [hlog]
  have hleft0 : 0 ≤ ((2 : ℝ) ^ (m i - 1))⁻¹ *
      (Real.sqrt (b i) * Real.pi) := by positivity
  have hright0 : 0 ≤ 2 * Real.pi * b i *
      Real.exp (-(Real.log 2 / 4) * b i) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hleft0, one_mul,
    Real.norm_eq_abs, abs_of_nonneg hright0]
  calc
    ((2 : ℝ) ^ (m i - 1))⁻¹ * (Real.sqrt (b i) * Real.pi) ≤
        (2 * Real.exp (-(Real.log 2 / 4) * b i)) *
          (b i * Real.pi) := by gcongr
    _ = 2 * Real.pi * b i *
        Real.exp (-(Real.log 2 / 4) * b i) := by ring

/-- At the order-dependent central radius, the complementary part of the
normalized Fabius saddle kernel is smaller than every prescribed inverse
power of the saddle width. -/
theorem integral_norm_fabius_scaledSaddleKernel_orderRadius_isBigO
    {α : Type*} (l : Filter α) (N : ℕ)
    (F : BoundedFabius) (hF : IsFabius F)
    (x r b : α → ℝ) (m : α → ℕ)
    (hr : ∀ᶠ i in l, 0 < r i)
    (hb : Tendsto b l atTop)
    (hm : ∀ᶠ i in l, b i / 4 ≤ (m i : ℝ))
    (hminor :
      (fun i => negativeLaplaceMinorArcConstant (r i) (2 * m i)) =O[l]
        (fun _i => (1 : ℝ))) :
    (fun i => ∫ v in
      (Icc (-fabiusSaddleCentralRadiusOrder N (b i))
        (fabiusSaddleCentralRadiusOrder N (b i)))ᶜ,
      ‖QuantitativeSaddle.scaledSaddleKernel
        (fun z => complexGeneratingFunction F (-z))
          (x i) (r i) (b i) v‖) =O[l]
      (fun i => (b i)⁻¹ ^ (N + 1)) := by
  let C : α → ℝ := fun i =>
    negativeLaplaceMinorArcConstant (r i) (2 * m i)
  let invPow : α → ℝ := fun i => (b i)⁻¹ ^ (N + 1)
  let A : α → ℝ := fun i => fabiusSaddleCentralRadiusOrder N (b i)
  let middle : α → ℝ := fun i =>
    2 * Real.exp (-((m i : ℝ) * A i / (2 * b i)) * A i) /
      ((m i : ℝ) * A i / (2 * b i))
  let far : α → ℝ := fun i =>
    ((2 : ℝ) ^ (m i - 1))⁻¹ * (Real.sqrt (b i) * Real.pi)
  let tail : α → ℝ := fun i => ∫ v in (Icc (-A i) (A i))ᶜ,
    ‖QuantitativeSaddle.scaledSaddleKernel
      (fun z => complexGeneratingFunction F (-z))
        (x i) (r i) (b i) v‖
  have hbexp : ∀ᶠ i in l, Real.exp 1 ≤ b i := hb.eventually_ge_atTop _
  have hb1 : ∀ᶠ i in l, (1 : ℝ) ≤ b i :=
    hb.eventually_ge_atTop _
  have hmiddle : middle =O[l] invPow := by
    apply IsBigO.of_bound 16
    filter_upwards [hbexp, hb1, hm] with i hbie hbi hmi
    have hAi : 1 ≤ A i := by
      dsimp [A]
      exact one_le_fabiusSaddleCentralRadiusOrder N hbie
    have hmiddle0 : 0 ≤ middle i := by
      dsimp [middle]
      have hmpos : 0 < (m i : ℝ) := by linarith
      have hbpos : 0 < b i := zero_lt_one.trans_le hbi
      positivity
    have hinv0 : 0 ≤ invPow i := by
      dsimp [invPow]
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hmiddle0,
      Real.norm_eq_abs, abs_of_nonneg hinv0]
    dsimp [middle, invPow]
    exact ordered_intermediate_tail_le_inv_pow N (b i) (A i) (m i)
      hbi hAi hmi (by
        dsimp [A]
        exact sq_fabiusSaddleCentralRadiusOrder N hbi)
  have hfar : far =O[l] invPow := by
    simpa only [far, invPow] using geometric_tail_isBigO_inv_pow l N b m hb hm
  have hbracket : (fun i => middle i + far i) =O[l] invPow :=
    hmiddle.add hfar
  have htailDom : tail =O[l] (fun i => C i * (middle i + far i)) := by
    apply IsBigO.of_bound 1
    filter_upwards [hr, hbexp, hb1, hm] with i hri hbie hbi hmi
    have hbpos : 0 < b i := zero_lt_one.trans_le hbi
    have hApos : 0 < A i := by
      dsimp [A]
      exact fabiusSaddleCentralRadiusOrder_pos N
        ((Real.one_lt_exp_iff.2 zero_lt_one).trans_le hbie)
    have hmposR : 0 < (m i : ℝ) := by linarith
    have hmone : 1 ≤ m i := by exact_mod_cast hmposR
    have hraw := integral_norm_fabius_scaledSaddleKernel_compl_Icc_le
      F hF (x i) (r i) (b i) (A i) (m i) hri hbpos hApos hmone
    have htail0 : 0 ≤ tail i := by
      dsimp [tail]
      apply integral_nonneg_of_ae
      filter_upwards with v
      exact norm_nonneg _
    have hC0 : 0 ≤ C i := by
      dsimp [C]
      exact (negativeLaplaceMinorArcConstant_pos (r i) hri (2 * m i)).le
    have hmiddle0 : 0 ≤ middle i := by
      dsimp [middle]
      positivity
    have hfar0 : 0 ≤ far i := by
      dsimp [far]
      positivity
    have hright0 : 0 ≤ C i * (middle i + far i) :=
      mul_nonneg hC0 (add_nonneg hmiddle0 hfar0)
    rw [Real.norm_eq_abs, abs_of_nonneg htail0, one_mul,
      Real.norm_eq_abs, abs_of_nonneg hright0]
    simpa only [tail, C, middle, far, A] using hraw
  have hproduct : (fun i => C i * (middle i + far i)) =O[l] invPow := by
    have hC : C =O[l] (fun _i => (1 : ℝ)) := by
      simpa only [C] using hminor
    simpa only [one_mul] using hC.mul hbracket
  have hresult := htailDom.trans hproduct
  simpa only [tail, A, invPow] using hresult

end Fabius
