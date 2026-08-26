import FabiusFunction.FabiusFullAsymptoticExpansion
import FabiusFunction.FabiusInverse
import FabiusFunction.FabiusSharpAsymptotic
import FabiusFunction.QuadraticAsymptoticInversion

/-!
# Sharp endpoint asymptotics of the inverse Fabius function

The corrected forward expansion is most naturally expressed in the exact
lower-Lambert phase `lam`.  At an inverse point `x = fabiusInv F hF y`, put
`T = -log y`.  Boundedness of the periodic correction reduces the forward
formula to

`T = log 2 / 2 * lam ^ 2 - (1 + log 2 / 2) * lam + O(log lam)`.

The reusable theorem `quadratic_asymptotic_inversion` then gives the phase,
including its affine correction and the full `O(log T / sqrt T)` error.  The
exact saddle identity

`log x = log lam - log 2 * lam`

turns that phase estimate into the sharp three-term logarithmic inverse
formula.  Exponentiation gives the explicit equivalent at zero, and the exact
reflection law for `fabiusInv` transports it to one.

The same logarithmic formula places the inverse strictly between every
positive real power of the endpoint argument and every real power of its
logarithmic scale.

Only the phase estimate retains the quantitative error.  The logarithmic and
exponentiated statements use its immediate `o(1)` consequence, which is the
weakest input they need.
-/

set_option autoImplicit false

open Filter Set Asymptotics

namespace Fabius

noncomputable section

/-- The positive-root quadratic main for the lower-Lambert phase at an inverse
point.  With `T = -log y`, `L = log 2`, and `B = 1 + L / 2`, this is
`sqrt (2 * T / L) + B / L`.

The definition is totalized on all real `y`, but the inverse theorem uses it
only as `y -> 0+`, where `T` is positive. -/
noncomputable def fabiusInverseQuadraticPhaseMain (y : ℝ) : ℝ :=
  Real.sqrt (2 * (-Real.log y) / Real.log 2) +
    (1 + Real.log 2 / 2) / Real.log 2

/-- The sharp three-term main for `log (fabiusInv F hF y)` at zero. -/
noncomputable def fabiusInverseLogAsymptoticMain (y : ℝ) : ℝ :=
  -Real.sqrt (2 * Real.log 2 * (-Real.log y)) +
    Real.log (-Real.log y) / 2 - 1 - Real.log (Real.log 2) / 2

/-- The explicit equivalent obtained by exponentiating
`fabiusInverseLogAsymptoticMain`; it is positive on `0 < y < 1`. -/
noncomputable def fabiusInverseAsymptoticMain (y : ℝ) : ℝ :=
  Real.sqrt (-Real.log y) /
      (Real.exp 1 * Real.sqrt (Real.log 2)) *
    Real.exp (-Real.sqrt (2 * Real.log 2 * (-Real.log y)))

private theorem tendsto_fabiusInv_nhdsGT_zero
    (F : BoundedFabius) (hF : IsFabius F) :
    Tendsto (fabiusInv F hF) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · exact ((continuous_fabiusInv F hF).tendsto' 0 0
      (fabiusInv_zero F hF)).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (zero_lt_one : (0 : ℝ) < 1))]
      with y hy0 hy1
    exact (fabiusInv_mem_Ioo F hF ⟨hy0, hy1⟩).1

private theorem tendsto_fabiusLambertPhase_at_zero_right :
    Tendsto fabiusLambertPhase (𝓝[>] (0 : ℝ)) atTop := by
  apply (tendsto_logScale_iff_smallArgument
    fabiusLambertPhase atTop).mp
  simpa only [fabiusLogArgument, fabiusLambertPhase_dyadic] using
    tendsto_dyadicLambertPhase_atTop

private theorem isBounded_range_negativeLaplacePsi :
    Bornology.IsBounded (range negativeLaplacePsi) :=
  negativeLaplacePsi_periodic.isBounded_of_continuous one_ne_zero
    continuous_negativeLaplacePsi

private theorem negativeLaplacePsi_comp_isBigO_one
    {α : Type*} (l : Filter α) (lam : α → ℝ) :
    (fun i => negativeLaplacePsi (lam i)) =O[l]
      (fun _ : α => (1 : ℝ)) := by
  obtain ⟨C, hC⟩ := isBounded_range_negativeLaplacePsi.exists_norm_le
  apply IsBigO.of_bound C
  filter_upwards with i
  simpa only [Real.norm_eq_abs, norm_one, mul_one] using
    hC (negativeLaplacePsi (lam i)) ⟨lam i, rfl⟩

private theorem fabius_inverse_quadratic_input
    (F : BoundedFabius) (hF : IsFabius F) :
    (fun y : ℝ =>
      -Real.log y -
        (Real.log 2 / 2 *
            fabiusLambertPhase (fabiusInv F hF y) ^ 2 -
          (1 + Real.log 2 / 2) *
            fabiusLambertPhase (fabiusInv F hF y)))
      =O[𝓝[>] (0 : ℝ)]
        (fun y : ℝ =>
          Real.log (fabiusLambertPhase (fabiusInv F hF y))) := by
  let l : Filter ℝ := 𝓝[>] (0 : ℝ)
  let lam : ℝ → ℝ := fun y =>
    fabiusLambertPhase (fabiusInv F hF y)
  have hinv := tendsto_fabiusInv_nhdsGT_zero F hF
  have hlam : Tendsto lam l atTop := by
    exact tendsto_fabiusLambertPhase_at_zero_right.comp hinv
  have hforward :=
    (log_fabius_sub_sharpLambertExpansion_isBigO F hF 0).comp_tendsto hinv
  have hbase :
      (fun y : ℝ => Real.log y -
        fabiusSharpLambertMain (fabiusInv F hF y)) =O[l]
          (fun _ : ℝ => (1 : ℝ)) := by
    apply hforward.congr'
    · filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Iio_mem_nhds (zero_lt_one : (0 : ℝ) < 1))]
        with y hy0 hy1
      rw [fabiusReal_fabiusInv F hF ⟨hy0.le, hy1.le⟩]
      simp [fabiusSharpLambertExpansion, fabiusSaddleLogPartialSum]
    · filter_upwards with y
      simp
  have honeLog :
      (fun _ : ℝ => (1 : ℝ)) =O[l] (fun y => Real.log (lam y)) := by
    simpa only [Function.comp_apply] using
      ((Real.isLittleO_const_log_atTop
        (c := (1 : ℝ))).comp_tendsto hlam).isBigO
  have hlogHalf :
      (fun y => (1 / 2 : ℝ) * Real.log (lam y)) =O[l]
        (fun y => Real.log (lam y)) :=
    (isBigO_refl (fun y => Real.log (lam y)) l).const_mul_left (1 / 2)
  have hconstant :
      (fun _ : ℝ => fabiusSharpAsymptoticConstant) =O[l]
        (fun y => Real.log (lam y)) :=
    (isBigO_const_const fabiusSharpAsymptoticConstant one_ne_zero l).trans
      honeLog
  have hperiodic :
      (fun y => negativeLaplacePsi (lam y)) =O[l]
        (fun y => Real.log (lam y)) :=
    (negativeLaplacePsi_comp_isBigO_one l lam).trans honeLog
  have hraw :=
    (((hbase.neg_left.trans honeLog).add hlogHalf).sub hconstant).sub
      hperiodic
  apply hraw.congr_left
  intro y
  unfold fabiusSharpLambertMain
  dsimp [l, lam]
  ring

/-- **Sharp quadratic inversion of the Fabius lower-Lambert phase.**

As `y -> 0+`, the exact phase at the inverse point satisfies

`lam = sqrt (2 * (-log y) / log 2) +
  (1 + log 2 / 2) / log 2 + O(log (-log y) / sqrt (-log y))`.

This is the exact quantitative counterpart of the quadratic inversion lemma
in the research-frontier derivation. -/
theorem
    fabiusLambertPhase_fabiusInv_sub_fabiusInverseQuadraticPhaseMain_isBigO
    (F : BoundedFabius) (hF : IsFabius F) :
    (fun y : ℝ => fabiusLambertPhase (fabiusInv F hF y) -
      fabiusInverseQuadraticPhaseMain y) =O[𝓝[>] (0 : ℝ)]
        (fun y : ℝ =>
          Real.log (-Real.log y) / Real.sqrt (-Real.log y)) := by
  simpa only [fabiusInverseQuadraticPhaseMain] using
    quadratic_asymptotic_inversion
      (T := fun y : ℝ => -Real.log y)
      (lam := fun y : ℝ => fabiusLambertPhase (fabiusInv F hF y))
      (L := Real.log 2) (B := 1 + Real.log 2 / 2)
      (Real.log_pos (by norm_num : (1 : ℝ) < 2))
      (tendsto_fabiusLambertPhase_at_zero_right.comp
        (tendsto_fabiusInv_nhdsGT_zero F hF))
      (fabius_inverse_quadratic_input F hF)

/-- The full-rate phase estimate has vanishing error at the left endpoint. -/
theorem
    tendsto_fabiusLambertPhase_fabiusInv_sub_fabiusInverseQuadraticPhaseMain
    (F : BoundedFabius) (hF : IsFabius F) :
    Tendsto
      (fun y : ℝ => fabiusLambertPhase (fabiusInv F hF y) -
        fabiusInverseQuadraticPhaseMain y)
      (𝓝[>] (0 : ℝ)) (nhds 0) := by
  have hT : Tendsto (fun y : ℝ => -Real.log y)
      (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hrateTop :
      Tendsto (fun T : ℝ => Real.log T / Real.sqrt T)
        atTop (nhds 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop
        (r := (1 / 2 : ℝ)) (by norm_num)).tendsto_div_nhds_zero
  exact
    (fabiusLambertPhase_fabiusInv_sub_fabiusInverseQuadraticPhaseMain_isBigO
      F hF).trans_tendsto (hrateTop.comp hT)

private theorem tendsto_log_sub_half_log_of_sqrt_affine_approximation
    {α : Type*} {l : Filter α} {T lam : α → ℝ} {c a : ℝ}
    (hc : 0 < c)
    (hT : Tendsto T l atTop)
    (happrox :
      Tendsto (fun i => lam i - (Real.sqrt (c * T i) + a)) l (nhds 0)) :
    Tendsto
      (fun i => Real.log (lam i) -
        (Real.log (T i) / 2 + Real.log c / 2))
      l (nhds 0) := by
  have hscaled : Tendsto (fun i => c * T i) l atTop :=
    hT.const_mul_atTop hc
  have hsqrtTop : Tendsto (fun i => Real.sqrt (c * T i)) l atTop :=
    Real.tendsto_sqrt_atTop.comp hscaled
  have hmainTop :
      Tendsto (fun i => Real.sqrt (c * T i) + a) l atTop :=
    tendsto_atTop_add_const_right l a hsqrtTop
  have honeMain :
      (fun _ : α => (1 : ℝ)) =o[l]
        (fun i => Real.sqrt (c * T i) + a) :=
    (isLittleO_one_left_iff ℝ).mpr
      (tendsto_norm_atTop_atTop.comp hmainTop)
  have hlamMain :
      lam ~[l] (fun i => Real.sqrt (c * T i) + a) :=
    ((happrox.isBigO_one ℝ).trans_isLittleO honeMain).isEquivalent
  have hmainSqrt :
      (fun i => Real.sqrt (c * T i) + a) ~[l]
        (fun i => Real.sqrt (c * T i)) :=
    (IsEquivalent.refl
      (u := fun i => Real.sqrt (c * T i))).add_const_of_norm_tendsto_atTop
        (tendsto_norm_atTop_atTop.comp hsqrtTop)
  have hlamSqrt :
      lam ~[l] (fun i => Real.sqrt (c * T i)) :=
    hlamMain.trans hmainSqrt
  have hsqrtPos : ∀ᶠ i in l, 0 < Real.sqrt (c * T i) :=
    hsqrtTop.eventually_gt_atTop 0
  have hlamPos : ∀ᶠ i in l, 0 < lam i :=
    hlamSqrt.eventually_pos hsqrtPos
  have hratio :
      Tendsto (fun i => lam i / Real.sqrt (c * T i)) l (nhds 1) :=
    (isEquivalent_iff_tendsto_one (hsqrtPos.mono fun _ hi => hi.ne')).mp
      hlamSqrt
  have hlogRatio :
      Tendsto (fun i => Real.log (lam i / Real.sqrt (c * T i)))
        l (nhds 0) := by
    simpa using hratio.log one_ne_zero
  apply hlogRatio.congr'
  filter_upwards [hT.eventually_gt_atTop 0, hlamPos] with i hTi hli
  have hsPos : 0 < Real.sqrt (c * T i) :=
    Real.sqrt_pos.2 (mul_pos hc hTi)
  rw [Real.log_div hli.ne' hsPos.ne',
    Real.log_sqrt (mul_nonneg hc.le hTi.le),
    Real.log_mul hc.ne' hTi.ne']
  ring

private theorem log_two_mul_sqrt_two_mul_div_log_two
    (T : ℝ) (hT : 0 ≤ T) :
    Real.log 2 * Real.sqrt (2 * T / Real.log 2) =
      Real.sqrt (2 * Real.log 2 * T) := by
  have hL : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hleftArg : 0 ≤ 2 * T / Real.log 2 :=
    div_nonneg (mul_nonneg (by norm_num) hT) hL.le
  have hrightArg : 0 ≤ 2 * Real.log 2 * T :=
    mul_nonneg (mul_nonneg (by norm_num) hL.le) hT
  have hsquare :
      (Real.log 2 * Real.sqrt (2 * T / Real.log 2)) ^ 2 =
        (Real.sqrt (2 * Real.log 2 * T)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hleftArg, Real.sq_sqrt hrightArg]
    field_simp [hL.ne'] <;> ring
  have hleftNonneg :
      0 ≤ Real.log 2 * Real.sqrt (2 * T / Real.log 2) :=
    mul_nonneg hL.le (Real.sqrt_nonneg _)
  have hrightNonneg : 0 ≤ Real.sqrt (2 * Real.log 2 * T) :=
    Real.sqrt_nonneg _
  nlinarith

/-- **Sharp logarithmic asymptotic of the inverse Fabius function.**

For `T = -log y` and `L = log 2`,

`log (fabiusInv F hF y) =
  -sqrt (2 * L * T) + log T / 2 - 1 - log L / 2 + o(1)`

as `y -> 0+`.  The constant `-1` is the exact cancellation between the
half-logarithm of `2` and the affine phase displacement. -/
theorem tendsto_log_fabiusInv_sub_fabiusInverseLogAsymptoticMain
    (F : BoundedFabius) (hF : IsFabius F) :
    Tendsto
      (fun y : ℝ => Real.log (fabiusInv F hF y) -
        fabiusInverseLogAsymptoticMain y)
      (𝓝[>] (0 : ℝ)) (nhds 0) := by
  let l : Filter ℝ := 𝓝[>] (0 : ℝ)
  have hL : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hT : Tendsto (fun y : ℝ => -Real.log y) l atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hphase :=
    tendsto_fabiusLambertPhase_fabiusInv_sub_fabiusInverseQuadraticPhaseMain
      F hF
  have hlogPhase :=
    tendsto_log_sub_half_log_of_sqrt_affine_approximation
      (T := fun y : ℝ => -Real.log y)
      (lam := fun y : ℝ => fabiusLambertPhase (fabiusInv F hF y))
      (c := 2 / Real.log 2)
      (a := (1 + Real.log 2 / 2) / Real.log 2)
      (div_pos (by norm_num) hL) hT (by
        apply hphase.congr'
        filter_upwards with y
        unfold fabiusInverseQuadraticPhaseMain
        congr 3 <;> ring)
  have hraw := hlogPhase.sub (hphase.const_mul (Real.log 2))
  have hinv := tendsto_fabiusInv_nhdsGT_zero F hF
  have hinvSmall :
      ∀ᶠ y in l,
        Real.log 2 * fabiusInv F hF y < Real.exp (-1) := by
    have hcut : 0 < Real.exp (-1) / Real.log 2 :=
      div_pos (Real.exp_pos _) hL
    have hlt :
        ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), x < Real.exp (-1) / Real.log 2 :=
      nhdsWithin_le_nhds (Iio_mem_nhds hcut)
    filter_upwards [hinv.eventually hlt] with y hy
    have hmul := (lt_div_iff₀ hL).mp hy
    simpa only [mul_comm] using hmul
  simpa only [mul_zero, sub_zero] using hraw.congr' (by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (zero_lt_one : (0 : ℝ) < 1)),
      hinvSmall] with y hy0 hy1 hsmall
    have hxPos : 0 < fabiusInv F hF y :=
      (fabiusInv_mem_Ioo F hF ⟨hy0, hy1⟩).1
    have hTPos : 0 < -Real.log y :=
      neg_pos.mpr (Real.log_neg hy0 hy1)
    rw [log_fabiusLambertArgument hxPos hsmall]
    unfold fabiusInverseQuadraticPhaseMain
      fabiusInverseLogAsymptoticMain
    rw [log_two_mul_sqrt_two_mul_div_log_two _ hTPos.le,
      Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hL.ne']
    field_simp [hL.ne'] <;> ring)

private theorem exp_fabiusInverseLogAsymptoticMain_eq
    {y : ℝ} (hy0 : 0 < y) (hy1 : y < 1) :
    Real.exp (fabiusInverseLogAsymptoticMain y) =
      fabiusInverseAsymptoticMain y := by
  have hT : 0 < -Real.log y := neg_pos.mpr (Real.log_neg hy0 hy1)
  have hL : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hExpT :
      Real.exp (Real.log (-Real.log y) / 2) =
        Real.sqrt (-Real.log y) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hT]
    congr 1
    ring
  have hExpL :
      Real.exp (Real.log (Real.log 2) / 2) =
        Real.sqrt (Real.log 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hL]
    congr 1
    ring
  have hExpNegOne : Real.exp (-1) = (Real.exp 1)⁻¹ := by
    simpa only using Real.exp_neg 1
  have hExpNegL :
      Real.exp (-Real.log (Real.log 2) / 2) =
        (Real.sqrt (Real.log 2))⁻¹ := by
    rw [show -Real.log (Real.log 2) / 2 =
      -(Real.log (Real.log 2) / 2) by ring, Real.exp_neg, hExpL]
  unfold fabiusInverseLogAsymptoticMain fabiusInverseAsymptoticMain
  rw [show
      -Real.sqrt (2 * Real.log 2 * -Real.log y) +
            Real.log (-Real.log y) / 2 - 1 -
          Real.log (Real.log 2) / 2 =
        ((-Real.sqrt (2 * Real.log 2 * -Real.log y) +
            Real.log (-Real.log y) / 2) + (-1)) +
          (-Real.log (Real.log 2) / 2) by ring,
    Real.exp_add, Real.exp_add, Real.exp_add,
    hExpT, hExpNegOne, hExpNegL]
  simp only [div_eq_mul_inv, mul_inv]
  ring

private theorem fabiusInv_isEquivalent_exp_fabiusInverseLogAsymptoticMain
    (F : BoundedFabius) (hF : IsFabius F) :
    (fabiusInv F hF) ~[𝓝[>] (0 : ℝ)]
      (fun y => Real.exp (fabiusInverseLogAsymptoticMain y)) := by
  have hpositive :
      ∀ᶠ y : ℝ in 𝓝[>] (0 : ℝ), 0 < fabiusInv F hF y := by
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with y hy
    exact (fabiusInv_mem_Ioo F hF hy).1
  exact isEquivalent_exp_of_tendsto_log_sub hpositive
    (tendsto_log_fabiusInv_sub_fabiusInverseLogAsymptoticMain F hF)

/-- **Explicit sharp equivalent of the inverse at zero.**

Writing `T = -log y` and `L = log 2`, the inverse is asymptotic to

`sqrt T / (exp 1 * sqrt L) * exp (-sqrt (2 * L * T))`.

The fixed sharp constant and bounded periodic correction from the forward
formula disappear because their induced phase displacement is `o(1)`. -/
theorem fabiusInv_isEquivalent_fabiusInverseAsymptoticMain
    (F : BoundedFabius) (hF : IsFabius F) :
    (fabiusInv F hF) ~[𝓝[>] (0 : ℝ)] fabiusInverseAsymptoticMain := by
  apply (fabiusInv_isEquivalent_exp_fabiusInverseLogAsymptoticMain F hF)
    .trans_eventuallyEq
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with y hy
  exact exp_fabiusInverseLogAsymptoticMain_eq hy.1 hy.2

private theorem sqrt_const_mul_isLittleO_id_atTop
    {c : ℝ} (hc : 0 < c) :
    (fun T : ℝ => Real.sqrt (c * T)) =o[atTop] (fun T => T) := by
  have h :=
    (Asymptotics.isLittleO_pow_pow_atTop_of_lt
      (𝕜 := ℝ) (p := 1) (q := 2) (by norm_num)).comp_tendsto
        (Real.tendsto_sqrt_atTop.comp
          (tendsto_id.const_mul_atTop hc))
  have hscaled :
      (fun T : ℝ => Real.sqrt (c * T)) =o[atTop]
        (fun T => c * T) := by
    apply h.congr'
    · filter_upwards with T
      simp only [Function.comp_apply, pow_one]
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
      simp only [Function.comp_apply]
      rw [Real.sq_sqrt (mul_nonneg hc.le hT)]
  exact hscaled.of_const_mul_right

private theorem tendsto_fabiusInversePowerGap_atTop
    {α : ℝ} (hα : 0 < α) :
    Tendsto
      (fun T : ℝ =>
        α * T - Real.sqrt (2 * Real.log 2 * T) +
          Real.log T / 2 - 1 - Real.log (Real.log 2) / 2)
      atTop atTop := by
  have hc : 0 < 2 * Real.log (2 : ℝ) :=
    mul_pos (by norm_num) (Real.log_pos (by norm_num))
  have hroot :
      (fun T : ℝ => Real.sqrt (2 * Real.log 2 * T)) =o[atTop]
        (fun T => α * T) :=
    (sqrt_const_mul_isLittleO_id_atTop hc).const_mul_right hα.ne'
  have hlogRaw :=
    (Real.isLittleO_log_id_atTop.const_mul_left (1 / 2 : ℝ))
      .const_mul_right hα.ne'
  have hlog :
      (fun T : ℝ => Real.log T / 2) =o[atTop]
        (fun T => α * T) :=
    hlogRaw.congr_left fun T => by ring
  have hconstant :
      (fun _ : ℝ => -1 - Real.log (Real.log 2) / 2) =o[atTop]
        (fun T => α * T) := by
    simpa only [id_eq] using
      (Asymptotics.isLittleO_const_id_atTop
        (-1 - Real.log (Real.log 2) / 2)).const_mul_right hα.ne'
  have hraw :=
    (((IsEquivalent.refl (l := atTop) (u := fun T : ℝ => α * T))
      .sub_isLittleO hroot).add_isLittleO hlog).add_isLittleO hconstant
  have heq :
      (fun T : ℝ =>
        α * T - Real.sqrt (2 * Real.log 2 * T) +
          Real.log T / 2 - 1 - Real.log (Real.log 2) / 2) ~[atTop]
        (fun T => α * T) := by
    apply hraw.congr_left
    filter_upwards with T
    ring
  exact heq.symm.tendsto_atTop (tendsto_id.const_mul_atTop hα)

private theorem tendsto_fabiusInverseLogPowerGap_atTop (r : ℝ) :
    Tendsto
      (fun T : ℝ =>
        Real.sqrt (2 * Real.log 2 * T) +
          (r - 1 / 2) * Real.log T +
          1 + Real.log (Real.log 2) / 2)
      atTop atTop := by
  have hc : 0 < 2 * Real.log (2 : ℝ) :=
    mul_pos (by norm_num) (Real.log_pos (by norm_num))
  have hrootTop :
      Tendsto (fun T : ℝ => Real.sqrt (2 * Real.log 2 * T))
        atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (tendsto_id.const_mul_atTop hc)
  have hlogRoot :
      (fun T : ℝ => Real.log T) =o[atTop]
        (fun T => Real.sqrt (2 * Real.log 2 * T)) := by
    have h :=
      (isLittleO_log_rpow_atTop
        (r := (1 / 2 : ℝ)) (by norm_num)).const_mul_right
          (Real.sqrt_pos.2 hc).ne'
    exact h.congr_right fun T => by
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_mul hc.le]
  have hlog :
      (fun T : ℝ => (r - 1 / 2) * Real.log T) =o[atTop]
        (fun T => Real.sqrt (2 * Real.log 2 * T)) :=
    hlogRoot.const_mul_left (r - 1 / 2)
  have hconstant :
      (fun _ : ℝ => 1 + Real.log (Real.log 2) / 2) =o[atTop]
        (fun T => Real.sqrt (2 * Real.log 2 * T)) := by
    simpa only [Function.comp_apply, id_eq] using
      (Asymptotics.isLittleO_const_id_atTop
        (1 + Real.log (Real.log 2) / 2)).comp_tendsto hrootTop
  have hraw :=
    ((IsEquivalent.refl
      (u := fun T : ℝ => Real.sqrt (2 * Real.log 2 * T)))
        .add_isLittleO hlog).add_isLittleO hconstant
  have heq :
      (fun T : ℝ =>
        Real.sqrt (2 * Real.log 2 * T) +
          (r - 1 / 2) * Real.log T +
          1 + Real.log (Real.log 2) / 2) ~[atTop]
        (fun T => Real.sqrt (2 * Real.log 2 * T)) := by
    apply hraw.congr_left
    filter_upwards with T
    ring
  exact heq.symm.tendsto_atTop hrootTop

/-! ## Complete hierarchy of elementary inverse scales -/

/-- Every positive real power of the endpoint argument is negligible beside
the inverse Fabius function at zero:

`y ^ α = o(fabiusInv F hF y)` for every `α > 0` as `y -> 0+`. -/
theorem rpow_isLittleO_fabiusInv_at_zero_right
    (F : BoundedFabius) (hF : IsFabius F)
    {α : ℝ} (hα : 0 < α) :
    (fun y : ℝ => y ^ α) =o[𝓝[>] (0 : ℝ)] fabiusInv F hF := by
  let l : Filter ℝ := 𝓝[>] (0 : ℝ)
  have hT : Tendsto (fun y : ℝ => -Real.log y) l atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hgap :
      Tendsto
        (fun y : ℝ =>
          fabiusInverseLogAsymptoticMain y - Real.log y * α)
        l atTop := by
    apply (tendsto_fabiusInversePowerGap_atTop hα).comp hT |>.congr'
    filter_upwards with y
    unfold fabiusInverseLogAsymptoticMain
    ring
  have hexp :
      (fun y : ℝ => Real.exp (Real.log y * α)) =o[l]
        (fun y => Real.exp (fabiusInverseLogAsymptoticMain y)) :=
    Real.isLittleO_exp_comp_exp_comp.mpr hgap
  have hpowExp :
      (fun y : ℝ => y ^ α) =o[l]
        (fun y => Real.exp (fabiusInverseLogAsymptoticMain y)) := by
    apply hexp.congr'
    · filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with y hy
      rw [Real.rpow_def_of_pos hy.1]
    · exact Filter.EventuallyEq.rfl
  exact hpowExp.trans_isEquivalent
    (fabiusInv_isEquivalent_exp_fabiusInverseLogAsymptoticMain F hF).symm

/-- The inverse Fabius function is negligible beside every real power of its
endpoint logarithmic scale:

`fabiusInv F hF y = o((-log y) ^ r)` for every `r : ℝ` as `y -> 0+`.

Taking `r = -m` gives the negative-logarithmic-power half of the canonical
inverse scale hierarchy for every `m > 0`. -/
theorem fabiusInv_isLittleO_negLog_rpow_at_zero_right
    (F : BoundedFabius) (hF : IsFabius F) (r : ℝ) :
    (fabiusInv F hF) =o[𝓝[>] (0 : ℝ)]
      (fun y : ℝ => (-Real.log y) ^ r) := by
  let l : Filter ℝ := 𝓝[>] (0 : ℝ)
  have hT : Tendsto (fun y : ℝ => -Real.log y) l atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hgap :
      Tendsto
        (fun y : ℝ => Real.log (-Real.log y) * r -
          fabiusInverseLogAsymptoticMain y)
        l atTop := by
    apply (tendsto_fabiusInverseLogPowerGap_atTop r).comp hT |>.congr'
    filter_upwards with y
    unfold fabiusInverseLogAsymptoticMain
    ring
  have hexp :
      (fun y : ℝ => Real.exp (fabiusInverseLogAsymptoticMain y)) =o[l]
        (fun y => Real.exp (Real.log (-Real.log y) * r)) :=
    Real.isLittleO_exp_comp_exp_comp.mpr hgap
  have hinvExp :=
    (fabiusInv_isEquivalent_exp_fabiusInverseLogAsymptoticMain F hF)
      .trans_isLittleO hexp
  apply hinvExp.congr'
  · exact Filter.EventuallyEq.rfl
  · filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with y hy
    have hTPos : 0 < -Real.log y :=
      neg_pos.mpr (Real.log_neg hy.1 hy.2)
    rw [Real.rpow_def_of_pos hTPos]

private theorem tendsto_one_sub_nhdsLT_one_nhdsGT_zero :
    Tendsto (fun y : ℝ => 1 - y) (𝓝[<] (1 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hcontinuous : Continuous (fun y : ℝ => 1 - y) := by fun_prop
    have hat : Tendsto (fun y : ℝ => 1 - y) (nhds (1 : ℝ))
        (nhds (1 - (1 : ℝ))) := hcontinuous.continuousAt
    have hat' : Tendsto (fun y : ℝ => 1 - y) (nhds (1 : ℝ)) (nhds 0) := by
      simpa only [sub_self] using hat
    exact hat'.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact sub_pos.mpr hy

/-- **Reflected sharp equivalent at the right endpoint.**

As `y -> 1-`, the distance of the inverse from one is asymptotic to the same
left-endpoint main evaluated at `1 - y`. -/
theorem one_sub_fabiusInv_isEquivalent_fabiusInverseAsymptoticMain_one_sub
    (F : BoundedFabius) (hF : IsFabius F) :
    (fun y : ℝ => 1 - fabiusInv F hF y) ~[𝓝[<] (1 : ℝ)]
      (fun y : ℝ => fabiusInverseAsymptoticMain (1 - y)) := by
  have h := (fabiusInv_isEquivalent_fabiusInverseAsymptoticMain F hF).comp_tendsto
    tendsto_one_sub_nhdsLT_one_nhdsGT_zero
  apply h.congr_left
  filter_upwards with y
  exact fabiusInv_one_sub F hF y

end

end Fabius
