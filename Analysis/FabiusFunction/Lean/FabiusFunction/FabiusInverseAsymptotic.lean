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
growth hypothesis after composition with `fabiusInv` comes from the public
small-argument limit in `FabiusLambertRates`.  The exact saddle identity

`log x = log lam - log 2 * lam`

turns that phase estimate into the sharp three-term logarithmic inverse
formula.  Exponentiation gives the explicit equivalent at zero, and the exact
reflection law for `fabiusInv` transports it to one.

The same logarithmic formula places the inverse strictly between every
positive real power of the endpoint argument and every real power of its
logarithmic scale.

The phase estimate and the logarithmic formula both carry the quantitative
`O(log T / sqrt T)` error
(`log_fabiusInv_sub_fabiusInverseLogAsymptoticMain_isBigO`); the
exponentiated statements use its immediate `o(1)` consequence, which is the
weakest input they need.
-/

set_option autoImplicit false

open Filter Set Asymptotics
open scoped Topology

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

/-- **Full sharp expansion pulled back to inverse coordinates.**

As `y -> 0+`, the logarithmic defect of the sharp Lambert main at the exact
inverse point has the full Poincaré expansion inherited from the forward
Fabius function.  Its scale and coefficients remain evaluated at the exact
phase `fabiusLambertPhase (fabiusInv F hF y)`; this theorem is an implicit
inverse-coordinate expansion, not an explicit all-orders reversion of that
phase. -/
theorem log_sub_sharpLambertMain_comp_fabiusInv_hasAsymptoticExpansion
    (F : BoundedFabius) (hF : IsFabius F) :
    SaddleExpansion.HasAsymptoticExpansion (𝓝[>] (0 : ℝ))
      (fun y : ℝ =>
        (fabiusLambertPhase (fabiusInv F hF y))⁻¹)
      (fun y : ℝ =>
        Real.log y -
          fabiusSharpLambertMain (fabiusInv F hF y))
      (fun j y =>
        fabiusSaddleLogCoefficient j
          (fabiusLambertPhase (fabiusInv F hF y))) := by
  have hcomp :=
    (log_fabius_sub_sharpLambertMain_hasAsymptoticExpansion F hF).comp_tendsto
      (fabiusInv F hF) (tendsto_fabiusInv_nhdsGT_zero F hF)
  have hfun :
      ((fun x : ℝ =>
          Real.log (fabiusReal F x) -
            fabiusSharpLambertMain x) ∘
          fabiusInv F hF)
        =ᶠ[𝓝[>] (0 : ℝ)]
      (fun y : ℝ =>
        Real.log y -
          fabiusSharpLambertMain (fabiusInv F hF y)) := by
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with y hy
    simp only [Function.comp_def]
    rw [fabiusReal_fabiusInv F hF ⟨hy.1.le, hy.2.le⟩]
  simpa only [Function.comp_def] using
    hcomp.congr Filter.EventuallyEq.rfl hfun

/-- The inverse-coordinate sharp-main defect is
`O(1 / fabiusLambertPhase (fabiusInv F hF y))` as `y -> 0+`.

This is the order-one remainder of the full pullback expansion: its only
retained coefficient is the identically zero zeroth saddle-log coefficient. -/
theorem log_sub_sharpLambertMain_comp_fabiusInv_isBigO_inv_phase
    (F : BoundedFabius) (hF : IsFabius F) :
    (fun y : ℝ =>
      Real.log y -
        fabiusSharpLambertMain (fabiusInv F hF y))
      =O[𝓝[>] (0 : ℝ)]
        (fun y : ℝ =>
          (fabiusLambertPhase (fabiusInv F hF y))⁻¹) := by
  have h :=
    (log_sub_sharpLambertMain_comp_fabiusInv_hasAsymptoticExpansion
      F hF).remainder_isBigO 1
  simpa only [SaddleExpansion.partialSum, Finset.sum_range_one,
    pow_zero, one_smul, fabiusSaddleLogCoefficient_zero,
    sub_zero, pow_one] using h

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
    exact tendsto_fabiusLambertPhase_nhdsGT_zero_atTop.comp hinv
  have hbase :
      (fun y : ℝ => Real.log y -
        fabiusSharpLambertMain (fabiusInv F hF y)) =O[l]
          (fun _ : ℝ => (1 : ℝ)) := by
    simpa only [SaddleExpansion.partialSum_zero, sub_zero, pow_zero] using
      (log_sub_sharpLambertMain_comp_fabiusInv_hasAsymptoticExpansion
        F hF).remainder_isBigO 0
  have honeLog :
      (fun _ : ℝ => (1 : ℝ)) =O[l] (fun y => Real.log (lam y)) := by
    simpa only [Function.comp_def] using
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
      (tendsto_fabiusLambertPhase_nhdsGT_zero_atTop.comp
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

/-- `|log (1 + u)| ≤ 2|u|` for `|u| ≤ 1/2`: from `log x ≤ x - 1` at
`x = 1 + u` and at `x = (1 + u)⁻¹`. -/
private theorem abs_log_one_add_le_two_mul {u : ℝ} (hu : |u| ≤ 1 / 2) :
    |Real.log (1 + u)| ≤ 2 * |u| := by
  have hu' := abs_le.mp hu
  have hpos : 0 < 1 + u := by linarith
  have hupper : Real.log (1 + u) ≤ u := by
    have := Real.log_le_sub_one_of_pos hpos
    linarith
  have hlower : u / (1 + u) ≤ Real.log (1 + u) := by
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
    rw [Real.log_inv] at h
    have heq : (1 + u)⁻¹ - 1 = -(u / (1 + u)) := by
      rw [inv_eq_one_div, div_sub_one hpos.ne', ← neg_div]
      congr 1
      ring
    linarith
  rw [abs_le]
  rcases le_or_gt 0 u with hu0 | hu0
  · have h3 : 0 ≤ u / (1 + u) := div_nonneg hu0 hpos.le
    rw [abs_of_nonneg hu0]
    constructor <;> linarith
  · have h3 : 2 * u ≤ u / (1 + u) := by
      rw [le_div_iff₀ hpos]
      nlinarith [mul_nonneg (neg_nonneg.mpr hu0.le)
        (by linarith : (0 : ℝ) ≤ 1 + 2 * u)]
    rw [abs_of_neg hu0]
    constructor <;> linarith

/-- **Quantitative logarithmic transfer of a square-root–affine
approximation.**  If `T → ∞` and `lam = √(cT) + a + O(log T/√T)`, then

`log lam = log T/2 + log c/2 + O(log T/√T)`.

The rate survives the logarithm because `log(lam/√(cT)) = log(1 + u)` with
`u = (lam - √(cT))/√(cT) = O(1/√T)`, and `|log(1 + u)| ≤ 2|u|` for small
`u`. -/
theorem log_sub_half_log_isBigO_of_sqrt_affine_approximation
    {α : Type*} {l : Filter α} {T lam : α → ℝ} {c a : ℝ}
    (hc : 0 < c) (hT : Tendsto T l atTop)
    (happrox : (fun i => lam i - (Real.sqrt (c * T i) + a)) =O[l]
      (fun i => Real.log (T i) / Real.sqrt (T i))) :
    (fun i => Real.log (lam i) -
      (Real.log (T i) / 2 + Real.log c / 2)) =O[l]
      (fun i => Real.log (T i) / Real.sqrt (T i)) := by
  have hrateTop :
      Tendsto (fun t : ℝ => Real.log t / Real.sqrt t) atTop (nhds 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop
        (r := (1 / 2 : ℝ)) (by norm_num)).tendsto_div_nhds_zero
  have hrate0 :
      Tendsto (fun i => Real.log (T i) / Real.sqrt (T i)) l (nhds 0) :=
    hrateTop.comp hT
  have hTpos : ∀ᶠ i in l, 0 < T i := hT.eventually_gt_atTop 0
  have hTe : ∀ᶠ i in l, 1 ≤ Real.log (T i) := by
    filter_upwards [hT.eventually_ge_atTop (Real.exp 1)] with i hi
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (T i) := Real.log_le_log (Real.exp_pos 1) hi
  -- the deviation `lam - √(cT)` is bounded
  have hdev : (fun i => lam i - Real.sqrt (c * T i)) =O[l]
      (fun _ => (1 : ℝ)) := by
    have h1 : (fun i => lam i - (Real.sqrt (c * T i) + a)) =O[l]
        (fun _ => (1 : ℝ)) :=
      (happrox.trans_tendsto hrate0).isBigO_one ℝ
    have h2 : (fun _ : α => a) =O[l] (fun _ => (1 : ℝ)) :=
      isBigO_const_const a one_ne_zero l
    exact (h1.add h2).congr_left fun i => by ring
  -- hence `u = (lam - √(cT))/√(cT) = O(1/√T)`
  set u : α → ℝ := fun i =>
    (lam i - Real.sqrt (c * T i)) / Real.sqrt (c * T i) with hu_def
  have hsqrtc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hu : u =O[l] (fun i => (Real.sqrt (T i))⁻¹) := by
    have h := hdev.mul (isBigO_refl (fun i => (Real.sqrt (c * T i))⁻¹) l)
    refine (h.congr_left fun i => by
      simp only [hu_def, div_eq_mul_inv]).trans ?_
    refine IsBigO.of_bound (Real.sqrt c)⁻¹ ?_
    filter_upwards [hTpos] with i hi
    refine le_of_eq ?_
    rw [one_mul, Real.sqrt_mul hc.le, mul_inv, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (by positivity), abs_of_pos (by positivity)]
  have hsqrtT : Tendsto (fun i => (Real.sqrt (T i))⁻¹) l (nhds 0) :=
    (Real.tendsto_sqrt_atTop.comp hT).inv_tendsto_atTop
  have hu0 : Tendsto u l (nhds 0) := hu.trans_tendsto hsqrtT
  have husmall : ∀ᶠ i in l, |u i| ≤ 1 / 2 := by
    filter_upwards [Metric.tendsto_nhds.mp hu0 (1 / 2) (by norm_num)] with i hi
    rw [Real.dist_eq, sub_zero] at hi
    exact hi.le
  -- `log (1 + u) = O(u)`
  have hlog : (fun i => Real.log (1 + u i)) =O[l] u := by
    refine IsBigO.of_bound 2 ?_
    filter_upwards [husmall] with i hi
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact abs_log_one_add_le_two_mul hi
  -- `lam > 0` eventually
  have hlamPos : ∀ᶠ i in l, 0 < lam i := by
    filter_upwards [husmall, hTpos] with i hi hi0
    have hs : 0 < Real.sqrt (c * T i) := Real.sqrt_pos.mpr (mul_pos hc hi0)
    have hs' : Real.sqrt (c * T i) ≠ 0 := hs.ne'
    have hui : -(1 / 2) ≤ u i := (abs_le.mp hi).1
    have hcancel : Real.sqrt (c * T i) *
        ((lam i - Real.sqrt (c * T i)) / Real.sqrt (c * T i)) =
        lam i - Real.sqrt (c * T i) := by
      field_simp
    have hlam : lam i = Real.sqrt (c * T i) * (1 + u i) := by
      simp only [hu_def]
      rw [mul_add, mul_one, hcancel]
      ring
    rw [hlam]
    exact mul_pos hs (by linarith)
  -- `log lam - log √(cT) = log (1 + u)`
  have hkey : (fun i => Real.log (lam i) -
      (Real.log (T i) / 2 + Real.log c / 2)) =ᶠ[l]
      (fun i => Real.log (1 + u i)) := by
    filter_upwards [hlamPos, hTpos] with i hli hi0
    have hs : 0 < Real.sqrt (c * T i) := Real.sqrt_pos.mpr (mul_pos hc hi0)
    have h1u : 1 + u i = lam i / Real.sqrt (c * T i) := by
      simp only [hu_def]
      rw [add_div' _ _ _ hs.ne']
      congr 1
      ring
    rw [h1u, Real.log_div hli.ne' hs.ne',
      Real.log_sqrt (mul_nonneg hc.le hi0.le), Real.log_mul hc.ne' hi0.ne']
    ring
  refine ((hlog.trans hu).congr' hkey.symm EventuallyEq.rfl).trans ?_
  -- `1/√T = O(log T/√T)` once `log T ≥ 1`
  refine IsBigO.of_bound 1 ?_
  filter_upwards [hTpos, hTe] with i hi0 hi1
  have hs : 0 < Real.sqrt (T i) := Real.sqrt_pos.mpr hi0
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hs),
    abs_of_pos (div_pos (by linarith) hs), inv_eq_one_div]
  gcongr

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
    field_simp [hL.ne']
  have hleftNonneg :
      0 ≤ Real.log 2 * Real.sqrt (2 * T / Real.log 2) :=
    mul_nonneg hL.le (Real.sqrt_nonneg _)
  have hrightNonneg : 0 ≤ Real.sqrt (2 * Real.log 2 * T) :=
    Real.sqrt_nonneg _
  nlinarith

/-- **Sharp logarithmic asymptotic of the inverse Fabius function, with
rate.**

For `T = -log y` and `L = log 2`,

`log (fabiusInv F hF y) =
  -sqrt (2 * L * T) + log T / 2 - 1 - log L / 2 + O(log T / sqrt T)`

as `y -> 0+`.  The constant `-1` is the exact cancellation between the
half-logarithm of `2` and the affine phase displacement; the rate is the
one of the phase estimate, carried through the logarithm by
`log_sub_half_log_isBigO_of_sqrt_affine_approximation`. -/
theorem log_fabiusInv_sub_fabiusInverseLogAsymptoticMain_isBigO
    (F : BoundedFabius) (hF : IsFabius F) :
    (fun y : ℝ => Real.log (fabiusInv F hF y) -
      fabiusInverseLogAsymptoticMain y) =O[𝓝[>] (0 : ℝ)]
      (fun y : ℝ =>
        Real.log (-Real.log y) / Real.sqrt (-Real.log y)) := by
  let l : Filter ℝ := 𝓝[>] (0 : ℝ)
  have hL : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hT : Tendsto (fun y : ℝ => -Real.log y) l atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hphase :=
    fabiusLambertPhase_fabiusInv_sub_fabiusInverseQuadraticPhaseMain_isBigO
      F hF
  have hlogPhase :=
    log_sub_half_log_isBigO_of_sqrt_affine_approximation
      (T := fun y : ℝ => -Real.log y)
      (lam := fun y : ℝ => fabiusLambertPhase (fabiusInv F hF y))
      (c := 2 / Real.log 2)
      (a := (1 + Real.log 2 / 2) / Real.log 2)
      (div_pos (by norm_num) hL) hT (by
        refine hphase.congr_left fun y => ?_
        unfold fabiusInverseQuadraticPhaseMain
        congr 3
        all_goals ring)
  have hraw := hlogPhase.sub (hphase.const_mul_left (Real.log 2))
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
  refine hraw.congr' ?_ EventuallyEq.rfl
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
  have hsqrt :
      Real.log 2 * Real.sqrt (-(Real.log y * 2 / Real.log 2)) =
        Real.sqrt (-(Real.log y * 2 * Real.log 2)) := by
    convert log_two_mul_sqrt_two_mul_div_log_two
      (-Real.log y) hTPos.le using 1
    all_goals ring_nf
  rw [Real.log_div (by norm_num : (2 : ℝ) ≠ 0) hL.ne']
  field_simp [hL.ne']
  nlinarith [hsqrt]

/-- **Sharp logarithmic asymptotic of the inverse Fabius function** (the
`o(1)` form): the rate `O(log T / sqrt T)` of
`log_fabiusInv_sub_fabiusInverseLogAsymptoticMain_isBigO` tends to `0`. -/
theorem tendsto_log_fabiusInv_sub_fabiusInverseLogAsymptoticMain
    (F : BoundedFabius) (hF : IsFabius F) :
    Tendsto
      (fun y : ℝ => Real.log (fabiusInv F hF y) -
        fabiusInverseLogAsymptoticMain y)
      (𝓝[>] (0 : ℝ)) (nhds 0) := by
  have hT : Tendsto (fun y : ℝ => -Real.log y) (𝓝[>] (0 : ℝ)) atTop :=
    tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hrateTop :
      Tendsto (fun T : ℝ => Real.log T / Real.sqrt T)
        atTop (nhds 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop
        (r := (1 / 2 : ℝ)) (by norm_num)).tendsto_div_nhds_zero
  exact IsBigO.trans_tendsto
    (log_fabiusInv_sub_fabiusInverseLogAsymptoticMain_isBigO F hF)
    (hrateTop.comp hT)

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
  refine (fabiusInv_isEquivalent_exp_fabiusInverseLogAsymptoticMain F hF).trans_eventuallyEq ?_
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
      simp only [Function.comp_apply, pow_one, id_eq]
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
      simp only [Function.comp_apply, id_eq]
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
    (Real.isLittleO_log_id_atTop.const_mul_left (1 / 2 : ℝ)).const_mul_right hα.ne'
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
  have hlinearEq :=
    IsEquivalent.refl (l := atTop) (u := fun T : ℝ => α * T)
  have hraw :=
    ((hlinearEq.sub_isLittleO hroot).add_isLittleO hlog).add_isLittleO hconstant
  have heq :
      (fun T : ℝ =>
        α * T - Real.sqrt (2 * Real.log 2 * T) +
          Real.log T / 2 - 1 - Real.log (Real.log 2) / 2) ~[atTop]
        (fun T => α * T) := by
    apply hraw.congr_left
    filter_upwards with T
    simp only [Pi.add_apply, Pi.sub_apply]
    ring_nf
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
    simpa only [Function.comp_def, id_eq] using
      (Asymptotics.isLittleO_const_id_atTop
        (1 + Real.log (Real.log 2) / 2)).comp_tendsto hrootTop
  have hrootEq :=
    IsEquivalent.refl
      (l := atTop)
      (u := fun T : ℝ => Real.sqrt (2 * Real.log 2 * T))
  have hraw := (hrootEq.add_isLittleO hlog).add_isLittleO hconstant
  have heq :
      (fun T : ℝ =>
        Real.sqrt (2 * Real.log 2 * T) +
          (r - 1 / 2) * Real.log T +
          1 + Real.log (Real.log 2) / 2) ~[atTop]
        (fun T => Real.sqrt (2 * Real.log 2 * T)) := by
    apply hraw.congr_left
    filter_upwards with T
    simp only [Pi.add_apply]
    ring_nf
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
    apply ((tendsto_fabiusInversePowerGap_atTop hα).comp hT).congr'
    filter_upwards with y
    unfold fabiusInverseLogAsymptoticMain
    simp only [Function.comp_def]
    ring_nf
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

/-- **Quotient form of positive-power separation at zero.**

For every `α > 0`, the inverse Fabius function divided by `y ^ α` tends to
positive infinity as `y -> 0+`.  This is the sharp limit formulation of the
fact that the inverse outruns every positive real power. -/
theorem tendsto_fabiusInv_div_rpow_atTop_at_zero_right
    (F : BoundedFabius) (hF : IsFabius F)
    {α : ℝ} (hα : 0 < α) :
    Tendsto (fun y : ℝ => fabiusInv F hF y / y ^ α)
      (𝓝[>] (0 : ℝ)) atTop := by
  have hzero :
      Tendsto (fun y : ℝ => y ^ α / fabiusInv F hF y)
        (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    (rpow_isLittleO_fabiusInv_at_zero_right F hF hα).tendsto_div_nhds_zero
  have hpos :
      ∀ᶠ y : ℝ in 𝓝[>] (0 : ℝ),
        0 < y ^ α / fabiusInv F hF y := by
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with y hy
    exact div_pos
      (Real.rpow_pos_of_pos hy.1 α)
      (fabiusInv_mem_Ioo F hF hy).1
  have hwithin :
      Tendsto (fun y : ℝ => y ^ α / fabiusInv F hF y)
        (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hzero, hpos⟩
  exact hwithin.inv_tendsto_nhdsGT_zero.congr fun y => by
    simp [Pi.inv_apply, inv_div]

/-- The inverse Fabius function is not `O(y ^ α)` at zero for any positive
real exponent `α`. -/
theorem fabiusInv_not_isBigO_rpow_at_zero_right
    (F : BoundedFabius) (hF : IsFabius F)
    {α : ℝ} (hα : 0 < α) :
    ¬ ((fabiusInv F hF) =O[𝓝[>] (0 : ℝ)]
      (fun y : ℝ => y ^ α)) := by
  have hne :
      ∀ᶠ y : ℝ in 𝓝[>] (0 : ℝ), y ^ α ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (Real.rpow_pos_of_pos hy α).ne'
  exact
    (rpow_isLittleO_fabiusInv_at_zero_right F hF hα).not_isBigO
      hne.frequently

/-- **Failure of every positive-order local Hölder bound at zero.**

For `α > 0`, no positive constants `C` and `δ` bound the inverse by
`C * y ^ α` throughout the closed endpoint interval `[0, δ]`. -/
theorem not_exists_fabiusInv_le_const_mul_rpow_near_zero
    (F : BoundedFabius) (hF : IsFabius F)
    {α : ℝ} (hα : 0 < α) :
    ¬ ∃ C > 0, ∃ δ > 0, ∀ y ∈ Set.Icc (0 : ℝ) δ,
      fabiusInv F hF y ≤ C * y ^ α := by
  rintro ⟨C, _hC, δ, hδ, hbound⟩
  apply fabiusInv_not_isBigO_rpow_at_zero_right F hF hα
  apply IsBigO.of_bound C
  filter_upwards [Icc_mem_nhdsGT hδ] with y hy
  simpa only [
    Real.norm_of_nonneg (fabiusInv_nonneg F hF y),
    Real.norm_of_nonneg (Real.rpow_nonneg hy.1 α)
  ] using hbound y hy

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
    apply ((tendsto_fabiusInverseLogPowerGap_atTop r).comp hT).congr'
    filter_upwards with y
    unfold fabiusInverseLogAsymptoticMain
    simp only [Function.comp_def]
    ring_nf
  have hexp :
      (fun y : ℝ => Real.exp (fabiusInverseLogAsymptoticMain y)) =o[l]
        (fun y => Real.exp (Real.log (-Real.log y) * r)) :=
    Real.isLittleO_exp_comp_exp_comp.mpr hgap
  have hinvExp :=
    (fabiusInv_isEquivalent_exp_fabiusInverseLogAsymptoticMain F hF).trans_isLittleO hexp
  apply hinvExp.congr'
  · exact Filter.EventuallyEq.rfl
  · filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with y hy
    have hTPos : 0 < -Real.log y :=
      neg_pos.mpr (Real.log_neg hy.1 hy.2)
    rw [Real.rpow_def_of_pos hTPos]

/-- Every positive real power of the remaining distance to one is negligible
beside the inverse Fabius deficiency:

`(1 - y) ^ α = o(1 - fabiusInv F hF y)` for every `α > 0` as `y -> 1-`. -/
theorem one_sub_rpow_isLittleO_one_sub_fabiusInv_at_one_left
    (F : BoundedFabius) (hF : IsFabius F)
    {α : ℝ} (hα : 0 < α) :
    (fun y : ℝ => (1 - y) ^ α) =o[𝓝[<] (1 : ℝ)]
      (fun y : ℝ => 1 - fabiusInv F hF y) := by
  simpa only [Function.comp_def, fabiusInv_one_sub] using
    (rpow_isLittleO_fabiusInv_at_zero_right F hF hα).comp_tendsto
      tendsto_one_sub_nhdsLT_one_nhdsGT_zero

/-- The inverse Fabius deficiency is negligible beside every real power of
the reflected endpoint logarithmic scale:

`1 - fabiusInv F hF y = o((-log (1 - y)) ^ r)` for every `r : ℝ` as
`y -> 1-`. -/
theorem one_sub_fabiusInv_isLittleO_negLog_one_sub_rpow_at_one_left
    (F : BoundedFabius) (hF : IsFabius F) (r : ℝ) :
    (fun y : ℝ => 1 - fabiusInv F hF y) =o[𝓝[<] (1 : ℝ)]
      (fun y : ℝ => (-Real.log (1 - y)) ^ r) := by
  simpa only [Function.comp_def, fabiusInv_one_sub] using
    (fabiusInv_isLittleO_negLog_rpow_at_zero_right F hF r).comp_tendsto
      tendsto_one_sub_nhdsLT_one_nhdsGT_zero

/-- **Reflected quotient divergence for every positive real exponent.**

For every `α > 0`, the inverse deficiency divided by `(1 - y) ^ α` tends to
positive infinity as `y -> 1-`. -/
theorem tendsto_one_sub_fabiusInv_div_one_sub_rpow_atTop_at_one_left
    (F : BoundedFabius) (hF : IsFabius F)
    {α : ℝ} (hα : 0 < α) :
    Tendsto
      (fun y : ℝ => (1 - fabiusInv F hF y) / (1 - y) ^ α)
      (𝓝[<] (1 : ℝ)) atTop := by
  have h :=
    (tendsto_fabiusInv_div_rpow_atTop_at_zero_right F hF hα).comp
      tendsto_one_sub_nhdsLT_one_nhdsGT_zero
  simpa only [Function.comp_def, fabiusInv_one_sub] using h

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
