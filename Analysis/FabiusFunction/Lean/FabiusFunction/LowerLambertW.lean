import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# The lower real Lambert W branch

This module supplies the minimal real `W_{-1}` infrastructure needed for
equation (9) of the local K-fold Thue--Morse draft.  The branch is totalized;
its defining equation, order, uniqueness, and exact-range API covers the
closed-left natural domain `[-exp(-1), 0)`, while its ordinary continuity and
derivative API uses the smooth interior `(-exp(-1), 0)`.

It also proves the near-zero logarithmic bounds of the Lambert W guide,

`-η - η·log η / (η - 1) ≤ W₋₁(x) < -η - log η`  for  `-1/e < x < 0`,
`η = log (1 / (-x)) > 1`,

and reads the standard first two terms of the branch's asymptotic expansion
off that bracket, together with the explicit `O(log η / η)` rate they carry.
-/

set_option autoImplicit false

open Set Filter Function Topology

namespace Fabius

noncomputable section

private def mulLog (u : ℝ) : ℝ := u * Real.log u

private lemma mulLog_image :
    mulLog '' Ioo (0 : ℝ) (Real.exp (-1)) = Ioo (-Real.exp (-1)) 0 := by
  have h := Real.continuous_mul_log.continuousOn.image_Ioo_of_strictAntiOn
    (show (0 : ℝ) ≤ Real.exp (-1) by positivity)
    Real.mul_log_strictAntiOn
  simpa [mulLog] using h

private lemma exists_mulLog_eq {z : ℝ} (hz : z ∈ Ioo (-Real.exp (-1)) 0) :
    ∃ u ∈ Ioo (0 : ℝ) (Real.exp (-1)), mulLog u = z := by
  rw [← mulLog_image] at hz
  exact hz

/-- The positive argument whose logarithm is the lower real Lambert branch. -/
noncomputable def lowerLambertArg (z : ℝ) : ℝ :=
  Function.invFunOn mulLog (Icc (0 : ℝ) (Real.exp (-1))) z

/-- A totalized definition of the lower real Lambert branch.  Its natural
domain is `[-exp (-1), 0)`; derivative statements use the smooth interior. -/
noncomputable def lowerLambertW (z : ℝ) : ℝ :=
  Real.log (lowerLambertArg z)

private lemma lowerLambertArg_spec {z : ℝ} (hz : z ∈ Ioo (-Real.exp (-1)) 0) :
    lowerLambertArg z ∈ Ioo (0 : ℝ) (Real.exp (-1)) ∧
      mulLog (lowerLambertArg z) = z := by
  obtain ⟨u, hu, huz⟩ := exists_mulLog_eq hz
  have hex : ∃ u ∈ Icc (0 : ℝ) (Real.exp (-1)), mulLog u = z :=
    ⟨u, ⟨hu.1.le, hu.2.le⟩, huz⟩
  have hspec0 := Function.invFunOn_pos hex
  have hspec : lowerLambertArg z ∈ Icc (0 : ℝ) (Real.exp (-1)) ∧
      mulLog (lowerLambertArg z) = z := by
    simpa [lowerLambertArg] using hspec0
  refine ⟨?_, hspec.2⟩
  constructor
  · exact lt_of_le_of_ne hspec.1.1 fun hzero => by
      rw [← hzero] at hspec
      simp [mulLog] at hspec
      exact hz.2.ne hspec.2.symm
  · exact lt_of_le_of_ne hspec.1.2 fun htop => by
      rw [htop] at hspec
      have heval : mulLog (Real.exp (-1)) = -Real.exp (-1) := by
        simp [mulLog]
      rw [heval] at hspec
      exact hz.1.ne hspec.2

private lemma lowerLambertArg_branchPoint :
    lowerLambertArg (-Real.exp (-1)) = Real.exp (-1) := by
  have hex : ∃ u ∈ Icc (0 : ℝ) (Real.exp (-1)),
      mulLog u = -Real.exp (-1) := by
    refine ⟨Real.exp (-1), ⟨(Real.exp_pos _).le, le_rfl⟩, ?_⟩
    simp [mulLog]
  have hspec0 := Function.invFunOn_pos hex
  have hspec : lowerLambertArg (-Real.exp (-1)) ∈
        Icc (0 : ℝ) (Real.exp (-1)) ∧
      mulLog (lowerLambertArg (-Real.exp (-1))) =
        -Real.exp (-1) := by
    simpa [lowerLambertArg] using hspec0
  apply Real.mul_log_strictAntiOn.injOn hspec.1
    ⟨(Real.exp_pos _).le, le_rfl⟩
  change mulLog (lowerLambertArg (-Real.exp (-1))) =
    mulLog (Real.exp (-1))
  rw [hspec.2]
  simp [mulLog]

/-- At the branch point, the lower real Lambert branch has value `-1`. -/
@[simp] theorem lowerLambertW_branchPoint :
    lowerLambertW (-Real.exp (-1)) = -1 := by
  rw [lowerLambertW, lowerLambertArg_branchPoint, Real.log_exp]

private lemma lowerLambertArg_spec_of_mem_Ico {z : ℝ}
    (hz : z ∈ Ico (-Real.exp (-1)) 0) :
    lowerLambertArg z ∈ Ioc (0 : ℝ) (Real.exp (-1)) ∧
      mulLog (lowerLambertArg z) = z := by
  rcases hz.1.eq_or_lt with rfl | hzlt
  · rw [lowerLambertArg_branchPoint]
    exact ⟨⟨Real.exp_pos _, le_rfl⟩, by simp [mulLog]⟩
  · have h := lowerLambertArg_spec ⟨hzlt, hz.2⟩
    exact ⟨⟨h.1.1, h.1.2.le⟩, h.2⟩

/-- On the full closed-left natural domain, the lower branch is at most
`-1`, with equality at the branch point. -/
theorem lowerLambertW_le_neg_one {z : ℝ}
    (hz : z ∈ Ico (-Real.exp (-1)) 0) :
    lowerLambertW z ≤ -1 := by
  rw [lowerLambertW]
  have hu := (lowerLambertArg_spec_of_mem_Ico hz).1
  exact (Real.log_le_iff_le_exp hu.1).2 hu.2

/-- On the smooth interior of its natural domain, the lower branch is strictly below `-1`. -/
theorem lowerLambertW_lt_neg_one {z : ℝ} (hz : z ∈ Ioo (-Real.exp (-1)) 0) :
    lowerLambertW z < -1 := by
  rw [lowerLambertW]
  have hu := (lowerLambertArg_spec hz).1
  exact (Real.log_lt_iff_lt_exp hu.1).2 hu.2

/-- Defining equation on the closed-left natural domain
`[-exp(-1), 0)`, including the branch point. -/
theorem lowerLambertW_mul_exp_of_mem_Ico {z : ℝ}
    (hz : z ∈ Ico (-Real.exp (-1)) 0) :
    lowerLambertW z * Real.exp (lowerLambertW z) = z := by
  rw [lowerLambertW,
    Real.exp_log (lowerLambertArg_spec_of_mem_Ico hz).1.1]
  simpa [mulLog, mul_comm] using
    (lowerLambertArg_spec_of_mem_Ico hz).2

/-- Defining equation `W(z) exp(W(z)) = z` on the interior of the lower
real branch. -/
theorem lowerLambertW_mul_exp {z : ℝ} (hz : z ∈ Ioo (-Real.exp (-1)) 0) :
    lowerLambertW z * Real.exp (lowerLambertW z) = z :=
  lowerLambertW_mul_exp_of_mem_Ico ⟨hz.1.le, hz.2⟩

/-- Uniqueness of the real Lambert solution at or below `-1` on the full
closed-left natural domain. -/
theorem lowerLambertW_unique_of_mem_Ico {z w : ℝ}
    (hz : z ∈ Ico (-Real.exp (-1)) 0) (hw : w ≤ -1)
    (heq : w * Real.exp w = z) :
    w = lowerLambertW z := by
  have hew : Real.exp w ∈ Ioc (0 : ℝ) (Real.exp (-1)) :=
    ⟨Real.exp_pos _, Real.exp_le_exp.2 hw⟩
  have harg := (lowerLambertArg_spec_of_mem_Ico hz).1
  have hargEq : mulLog (Real.exp w) = mulLog (lowerLambertArg z) := by
    rw [(lowerLambertArg_spec_of_mem_Ico hz).2]
    simpa [mulLog, mul_comm] using heq
  have hinj := Real.mul_log_strictAntiOn.injOn
  have hexp : Real.exp w = lowerLambertArg z :=
    hinj ⟨hew.1.le, hew.2⟩ ⟨harg.1.le, harg.2⟩ hargEq
  rw [lowerLambertW, ← hexp, Real.log_exp]

/-- Uniqueness of the real Lambert solution below `-1`. -/
theorem lowerLambertW_unique {z w : ℝ} (hz : z ∈ Ioo (-Real.exp (-1)) 0)
    (hw : w < -1) (heq : w * Real.exp w = z) :
    w = lowerLambertW z :=
  lowerLambertW_unique_of_mem_Ico ⟨hz.1.le, hz.2⟩ hw.le heq

/-- The lower real Lambert branch is strictly decreasing on its closed-left
natural domain. -/
theorem lowerLambertW_strictAntiOn_Ico :
    StrictAntiOn lowerLambertW (Ico (-Real.exp (-1)) 0) := by
  intro z₁ hz₁ z₂ hz₂ hz
  have hs₁ := lowerLambertArg_spec_of_mem_Ico hz₁
  have hs₂ := lowerLambertArg_spec_of_mem_Ico hz₂
  have harg : lowerLambertArg z₂ < lowerLambertArg z₁ := by
    by_contra hnot
    have hle : lowerLambertArg z₁ ≤ lowerLambertArg z₂ := le_of_not_gt hnot
    rcases hle.eq_or_lt with heq | hlt
    · have hzEq : z₁ = z₂ := by
        rw [← hs₁.2, ← hs₂.2, heq]
      exact (ne_of_lt hz) hzEq
    · have hanti := Real.mul_log_strictAntiOn
          ⟨hs₁.1.1.le, hs₁.1.2⟩ ⟨hs₂.1.1.le, hs₂.1.2⟩ hlt
      change mulLog (lowerLambertArg z₂) <
        mulLog (lowerLambertArg z₁) at hanti
      rw [hs₁.2, hs₂.2] at hanti
      exact (not_lt_of_ge hz.le) hanti
  rw [lowerLambertW, lowerLambertW]
  exact Real.strictMonoOn_log hs₂.1.1 hs₁.1.1 harg

/-- The lower real Lambert branch is strictly decreasing on the smooth
interior of its natural domain. -/
theorem lowerLambertW_strictAntiOn :
    StrictAntiOn lowerLambertW (Ioo (-Real.exp (-1)) 0) :=
  lowerLambertW_strictAntiOn_Ico.mono fun _ hz ↦ ⟨hz.1.le, hz.2⟩

/-- Exact range of the lower real Lambert branch on its smooth interior. -/
theorem lowerLambertW_image :
    lowerLambertW '' Ioo (-Real.exp (-1)) 0 = Iio (-1) := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact lowerLambertW_lt_neg_one hz
  · intro w hw
    let z : ℝ := w * Real.exp w
    have hw0 : w < 0 := hw.trans (by norm_num)
    have hew : Real.exp w ∈ Ioo (0 : ℝ) (Real.exp (-1)) :=
      ⟨Real.exp_pos _, Real.exp_lt_exp.2 hw⟩
    have hanti := Real.mul_log_strictAntiOn
      ⟨hew.1.le, hew.2.le⟩
      ⟨(Real.exp_pos _).le, le_rfl⟩ hew.2
    have hz : z ∈ Ioo (-Real.exp (-1)) 0 := by
      constructor
      · simpa [z, mulLog, mul_comm] using hanti
      · exact mul_neg_of_neg_of_pos hw0 (Real.exp_pos _)
    refine ⟨z, hz, ?_⟩
    exact (lowerLambertW_unique hz hw rfl).symm

/-- Exact range of the lower real Lambert branch on the full closed-left
natural domain. -/
theorem lowerLambertW_image_Ico :
    lowerLambertW '' Ico (-Real.exp (-1)) 0 = Iic (-1) := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact lowerLambertW_le_neg_one hz
  · intro w hw
    change w ≤ -1 at hw
    rcases eq_or_lt_of_le hw with rfl | hwlt
    · exact ⟨-Real.exp (-1), ⟨le_rfl, neg_lt_zero.2 (Real.exp_pos _)⟩,
        lowerLambertW_branchPoint⟩
    · have hwmem : w ∈ Iio (-1) := hwlt
      rw [← lowerLambertW_image] at hwmem
      obtain ⟨z, hz, hzw⟩ := hwmem
      exact ⟨z, ⟨hz.1.le, hz.2⟩, hzw⟩

/-- The lower branch is right-continuous at the real branch point relative
to its closed-left natural domain.

Negating the branch turns its strict antitonicity into strict monotonicity;
the exact image `(-W₋₁) '' [-exp (-1), 0) = [1, ∞)` then rules out a
jump at the endpoint. -/
theorem lowerLambertW_continuousWithinAt_branchPoint :
    ContinuousWithinAt lowerLambertW (Ico (-Real.exp (-1)) 0)
      (-Real.exp (-1)) := by
  let g : ℝ → ℝ := fun x ↦ -lowerLambertW x
  have hgmono : StrictMonoOn g (Ico (-Real.exp (-1)) 0) := by
    intro a ha b hb hab
    exact neg_lt_neg (lowerLambertW_strictAntiOn_Ico ha hb hab)
  have hgimage : g '' Ico (-Real.exp (-1)) 0 = Ici 1 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact mem_Ici.mpr (by
        dsimp only [g]
        linarith [lowerLambertW_le_neg_one hx])
    · intro hy
      have hneg : -y ∈ Iic (-1) := by
        exact mem_Iic.mpr (by linarith [mem_Ici.mp hy])
      rw [← lowerLambertW_image_Ico] at hneg
      obtain ⟨x, hx, hxy⟩ := hneg
      refine ⟨x, hx, ?_⟩
      dsimp only [g]
      rw [hxy]
      simp
  have hg : ContinuousWithinAt g (Ici (-Real.exp (-1)))
      (-Real.exp (-1)) := by
    apply hgmono.continuousWithinAt_right_of_image_mem_nhdsWithin
    · exact Ico_mem_nhdsGE (neg_lt_zero.mpr (Real.exp_pos _))
    · rw [hgimage]
      have hgbp : g (-Real.exp (-1)) = 1 := by
        simp [g]
      rw [hgbp]
      exact self_mem_nhdsWithin
  have hgneg : ContinuousWithinAt (fun x ↦ -g x)
      (Ici (-Real.exp (-1))) (-Real.exp (-1)) := hg.neg
  have hfun : (fun x ↦ -g x) = lowerLambertW := by
    funext x
    simp [g]
  rw [hfun] at hgneg
  exact hgneg.mono fun _ hx ↦ mem_Ici.mpr hx.1

/-- The lower real Lambert branch is continuous at every point of the smooth
interior of its natural domain. -/
theorem lowerLambertW_continuousAt {z : ℝ}
    (hz : z ∈ Ioo (-Real.exp (-1)) 0) :
    ContinuousAt lowerLambertW z := by
  let g : ℝ → ℝ := fun x => -lowerLambertW x
  have hgmono : StrictMonoOn g (Ioo (-Real.exp (-1)) 0) := by
    intro a ha b hb hab
    exact neg_lt_neg (lowerLambertW_strictAntiOn ha hb hab)
  have hgimage : g '' Ioo (-Real.exp (-1)) 0 = Ioi 1 := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change 1 < -lowerLambertW x
      simpa only [neg_neg] using neg_lt_neg (lowerLambertW_lt_neg_one hx)
    · intro hy
      have hneg : -y ∈ Iio (-1) := by
        simpa only [mem_Iio] using (neg_lt_neg hy)
      rw [← lowerLambertW_image] at hneg
      obtain ⟨x, hx, hxy⟩ := hneg
      refine ⟨x, hx, ?_⟩
      dsimp [g]
      rw [hxy]
      simp
  have hg : ContinuousAt g z :=
    hgmono.continuousAt_of_image_mem_nhds
      (isOpen_Ioo.mem_nhds hz) (by
        rw [hgimage]
        exact Ioi_mem_nhds (by
          dsimp [g]
          linarith [lowerLambertW_lt_neg_one hz]))
  have hgneg : ContinuousAt (fun x => -g x) z := hg.neg
  have hfun : (fun x => -g x) = lowerLambertW := by
    funext x
    simp [g]
  rwa [hfun] at hgneg

/-- Continuity of the lower real Lambert branch on its smooth interior. -/
theorem lowerLambertW_continuousOn :
    ContinuousOn lowerLambertW (Ioo (-Real.exp (-1)) 0) :=
  fun _ hz => (lowerLambertW_continuousAt hz).continuousWithinAt

/-- Continuity of the lower branch on the full endpoint-inclusive natural
domain `[-exp (-1), 0)`. -/
theorem lowerLambertW_continuousOn_Ico :
    ContinuousOn lowerLambertW (Ico (-Real.exp (-1)) 0) := by
  intro z hz
  rcases eq_or_lt_of_le hz.1 with h | h
  · subst z
    exact lowerLambertW_continuousWithinAt_branchPoint
  · exact (lowerLambertW_continuousAt ⟨h, hz.2⟩).continuousWithinAt

/-- Inverse-function derivative of the lower real Lambert branch. -/
theorem lowerLambertW_hasDerivAt {z : ℝ}
    (hz : z ∈ Ioo (-Real.exp (-1)) 0) :
    HasDerivAt lowerLambertW
      (Real.exp (lowerLambertW z) * (lowerLambertW z + 1))⁻¹ z := by
  have hf : HasDerivAt (fun w : ℝ => w * Real.exp w)
      (Real.exp (lowerLambertW z) * (lowerLambertW z + 1))
      (lowerLambertW z) := by
    have h0 := (hasDerivAt_id (lowerLambertW z)).mul
      (Real.hasDerivAt_exp (lowerLambertW z))
    have hfun : (fun w : ℝ => w * Real.exp w) =ᶠ[𝓝 (lowerLambertW z)]
        (id * Real.exp) :=
      Eventually.of_forall fun w => by simp only [Pi.mul_apply, id_eq]
    exact (h0.congr_of_eventuallyEq hfun).congr_deriv (by
      simp only [id_eq]
      ring_nf)
  have hW := lowerLambertW_lt_neg_one hz
  have hderiv : Real.exp (lowerLambertW z) * (lowerLambertW z + 1) ≠ 0 :=
    mul_ne_zero (Real.exp_ne_zero _) (by linarith)
  have hinverse : ∀ᶠ y in 𝓝 z,
      lowerLambertW y * Real.exp (lowerLambertW y) = y := by
    filter_upwards [isOpen_Ioo.mem_nhds hz] with y hy
    exact lowerLambertW_mul_exp hy
  exact hf.of_local_left_inverse
    (lowerLambertW_continuousAt hz) hderiv hinverse

/-- Standard quotient formula for the derivative of the lower real Lambert
branch. -/
theorem deriv_lowerLambertW {z : ℝ}
    (hz : z ∈ Ioo (-Real.exp (-1)) 0) :
    deriv lowerLambertW z =
      lowerLambertW z / (z * (1 + lowerLambertW z)) := by
  rw [(lowerLambertW_hasDerivAt hz).deriv]
  have hW0 : lowerLambertW z ≠ 0 := by
    linarith [lowerLambertW_lt_neg_one hz]
  have hW1 : lowerLambertW z + 1 ≠ 0 := by
    linarith [lowerLambertW_lt_neg_one hz]
  calc
    (Real.exp (lowerLambertW z) * (lowerLambertW z + 1))⁻¹ =
        lowerLambertW z /
          ((lowerLambertW z * Real.exp (lowerLambertW z)) *
            (lowerLambertW z + 1)) := by
      field_simp [hW0, hW1, Real.exp_ne_zero]
    _ = lowerLambertW z / (z * (1 + lowerLambertW z)) := by
      rw [lowerLambertW_mul_exp hz, add_comm]

/-- The derivative of the lower real Lambert branch is strictly negative on
the smooth interior of its natural domain. -/
theorem deriv_lowerLambertW_neg {z : ℝ}
    (hz : z ∈ Ioo (-Real.exp (-1)) 0) :
    deriv lowerLambertW z < 0 := by
  rw [(lowerLambertW_hasDerivAt hz).deriv]
  rw [inv_lt_zero]
  exact mul_neg_of_pos_of_neg (Real.exp_pos _) (by
    linarith [lowerLambertW_lt_neg_one hz])

/-- The continuous stationary point displayed in equation (9) of the draft. -/
noncomputable def paperLambertN (x : ℝ) : ℝ :=
  -lowerLambertW (-(Real.log 2 * x)) / Real.log 2

/-- Endpoint-inclusive equation (9): the displayed closed form solves
`n * 2⁻ⁿ = x` throughout the full lower-branch domain. -/
theorem paperLambertN_eq9_of_le {x : ℝ} (hx : 0 < x)
    (hsmall : Real.log 2 * x ≤ Real.exp (-1)) :
    paperLambertN x * (2 : ℝ) ^ (-paperLambertN x) = x := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hz : -(Real.log 2 * x) ∈ Ico (-Real.exp (-1)) 0 := by
    constructor <;> linarith [mul_pos hlog2 hx]
  have hW := lowerLambertW_mul_exp_of_mem_Ico hz
  rw [paperLambertN, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [show Real.log 2 * (-(-lowerLambertW (-(Real.log 2 * x)) / Real.log 2)) =
      lowerLambertW (-(Real.log 2 * x)) by field_simp]
  field_simp
  linarith

/-- Repaired equation (9): on the interior lower-branch domain, the displayed
closed form solves `n * 2⁻ⁿ = x`. -/
theorem paperLambertN_eq9 {x : ℝ} (hx : 0 < x)
    (hsmall : Real.log 2 * x < Real.exp (-1)) :
    paperLambertN x * (2 : ℝ) ^ (-paperLambertN x) = x :=
  paperLambertN_eq9_of_le hx hsmall.le

/-- On the full lower-branch domain, the paper's stationary point lies at or
beyond the turning value `1 / log 2`. -/
theorem one_div_log_two_le_paperLambertN {x : ℝ} (hx : 0 < x)
    (hsmall : Real.log 2 * x ≤ Real.exp (-1)) :
    1 / Real.log 2 ≤ paperLambertN x := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hz : -(Real.log 2 * x) ∈ Ico (-Real.exp (-1)) 0 := by
    constructor <;> linarith [mul_pos hlog2 hx]
  unfold paperLambertN
  exact (div_le_div_iff_of_pos_right hlog2).2 (by
    linarith [lowerLambertW_le_neg_one hz])

/-- At the branch-point input, the stationary point attains its sharp lower
bound. -/
theorem paperLambertN_eq_one_div_log_two {x : ℝ}
    (hx : Real.log 2 * x = Real.exp (-1)) :
    paperLambertN x = 1 / Real.log 2 := by
  rw [paperLambertN, hx, lowerLambertW_branchPoint]
  ring

/-- The paper's stationary point equals the turning value exactly at the
Lambert branch point. -/
theorem paperLambertN_eq_one_div_log_two_iff {x : ℝ} (hx : 0 < x)
    (hsmall : Real.log 2 * x ≤ Real.exp (-1)) :
    paperLambertN x = 1 / Real.log 2 ↔
      Real.log 2 * x = Real.exp (-1) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hz : -(Real.log 2 * x) ∈ Ico (-Real.exp (-1)) 0 := by
    constructor <;> linarith [mul_pos hlog2 hx]
  constructor
  · intro hphase
    have hW : lowerLambertW (-(Real.log 2 * x)) = -1 := by
      unfold paperLambertN at hphase
      rw [div_left_inj' hlog2.ne'] at hphase
      linarith
    have hdef := lowerLambertW_mul_exp_of_mem_Ico hz
    rw [hW] at hdef
    norm_num at hdef
    linarith
  · intro hbranch
    exact paperLambertN_eq_one_div_log_two hbranch

/-- In the interior lower-branch domain, the paper's stationary point lies
strictly beyond the turning value `1 / log 2`. -/
theorem one_div_log_two_lt_paperLambertN {x : ℝ} (hx : 0 < x)
    (hsmall : Real.log 2 * x < Real.exp (-1)) :
    1 / Real.log 2 < paperLambertN x := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hz : -(Real.log 2 * x) ∈ Ioo (-Real.exp (-1)) 0 := by
    constructor <;> linarith [mul_pos hlog2 hx]
  unfold paperLambertN
  exact (div_lt_div_iff_of_pos_right hlog2).2 (by
    linarith [lowerLambertW_lt_neg_one hz])

/-! ### The map `z ↦ z - log z` on `(1, ∞)`

The near-zero bracket proved below is really a statement about the *inverse*
of `φ(z) = z - log z`, which is strictly increasing on `(1, ∞)`.  Writing
`y = -W₋₁(x) > 1`, the defining equation `W e^W = x` becomes `y·e^{-y} = -x`,
that is `y - log y = η` with `η = log (1 / (-x))`.  Then

* `y > η + log η`, because `y > η` forces `log y > log η`; and
* `y ≤ B := η + η·log η / (η - 1)`, because `log B ≤ log η + (B - η)/η`
  shows `φ(B) ≥ η = φ(y)`, and `φ` is monotone.

Neither step mentions Lambert's function, so the bracket is proved for an
arbitrary `y > 1` and `η = φ(y)` in `Fabius.SubLog`, and only then read off
for `W₋₁` through `lowerLambertW_mul_exp`.  Stated this way it applies to any
quantity known only through an equation `y - log y = η` — which is how the
lower branch enters the dyadic saddle-point analysis elsewhere in this
library. -/

namespace SubLog

/-- `z ↦ z - log z` is strictly increasing on `[1, ∞)`: its derivative
`1 - 1/z` is positive for `z > 1`. -/
theorem strictMonoOn_sub_log : StrictMonoOn (fun z : ℝ => z - Real.log z) (Ici 1) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici 1) ?_ ?_
  · exact (continuousOn_id.sub (Real.continuousOn_log.mono fun z hz =>
      by simp only [mem_Ici, mem_compl_iff, mem_singleton_iff] at hz ⊢; linarith))
  · intro z hz
    rw [interior_Ici, mem_Ioi] at hz
    have hz0 : z ≠ 0 := by linarith
    have hd : HasDerivAt (fun z : ℝ => z - Real.log z) (1 - z⁻¹) z :=
      (hasDerivAt_id z).sub (Real.hasDerivAt_log hz0)
    rw [hd.deriv]
    have : z⁻¹ < 1 := inv_lt_one_of_one_lt₀ hz
    linarith

/-- A point `y > 1` with `y - log y = η` lies strictly above `η + log η`. -/
theorem lt_of_sub_log_eq {y η : ℝ} (hy : 1 < y) (h : y - Real.log y = η) :
    η + Real.log η < y := by
  have hlog : 0 < Real.log y := Real.log_pos hy
  have hη : η < y := by linarith
  have hη1 : 1 < η := by
    -- `η = y - log y` and `log y < y - 1`
    have := Real.log_lt_sub_one_of_pos (by linarith : 0 < y) hy.ne'
    linarith
  have := Real.log_lt_log (by linarith) hη
  linarith

/-- A point `y > 1` with `y - log y = η` lies at most at
`η + η·log η / (η - 1)`. -/
theorem le_of_sub_log_eq {y η : ℝ} (hy : 1 < y) (h : y - Real.log y = η) :
    y ≤ η + η * Real.log η / (η - 1) := by
  have hη1 : 1 < η := by
    have := Real.log_lt_sub_one_of_pos (by linarith : 0 < y) hy.ne'
    linarith
  have hη0 : 0 < η := by linarith
  have hlogη : 0 < Real.log η := Real.log_pos hη1
  set r := η * Real.log η / (η - 1) with hr
  have hr0 : 0 < r := by positivity
  -- `log (η + r) ≤ log η + r/η`, from `log (1 + s) ≤ s` at `s = r/η`
  have hlogB : Real.log (η + r) ≤ Real.log η + r / η := by
    have hs : 0 < 1 + r / η := by positivity
    have h1 : Real.log (η + r) = Real.log η + Real.log (1 + r / η) := by
      rw [← Real.log_mul hη0.ne' hs.ne']
      congr 1
      field_simp
    have h2 : Real.log (1 + r / η) ≤ r / η := by
      linarith [Real.log_le_sub_one_of_pos hs]
    linarith
  -- and `r/η = log η / (η - 1)`, so `log η + r/η = r`
  have hrη : Real.log η + r / η = r := by
    have hne : η - 1 ≠ 0 := by linarith
    rw [hr]
    field_simp
    ring
  -- hence `φ(η + r) ≥ η = φ(y)`, and `φ` is increasing on `[1, ∞)`
  have hφB : η ≤ (η + r) - Real.log (η + r) := by linarith
  refine le_of_not_gt fun hcon => ?_
  have hmono := strictMonoOn_sub_log (mem_Ici.mpr (by linarith : (1 : ℝ) ≤ η + r))
    (mem_Ici.mpr hy.le) hcon
  simp only at hmono
  linarith

/-- **The bracket for the inverse of `z - log z`.**  If `y > 1` and
`y - log y = η`, then `η + log η < y ≤ η + η·log η / (η - 1)`. -/
theorem bracket_of_sub_log_eq {y η : ℝ} (hy : 1 < y) (h : y - Real.log y = η) :
    η + Real.log η < y ∧ y ≤ η + η * Real.log η / (η - 1) :=
  ⟨lt_of_sub_log_eq hy h, le_of_sub_log_eq hy h⟩

end SubLog

/-! ### The lower branch near zero -/

/-- On `(-1/e, 0)`, the lower branch satisfies `y - log y = log (1 / (-x))`
with `y = -W₋₁(x)`: the defining equation read through `y·e^{-y} = -x`. -/
theorem neg_lowerLambertW_sub_log_eq {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    -lowerLambertW x - Real.log (-lowerLambertW x) = Real.log (1 / (-x)) := by
  have hW := lowerLambertW_mul_exp hx
  have hWneg : lowerLambertW x < -1 := lowerLambertW_lt_neg_one hx
  have hy : 0 < -lowerLambertW x := by linarith
  have hx0 : 0 < -x := by linarith [hx.2]
  -- `-x = (-W) · exp W`, so `log (-x) = log (-W) + W`
  have hprod : -x = (-lowerLambertW x) * Real.exp (lowerLambertW x) := by linarith
  have hlog : Real.log (-x) = Real.log (-lowerLambertW x) + lowerLambertW x := by
    rw [hprod, Real.log_mul hy.ne' (Real.exp_pos _).ne', Real.log_exp]
  rw [one_div, Real.log_inv, hlog]
  ring

/-- **Near-zero logarithmic bounds, upper half.**  For `-1/e < x < 0` and
`η = log (1 / (-x))`, `W₋₁(x) < -η - log η`. -/
theorem lowerLambertW_lt_neg_log_sub {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    lowerLambertW x <
      -Real.log (1 / (-x)) - Real.log (Real.log (1 / (-x))) := by
  have hy : 1 < -lowerLambertW x := by linarith [lowerLambertW_lt_neg_one hx]
  have := SubLog.lt_of_sub_log_eq hy (neg_lowerLambertW_sub_log_eq hx)
  linarith

/-- **Near-zero logarithmic bounds, lower half.**  For `-1/e < x < 0` and
`η = log (1 / (-x))`, `-η - η·log η / (η - 1) ≤ W₋₁(x)`. -/
theorem neg_log_sub_div_le_lowerLambertW {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    -Real.log (1 / (-x)) -
        Real.log (1 / (-x)) * Real.log (Real.log (1 / (-x))) / (Real.log (1 / (-x)) - 1) ≤
      lowerLambertW x := by
  have hy : 1 < -lowerLambertW x := by linarith [lowerLambertW_lt_neg_one hx]
  have := SubLog.le_of_sub_log_eq hy (neg_lowerLambertW_sub_log_eq hx)
  linarith

/-- **The two-sided near-zero bracket** for the lower branch, in the guide's
form: with `η = log (1 / (-x)) > 1`,
`-η - η·log η / (η - 1) ≤ W₋₁(x) < -η - log η`. -/
theorem lowerLambertW_near_zero_bounds {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    -Real.log (1 / (-x)) -
        Real.log (1 / (-x)) * Real.log (Real.log (1 / (-x))) / (Real.log (1 / (-x)) - 1) ≤
      lowerLambertW x ∧
    lowerLambertW x < -Real.log (1 / (-x)) - Real.log (Real.log (1 / (-x))) :=
  ⟨neg_log_sub_div_le_lowerLambertW hx, lowerLambertW_lt_neg_log_sub hx⟩

/-- The auxiliary quantity `η = log (1 / (-x))` exceeds `1` on `(-1/e, 0)`. -/
theorem one_lt_log_one_div_neg {x : ℝ} (hx : x ∈ Ioo (-Real.exp (-1)) 0) :
    1 < Real.log (1 / (-x)) := by
  have hx0 : 0 < -x := by linarith [hx.2]
  have hlt : -x < Real.exp (-1) := by linarith [hx.1]
  rw [one_div, Real.log_inv]
  have := Real.log_lt_log hx0 hlt
  rw [Real.log_exp] at this
  linarith

/-! ### The two-term expansion at the singularity

Everything below is the bracket of `lowerLambertW_near_zero_bounds` rewritten
in the coordinate `eps = -x`, where `η = log (1 / (-x))` becomes `-log eps`.
The upper endpoint of the bracket is exactly `log eps - log |log eps|`, and
the lower endpoint sits `log η / (η - 1)` below it, so the two-term expansion
and its rate are read off the bracket rather than proved again. -/

-- The bracket's width, in the normalization used below:
-- `log η - η·log η/(η - 1) = -(log η/(η - 1))`.
private lemma remainder_bracket {y η : ℝ} (hη : 1 < η)
    (hlow : -η - η * Real.log η / (η - 1) ≤ y) (hupp : y < -η - Real.log η) :
    -(Real.log η / (η - 1)) ≤ y - (-η - Real.log η) ∧
      y - (-η - Real.log η) < 0 := by
  have hne : η - 1 ≠ 0 := by linarith
  have hsplit : η * Real.log η / (η - 1) = Real.log η + Real.log η / (η - 1) := by
    have hnum : η * Real.log η = (η - 1) * Real.log η + Real.log η := by ring
    rw [hnum, add_div, mul_div_cancel_left₀ (Real.log η) hne]
  rw [hsplit] at hlow
  exact ⟨by linarith, by linarith⟩

private lemma one_lt_neg_log {eps : ℝ} (heps : eps ∈ Ioo 0 (Real.exp (-1))) :
    1 < -Real.log eps := by
  have h := Real.log_lt_log heps.1 heps.2
  rw [Real.log_exp] at h
  linarith

-- The near-zero bracket in the coordinate `eps`, centred at the two-term
-- expansion `log eps - log |log eps|`.
private lemma lowerLambertW_expansion_bracket {eps : ℝ}
    (heps : eps ∈ Ioo 0 (Real.exp (-1))) :
    -(Real.log (-Real.log eps) / (-Real.log eps - 1)) ≤
        lowerLambertW (-eps) - (Real.log eps - Real.log |Real.log eps|) ∧
      lowerLambertW (-eps) - (Real.log eps - Real.log |Real.log eps|) < 0 := by
  have hx : (-eps) ∈ Ioo (-Real.exp (-1)) 0 :=
    ⟨by linarith [heps.2], by linarith [heps.1]⟩
  have hEta1 := one_lt_neg_log heps
  have hlogneg : Real.log eps < 0 := by linarith
  have hEtaEq : Real.log (1 / (-(-eps))) = -Real.log eps := by
    rw [neg_neg, one_div, Real.log_inv]
  have hrewrite : Real.log eps - Real.log |Real.log eps|
      = -(-Real.log eps) - Real.log (-Real.log eps) := by
    rw [abs_of_neg hlogneg]
    ring
  have hlow := neg_log_sub_div_le_lowerLambertW hx
  have hupp := lowerLambertW_lt_neg_log_sub hx
  rw [hEtaEq] at hlow hupp
  rw [hrewrite]
  exact remainder_bracket hEta1 hlow hupp

/-- The lower Lambert branch diverges to negative infinity as its negative
argument approaches zero: `W₋₁(-eps) → -∞` as `eps ↓0`.

This is the upper half of the near-zero bracket alone: `W₋₁(-eps)` stays
below `log eps - log (-log eps) < log eps → -∞`. -/
theorem tendsto_lowerLambertW_neg_nhdsGT_zero_atBot :
    Tendsto (fun eps : ℝ ↦ lowerLambertW (-eps))
      (nhdsWithin (0 : ℝ) (Ioi 0)) atBot := by
  have hEta : Tendsto (fun eps : ℝ => -Real.log eps)
      (nhdsWithin (0 : ℝ) (Ioi 0)) atTop :=
    tendsto_neg_atTop_iff.mpr Real.tendsto_log_nhdsGT_zero
  have hbound : ∀ᶠ eps : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      -Real.log eps ≤ -(lowerLambertW (-eps)) := by
    filter_upwards [Ioo_mem_nhdsGT (Real.exp_pos (-1))] with eps heps
    have hEta1 := one_lt_neg_log heps
    have hlogneg : Real.log eps < 0 := by linarith
    have habs : Real.log |Real.log eps| = Real.log (-Real.log eps) := by
      rw [abs_of_neg hlogneg]
    have hupp := (lowerLambertW_expansion_bracket heps).2
    rw [habs] at hupp
    have hlogpos : 0 < Real.log (-Real.log eps) := Real.log_pos hEta1
    linarith
  have hneg : Tendsto (fun eps : ℝ ↦ -(lowerLambertW (-eps)))
      (nhdsWithin (0 : ℝ) (Ioi 0)) atTop :=
    tendsto_atTop_mono' _ hbound hEta
  exact tendsto_neg_atTop_iff.mp hneg

/-- **Explicit rate in the two-term expansion of the lower branch.**  For
`0 < eps < 1/e` and `η = -log eps > 1`,

`|W₋₁(-eps) - (log eps - log |log eps|)| ≤ log η / (η - 1)`.

The error is in fact confined to the half-open interval
`[-log η / (η - 1), 0)`: this is nothing but `lowerLambertW_near_zero_bounds`
recentred at the upper endpoint of the bracket, whose distance to the lower
endpoint is `η·log η/(η - 1) - log η = log η/(η - 1)`. -/
theorem abs_lowerLambertW_expansion_le {eps : ℝ}
    (heps : eps ∈ Ioo 0 (Real.exp (-1))) :
    |lowerLambertW (-eps) - (Real.log eps - Real.log |Real.log eps|)| ≤
      Real.log (-Real.log eps) / (-Real.log eps - 1) := by
  obtain ⟨hlow, hupp⟩ := lowerLambertW_expansion_bracket heps
  rw [abs_of_nonpos hupp.le]
  linarith

-- `log t / (t - 1) ≤ 2 · log t / t` for `t ≥ 2`, since then `t/2 ≤ t - 1`.
private lemma log_div_sub_one_le {t : ℝ} (ht : 2 ≤ t) :
    Real.log t / (t - 1) ≤ 2 * (Real.log t / t) := by
  have hlog : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  have h1 : Real.log t / (t - 1) ≤ Real.log t / (t / 2) :=
    div_le_div_of_nonneg_left hlog (by linarith) (by linarith)
  have h2 : Real.log t / (t / 2) = 2 * (Real.log t / t) := by
    rw [div_div_eq_mul_div]
    ring
  rwa [h2] at h1

/-- **The two-term expansion of the lower branch, with its rate.**  With
`η = -log eps`, the error of `W₋₁(-eps) = log eps - log |log eps| + o(1)` is
`O(log η / η)` as `eps ↓ 0`.

This is an `eps`-coordinate packaging of `abs_lowerLambertW_expansion_le`,
not new content: the same `O(log/·)` rate for the same remainder is recorded
in the dyadic `t`-coordinate by `dyadicLambertPerturbation_isBigO_log_div`
and `dyadicLambertRefinedRemainder_isBigO`. -/
theorem lowerLambertW_expansion_isBigO :
    (fun eps : ℝ => lowerLambertW (-eps) -
        (Real.log eps - Real.log |Real.log eps|)) =O[nhdsWithin (0 : ℝ) (Ioi 0)]
      (fun eps : ℝ => Real.log (-Real.log eps) / (-Real.log eps)) := by
  have key : ∀ᶠ eps : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      ‖lowerLambertW (-eps) - (Real.log eps - Real.log |Real.log eps|)‖ ≤
        2 * ‖Real.log (-Real.log eps) / (-Real.log eps)‖ := by
    filter_upwards [Ioo_mem_nhdsGT (Real.exp_pos (-2))] with eps heps
    have hle : Real.exp (-2) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by norm_num)
    have hepsDom : eps ∈ Ioo 0 (Real.exp (-1)) := ⟨heps.1, lt_of_lt_of_le heps.2 hle⟩
    have hEta2 : 2 ≤ -Real.log eps := by
      have h := Real.log_lt_log heps.1 heps.2
      rw [Real.log_exp] at h
      linarith
    have hnum : 0 ≤ Real.log (-Real.log eps) := Real.log_nonneg (by linarith)
    have hbound := abs_lowerLambertW_expansion_le hepsDom
    have hcmp := log_div_sub_one_le hEta2
    have habs2 : |Real.log (-Real.log eps) / (-Real.log eps)|
        = Real.log (-Real.log eps) / (-Real.log eps) :=
      abs_of_nonneg (div_nonneg hnum (by linarith))
    simp only [Real.norm_eq_abs]
    linarith
  exact Asymptotics.IsBigO.of_bound 2 key

/-- Standard first two terms of the lower real Lambert branch:
`W₋₁(-eps) = log eps - log |log eps| + o(1)` as `eps ↓ 0`.

The `o(1)` is the qualitative shadow of `lowerLambertW_expansion_isBigO`:
the majorant `log η / η` tends to `0` because `η = -log eps → ∞`. -/
theorem tendsto_lowerLambertW_expansion :
    Tendsto
      (fun eps : ℝ => lowerLambertW (-eps) -
        (Real.log eps - Real.log |Real.log eps|))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
  have hEta : Tendsto (fun eps : ℝ => -Real.log eps)
      (nhdsWithin (0 : ℝ) (Ioi 0)) atTop :=
    tendsto_neg_atTop_iff.mpr Real.tendsto_log_nhdsGT_zero
  have hmaj : Tendsto (fun eps : ℝ => Real.log (-Real.log eps) / (-Real.log eps))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
    change Tendsto ((fun t : ℝ => Real.log t / t) ∘ (fun eps : ℝ => -Real.log eps))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0)
    exact Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hEta
  exact lowerLambertW_expansion_isBigO.trans_tendsto hmaj

end

end Fabius
