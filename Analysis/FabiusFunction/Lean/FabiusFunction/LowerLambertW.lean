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
derivative API uses the smooth interior `(-exp(-1), 0)`.  It also proves the
standard first two terms of the branch's positive-side asymptotic expansion.
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

/-- A totalized definition of the lower real Lambert branch.  Its intended
domain is `(-exp (-1), 0)`. -/
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

/-- On its natural domain, the lower branch is strictly below `-1`. -/
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

/-- Exact range of the lower real Lambert branch on its natural domain. -/
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

/-- The lower real Lambert branch is continuous at every point of its natural
domain. -/
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

/-- Continuity of the lower real Lambert branch on its natural domain. -/
theorem lowerLambertW_continuousOn :
    ContinuousOn lowerLambertW (Ioo (-Real.exp (-1)) 0) :=
  fun _ hz => (lowerLambertW_continuousAt hz).continuousWithinAt

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
its natural domain. -/
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

private def mulExpNeg (y : ℝ) : ℝ := y * Real.exp (-y)

private lemma mulExpNeg_strictAntiOn : StrictAntiOn mulExpNeg (Ici (1 : ℝ)) := by
  intro a ha b hb hab
  have heba : Real.exp (-b) < Real.exp (-a) := Real.exp_lt_exp.2 (neg_lt_neg hab)
  have hea : Real.exp (-a) ∈ Icc (0 : ℝ) (Real.exp (-1)) := by
    exact ⟨(Real.exp_pos _).le, Real.exp_le_exp.2 (neg_le_neg ha)⟩
  have heb : Real.exp (-b) ∈ Icc (0 : ℝ) (Real.exp (-1)) := by
    exact ⟨(Real.exp_pos _).le, Real.exp_le_exp.2 (neg_le_neg hb)⟩
  have h := Real.mul_log_strictAntiOn heb hea heba
  simpa [mulExpNeg, Real.log_exp, mul_comm] using h

private noncomputable def lowerLambertY (eps : ℝ) : ℝ := -lowerLambertW (-eps)

private lemma lowerLambertY_gt_one {eps : ℝ} (heps : eps ∈ Ioo 0 (Real.exp (-1))) :
    1 < lowerLambertY eps := by
  have hz : -eps ∈ Ioo (-Real.exp (-1)) 0 :=
    ⟨neg_lt_neg heps.2, neg_lt_zero.2 heps.1⟩
  simpa [lowerLambertY] using neg_lt_neg (lowerLambertW_lt_neg_one hz)

private lemma lowerLambertY_mul_exp_neg {eps : ℝ}
    (heps : eps ∈ Ioo 0 (Real.exp (-1))) :
    mulExpNeg (lowerLambertY eps) = eps := by
  have hz : -eps ∈ Ioo (-Real.exp (-1)) 0 :=
    ⟨by linarith [heps.2], by linarith [heps.1]⟩
  have h := lowerLambertW_mul_exp hz
  simpa [lowerLambertY, mulExpNeg] using congrArg Neg.neg h

private theorem tendsto_lowerLambertY_nhdsGT_zero_atTop :
    Tendsto lowerLambertY (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by
  refine tendsto_atTop.2 ?_
  intro B
  let A : ℝ := max B 1 + 1
  have hA1 : 1 < A := by
    dsimp [A]
    linarith [le_max_right B 1]
  have hdelta : 0 < mulExpNeg A := by
    exact mul_pos (lt_trans zero_lt_one hA1) (Real.exp_pos _)
  have hcut : 0 < min (Real.exp (-1)) (mulExpNeg A) :=
    lt_min (Real.exp_pos _) hdelta
  filter_upwards [Ioo_mem_nhdsGT hcut] with eps heps
  have hepsDomain : eps ∈ Ioo 0 (Real.exp (-1)) :=
    ⟨heps.1, heps.2.trans_le (min_le_left _ _)⟩
  have hy1 : 1 < lowerLambertY eps := lowerLambertY_gt_one hepsDomain
  by_contra hnot
  have hyB : lowerLambertY eps < B := lt_of_not_ge hnot
  have hBA : B < A := by
    dsimp [A]
    linarith [le_max_left B 1]
  have hyA : lowerLambertY eps < A := hyB.trans hBA
  have hanti := mulExpNeg_strictAntiOn hy1.le hA1.le hyA
  rw [lowerLambertY_mul_exp_neg hepsDomain] at hanti
  exact (not_lt_of_ge (le_of_lt (heps.2.trans_le (min_le_right _ _)))) hanti

private lemma log_eq_log_lowerLambertY_sub {eps : ℝ}
    (heps : eps ∈ Ioo 0 (Real.exp (-1))) :
    Real.log eps = Real.log (lowerLambertY eps) - lowerLambertY eps := by
  have hy : 0 < lowerLambertY eps :=
    zero_lt_one.trans (lowerLambertY_gt_one heps)
  have hlog := congrArg Real.log (lowerLambertY_mul_exp_neg heps)
  rw [mulExpNeg, Real.log_mul hy.ne' (Real.exp_ne_zero _), Real.log_exp] at hlog
  linarith

private lemma neg_log_div_lowerLambertY {eps : ℝ}
    (heps : eps ∈ Ioo 0 (Real.exp (-1))) :
    -Real.log eps / lowerLambertY eps =
      1 - Real.log (lowerLambertY eps) / lowerLambertY eps := by
  rw [log_eq_log_lowerLambertY_sub heps]
  have hy : lowerLambertY eps ≠ 0 :=
    (zero_lt_one.trans (lowerLambertY_gt_one heps)).ne'
  field_simp
  ring

private lemma lowerLambertW_expansion_remainder_eq {eps : ℝ}
    (heps : eps ∈ Ioo 0 (Real.exp (-1))) :
    lowerLambertW (-eps) -
        (Real.log eps - Real.log |Real.log eps|) =
      Real.log ((-Real.log eps) / lowerLambertY eps) := by
  have heps1 : eps < 1 := heps.2.trans (Real.exp_lt_one_iff.2 (by norm_num))
  have hlogneg : Real.log eps < 0 := Real.log_neg heps.1 heps1
  have hL : 0 < -Real.log eps := neg_pos.2 hlogneg
  have hy : 0 < lowerLambertY eps :=
    zero_lt_one.trans (lowerLambertY_gt_one heps)
  rw [Real.log_div hL.ne' hy.ne', abs_of_neg hlogneg]
  have hW : lowerLambertW (-eps) = -lowerLambertY eps := by
    simp [lowerLambertY]
  rw [hW, log_eq_log_lowerLambertY_sub heps]
  ring

/-- Standard first two terms of the lower real Lambert branch:
`W₋₁(-eps) = log eps - log |log eps| + o(1)` as `eps ↓ 0`. -/
theorem tendsto_lowerLambertW_expansion :
    Tendsto
      (fun eps : ℝ => lowerLambertW (-eps) -
        (Real.log eps - Real.log |Real.log eps|))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
  have hlogOverY :
      Tendsto
        (fun eps : ℝ => Real.log (lowerLambertY eps) / lowerLambertY eps)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
    change Tendsto ((fun x : ℝ => Real.log x / x) ∘ lowerLambertY)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0)
    exact Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
      tendsto_lowerLambertY_nhdsGT_zero_atTop
  have hbase :
      Tendsto
        (fun eps : ℝ => 1 - Real.log (lowerLambertY eps) / lowerLambertY eps)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 1) := by
    simpa using (tendsto_const_nhds.sub hlogOverY :
      Tendsto
        (fun eps : ℝ => 1 - Real.log (lowerLambertY eps) / lowerLambertY eps)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (1 - 0)))
  have hdomain : ∀ᶠ eps : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      eps ∈ Ioo 0 (Real.exp (-1)) :=
    Ioo_mem_nhdsGT (Real.exp_pos _)
  have hratio :
      Tendsto (fun eps : ℝ => (-Real.log eps) / lowerLambertY eps)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 1) := by
    exact hbase.congr' <| by
      filter_upwards [hdomain] with eps heps
      exact (neg_log_div_lowerLambertY heps).symm
  have hlogRatio :
      Tendsto (fun eps : ℝ =>
        Real.log ((-Real.log eps) / lowerLambertY eps))
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
    simpa using hratio.log one_ne_zero
  exact hlogRatio.congr' <| by
    filter_upwards [hdomain] with eps heps
    exact (lowerLambertW_expansion_remainder_eq heps).symm

end

end Fabius
