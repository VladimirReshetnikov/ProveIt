import Surreal.Surcomplex.TrigonometricFineDerivative
import Surreal.Surcomplex.FiniteTrigonometryIdentities
import Surreal.Foundations.SignSequenceAnalyticStrictSign
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Signs, monotonicity and inequalities of finite surreal trigonometry

The strict analytic sign-lifting theorem supplies the signs in
`trigonometry:prop:order`, including infinitesimal endpoint displacements.
Sum-to-product identities then give strict monotonicity directly, without
inferring global monotonicity from fine derivatives.
Lifting ordinary analytic inequalities proves Jordan's bounds, the absolute
sine bound and the strict sine/input/tangent comparison.
-/

universe u

namespace Surreal.Surcomplex

open Foundations

/-- Sine is strictly positive between zero and the embedded ordinary pi. -/
theorem finiteSin_pos_of_mem_Ioo (θ : SignSequence.FiniteElement.{u})
    (hθ : θ.val ∈ Set.Ioo 0 (SignSequence.ofReal Real.pi)) : 0 < finiteSin θ := by
  have h := SignSequence.analyticLiftFunction_pos_of_mem_Ioo Real.sin 0 Real.pi
    (fun _ _ => Real.analyticAt_sin) (fun _ hx => Real.sin_pos_of_mem_Ioo hx) θ.val
    (by simpa only [map_zero] using hθ)
  change 0 < sinFunction θ.val at h
  rwa [sinFunction_eq_finiteSin] at h

/-- Cosine is strictly positive on the central open half-period. -/
theorem finiteCos_pos_of_mem_Ioo (θ : SignSequence.FiniteElement.{u})
    (hθ : θ.val ∈ Set.Ioo (SignSequence.ofReal (-(Real.pi / 2)))
      (SignSequence.ofReal (Real.pi / 2))) : 0 < finiteCos θ := by
  have h := SignSequence.analyticLiftFunction_pos_of_mem_Ioo Real.cos (-(Real.pi / 2)) (Real.pi / 2)
    (fun _ _ => Real.analyticAt_cos) (fun _ hx => Real.cos_pos_of_mem_Ioo hx) θ.val hθ
  change 0 < cosFunction θ.val at h
  rwa [cosFunction_eq_finiteCos] at h

/-- Sine is strictly negative on the second open half-period. -/
theorem finiteSin_neg_of_mem_Ioo (θ : SignSequence.FiniteElement.{u})
    (hθ : θ.val ∈ Set.Ioo (SignSequence.ofReal Real.pi)
      (SignSequence.ofReal (2 * Real.pi))) : finiteSin θ < 0 := by
  have h := SignSequence.analyticLiftFunction_pos_of_mem_Ioo (-Real.sin) Real.pi (2 * Real.pi)
    (fun _ _ => Real.analyticAt_sin.neg) (by
      intro y hy
      have hs := Real.sin_pos_of_pos_of_lt_pi (x := y - Real.pi)
        (by linarith [hy.1]) (by linarith [hy.2])
      have he : Real.sin y = -Real.sin (y - Real.pi) := by
        simpa only [sub_add_cancel] using Real.sin_add_pi (y - Real.pi)
      simpa only [Pi.neg_apply, he, neg_neg] using hs) θ.val hθ
  rw [SignSequence.analyticLiftFunction_neg _ _ θ.property Real.analyticAt_sin] at h
  change 0 < -sinFunction θ.val at h
  rw [sinFunction_eq_finiteSin, neg_pos] at h
  exact h

/-- Cosine is strictly decreasing on the actual closed interval from zero to pi. -/
theorem finiteCos_strictAntiOn : StrictAntiOn finiteCos
    {θ : SignSequence.FiniteElement.{u} | θ.val ∈ Set.Icc 0 (SignSequence.ofReal Real.pi)} := by
  intro α hα β hβ hab
  have hab' : α.val < β.val := hab
  have hs : 0 < finiteSin (finiteHalf (β + α)) := by
    apply finiteSin_pos_of_mem_Ioo
    rw [val_finiteHalf]
    change 0 < (β.val + α.val) / 2 ∧ (β.val + α.val) / 2 < SignSequence.ofReal Real.pi
    constructor <;> linarith [hα.1, hα.2, hβ.1, hβ.2]
  have hd : 0 < finiteSin (finiteHalf (β - α)) := by
    apply finiteSin_pos_of_mem_Ioo
    rw [val_finiteHalf]
    change 0 < (β.val - α.val) / 2 ∧ (β.val - α.val) / 2 < SignSequence.ofReal Real.pi
    constructor <;> linarith [hα.1, hα.2, hβ.1, hβ.2]
  apply sub_neg.mp
  rw [finiteCos_sub_finiteCos]
  exact mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos (by norm_num) hs) hd

/-- Sine is strictly increasing on the actual central closed half-period. -/
theorem finiteSin_strictMonoOn : StrictMonoOn finiteSin
    {θ : SignSequence.FiniteElement.{u} | θ.val ∈ Set.Icc
      (SignSequence.ofReal (-(Real.pi / 2))) (SignSequence.ofReal (Real.pi / 2))} := by
  intro α hα β hβ hab
  have hab' : α.val < β.val := hab
  have hp : (0 : SignSequence.{u}) < SignSequence.ofReal Real.pi := by
    simpa only [map_zero] using SignSequence.ofReal_strictMono Real.pi_pos
  simp only [map_neg, map_div₀, map_ofNat] at hα hβ
  have hc : 0 < finiteCos (finiteHalf (β + α)) := by
    apply finiteCos_pos_of_mem_Ioo
    simp only [Set.mem_Ioo, map_neg, map_div₀, map_ofNat]
    rw [val_finiteHalf]
    change -(SignSequence.ofReal Real.pi / 2) < (β.val + α.val) / 2 ∧
      (β.val + α.val) / 2 < SignSequence.ofReal Real.pi / 2
    constructor <;> linarith [hα.1, hα.2, hβ.1, hβ.2]
  have hs : 0 < finiteSin (finiteHalf (β - α)) := by
    apply finiteSin_pos_of_mem_Ioo
    rw [val_finiteHalf]
    change 0 < (β.val - α.val) / 2 ∧ (β.val - α.val) / 2 < SignSequence.ofReal Real.pi
    constructor <;> linarith [hα.1, hα.2, hβ.1, hβ.2]
  apply sub_pos.mp
  rw [finiteSin_sub_finiteSin]
  exact mul_pos (mul_pos (by norm_num) hc) hs

/-- Jordan's lower and upper bounds hold throughout the actual closed quarter-period. -/
theorem finiteSin_jordan (θ : SignSequence.FiniteElement.{u})
    (hθ : θ.val ∈ Set.Icc 0 (SignSequence.ofReal (Real.pi / 2))) :
    2 * θ.val / SignSequence.ofReal Real.pi ≤ finiteSin θ ∧ finiteSin θ ≤ θ.val := by
  have hi : AnalyticAt ℝ (id : ℝ → ℝ) (SignSequence.standardPart θ.val) := analyticAt_id
  have hs : AnalyticAt ℝ Real.sin (SignSequence.standardPart θ.val) := Real.analyticAt_sin
  have hx : θ.val ∈ Set.Icc (SignSequence.ofReal 0) (SignSequence.ofReal (Real.pi / 2)) := by
    simpa only [map_zero] using hθ
  have hupper := SignSequence.analyticLiftFunction_nonneg_of_mem_Icc (id - Real.sin) 0 (Real.pi / 2)
    (fun _ _ => analyticAt_id.sub Real.analyticAt_sin)
    (fun r hr => sub_nonneg.mpr (Real.sin_le hr.1)) θ.val hx
  rw [SignSequence.analyticLiftFunction_sub _ _ _ θ.property hi hs,
    SignSequence.analyticLiftFunction_id _ θ.property] at hupper
  change 0 ≤ θ.val - sinFunction θ.val at hupper
  rw [sinFunction_eq_finiteSin] at hupper
  have hlower := SignSequence.analyticLiftFunction_nonneg_of_mem_Icc
    (Real.sin - (fun _ : ℝ => 2 / Real.pi) * id) 0 (Real.pi / 2)
    (fun _ _ => Real.analyticAt_sin.sub (analyticAt_const.mul analyticAt_id))
    (fun r hr => sub_nonneg.mpr (Real.mul_le_sin hr.1 hr.2)) θ.val hx
  rw [SignSequence.analyticLiftFunction_sub _ _ _ θ.property hs
      (analyticAt_const.mul hi),
    SignSequence.analyticLiftFunction_mul _ _ _ θ.property analyticAt_const hi,
    SignSequence.analyticLiftFunction_const _ _ θ.property,
    SignSequence.analyticLiftFunction_id _ θ.property, map_div₀, map_ofNat] at hlower
  change 0 ≤ sinFunction θ.val - 2 / SignSequence.ofReal Real.pi * θ.val at hlower
  rw [sinFunction_eq_finiteSin] at hlower
  constructor
  · convert sub_nonneg.mp hlower using 1
    ring
  · exact sub_nonneg.mp hupper

/-- The absolute sine bound holds at every finite actual real angle. -/
theorem abs_finiteSin_le_abs (θ : SignSequence.FiniteElement.{u}) :
    |finiteSin θ| ≤ |θ.val| := by
  have hi : AnalyticAt ℝ (id : ℝ → ℝ) (SignSequence.standardPart θ.val) := analyticAt_id
  have hs : AnalyticAt ℝ Real.sin (SignSequence.standardPart θ.val) := Real.analyticAt_sin
  have h := SignSequence.analyticLiftFunction_nonneg (id * id - Real.sin * Real.sin)
    (fun _ => (analyticAt_id.mul analyticAt_id).sub (Real.analyticAt_sin.mul Real.analyticAt_sin))
    (fun r => by
      change 0 ≤ r * r - Real.sin r * Real.sin r
      simpa only [pow_two] using sub_nonneg.mpr (Real.sin_sq_le_sq (x := r))) θ.val θ.property
  rw [SignSequence.analyticLiftFunction_sub _ _ _ θ.property (hi.mul hi) (hs.mul hs),
    SignSequence.analyticLiftFunction_mul _ _ _ θ.property hi hi,
    SignSequence.analyticLiftFunction_mul _ _ _ θ.property hs hs,
    SignSequence.analyticLiftFunction_id _ θ.property] at h
  change 0 ≤ θ.val * θ.val - sinFunction θ.val * sinFunction θ.val at h
  rw [sinFunction_eq_finiteSin] at h
  exact (sq_le_sq).mp (by simpa only [pow_two] using sub_nonneg.mp h)

/-- The strict sine and tangent comparison remains valid at infinitesimal endpoint distances. -/
theorem finiteSin_lt_self_lt_finiteTan (θ : SignSequence.FiniteElement.{u})
    (hθ : θ.val ∈ Set.Ioo 0 (SignSequence.ofReal (Real.pi / 2))) :
    0 < finiteSin θ ∧ finiteSin θ < θ.val ∧ θ.val < finiteTan θ := by
  have hp : (0 : SignSequence.{u}) < SignSequence.ofReal Real.pi := by
    simpa only [map_zero] using SignSequence.ofReal_strictMono Real.pi_pos
  have hcθ : 0 < finiteCos θ := by
    apply finiteCos_pos_of_mem_Ioo
    simp only [Set.mem_Ioo, map_neg, map_div₀, map_ofNat] at hθ ⊢
    exact ⟨by linarith [hθ.1], hθ.2⟩
  have hsθ : 0 < finiteSin θ := by
    apply finiteSin_pos_of_mem_Ioo
    simp only [Set.mem_Ioo, map_div₀, map_ofNat] at hθ ⊢
    exact ⟨hθ.1, by linarith [hθ.2]⟩
  have hx : θ.val ∈ Set.Ioo (SignSequence.ofReal 0) (SignSequence.ofReal (Real.pi / 2)) := by
    simpa only [map_zero] using hθ
  have hi : AnalyticAt ℝ (id : ℝ → ℝ) (SignSequence.standardPart θ.val) := analyticAt_id
  have hs : AnalyticAt ℝ Real.sin (SignSequence.standardPart θ.val) := Real.analyticAt_sin
  have hc : AnalyticAt ℝ Real.cos (SignSequence.standardPart θ.val) := Real.analyticAt_cos
  have hsin := SignSequence.analyticLiftFunction_pos_of_mem_Ioo (id - Real.sin) 0 (Real.pi / 2)
    (fun _ _ => analyticAt_id.sub Real.analyticAt_sin)
    (fun r hr => sub_pos.mpr (Real.sin_lt hr.1)) θ.val hx
  rw [SignSequence.analyticLiftFunction_sub _ _ _ θ.property hi hs,
    SignSequence.analyticLiftFunction_id _ θ.property] at hsin
  change 0 < θ.val - sinFunction θ.val at hsin
  rw [sinFunction_eq_finiteSin] at hsin
  have htan := SignSequence.analyticLiftFunction_pos_of_mem_Ioo (Real.sin - id * Real.cos)
    0 (Real.pi / 2) (fun _ _ => Real.analyticAt_sin.sub (analyticAt_id.mul Real.analyticAt_cos))
    (by
      intro r hr
      have hcr : 0 < Real.cos r := Real.cos_pos_of_mem_Ioo ⟨by linarith [hr.1, Real.pi_pos], hr.2⟩
      change 0 < Real.sin r - r * Real.cos r
      apply sub_pos.mpr
      exact (lt_div_iff₀ hcr).mp (by simpa only [Real.tan_eq_sin_div_cos] using Real.lt_tan hr.1 hr.2))
    θ.val hx
  rw [SignSequence.analyticLiftFunction_sub _ _ _ θ.property hs (hi.mul hc),
    SignSequence.analyticLiftFunction_mul _ _ _ θ.property hi hc,
    SignSequence.analyticLiftFunction_id _ θ.property] at htan
  change 0 < sinFunction θ.val - θ.val * cosFunction θ.val at htan
  rw [sinFunction_eq_finiteSin, cosFunction_eq_finiteCos] at htan
  exact ⟨hsθ, sub_pos.mp hsin, (lt_div_iff₀ hcθ).mpr (sub_pos.mp htan)⟩

end Surreal.Surcomplex
