import OAI.Combinatorics.Progressions.Probability.AllocatedSlicedIdealDensity

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable [∀ a, DecidableEq (B a)]
variable (P : LayerSamplerAxis I n → Prop) [DecidablePred P]
variable (R σ : Fin m → ℝ)

local notation "degree" => layerSamplerDegree I n
local notation "Active" => {a // ¬P a}
local notation "Coeff" => ActiveProfileCoefficientIndex G B degree P
local notation "Input" => (Σ a : {a : LayerSamplerAxis I n // ¬P a},
  B (Subtype.val a) × Fin (layerSamplerDegree I n (Subtype.val a)))
local notation "Output" => (Σ _a : Active, Unit)

omit [∀ a, DecidableEq (B a)] in
theorem allocatedFixedPathLiftMap_measurable
    (lower width : ∀ a : Active, B a.val × Fin (degree a.val) → ℝ) (r : Coeff → ℝ) :
    Measurable (allocatedFixedPathLiftMap B P R σ lower width r) := by
  unfold allocatedFixedPathLiftMap jointSlicedPrincipal sigmaAxisSampler
    principalSliceSingleton principalSliceValue
  fun_prop

omit [∀ a, DecidableEq (B a)] in
theorem allocatedFixedPathLiftMap_norm_le (hR : ∀ j, R j ≠ 0)
    (lower width : ∀ a : Active, B a.val × Fin (degree a.val) → ℝ)
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    (r : Coeff → ℝ) (hr : ∀ e, |r e| ≤ 1)
    (x : Input → ℝ) (hx : ∀ p, |x p| ≤ 1) :
    ‖allocatedFixedPathLiftMap B P R σ lower width r x‖ ≤ 2 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)).mpr
  intro o
  have hp := principalSliceValue_abs_le
    (jointSlicedProfilePrincipal degree Subtype.val (unitProfilePrincipalSize (B := B))
      (fun a e => r ⟨a,e⟩) o.1)
    (lower o.1) (width o.1) (hwidth o.1) (fun p => x ⟨o.1,p⟩) (fun p => hx _)
  have hm := jointSlicedProfilePrincipal_unit_mass degree Subtype.val
    (fun a e => r ⟨a,e⟩) (fun _ _ => hr _) o.1
  have hc : |(1 / 4 : ℝ) * r ⟨o.1, constantCoefficientSlot _ _⟩| ≤ 1 / 4 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    exact mul_le_of_le_one_right (by norm_num) (hr _)
  simp only [allocatedFixedPathLiftMap, allocatedFixedPathPrincipal_eq B P R σ hR,
    allocatedFixedPathShift_eq B P R σ hR, Pi.add_apply]
  change |(1 / 4 : ℝ) * r ⟨o.1, constantCoefficientSlot _ _⟩ +
    principalSliceValue _ _ _ _| ≤ 2
  exact (abs_add_le _ _).trans ((add_le_add hc (hp.trans hm)).trans (by norm_num))

theorem allocatedFixedPathLiftDensity_zero_off_ball
    (hR : ∀ j, R j ≠ 0) (hB : ∀ a : Active, 4 ≤ Fintype.card (B a.val))
    (lower width : ∀ a : Active, B a.val × Fin (degree a.val) → ℝ)
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hprincipal : ∀ j : Active, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
    (r : Coeff → ℝ) (hr : ∀ e, |r e| ≤ 1)
    (z : Output → ℝ) (hz : 2 < ‖z‖) :
    allocatedFixedPathLiftDensity B P R σ hB lower width r z = 0 := by
  have hd := allocatedFixedPathLiftDensity_law_probability B P R σ hR hB lower width
    ha hδ hprincipal hw hl r hr
  have hb := allocatedFixedPathLiftDensity_cap_lipschitz B P R σ hR hB lower width
    ha hδ hprincipal hw hl r hr
  have hm := allocatedFixedPathLiftMap_measurable B P R σ lower width r
  apply continuousDensity_zero_off_closed volume _ hb.2.continuous hd.2.1
    (S := Metric.closedBall 0 2) Metric.isClosed_closedBall ?_ z
    (by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hz)
  rw [← hd.1]
  apply (ae_map_iff hm.aemeasurable Metric.isClosed_closedBall.measurableSet).mpr
  filter_upwards [unitBoxMeasure_ae] with x hx
  simpa only [dist_zero_right] using
    allocatedFixedPathLiftMap_norm_le B P R σ hR lower width hwidth r hr x
    (fun p => by rw [abs_of_nonneg (hx p).1.le]; exact (hx p).2)

theorem allocatedFixedPathLiftDensity_compact
    (hR : ∀ j, R j ≠ 0) (hB : ∀ a : Active, 4 ≤ Fintype.card (B a.val))
    (lower width : ∀ a : Active, B a.val × Fin (degree a.val) → ℝ)
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hprincipal : ∀ j : Active, a ≤ unitProfilePrincipalSize (B := B) j.val)
    (hw : ∀ j p, δ ≤ width j p) (hl : ∀ j p, 0 ≤ lower j p)
    (r : Coeff → ℝ) (hr : ∀ e, |r e| ≤ 1) :
    HasCompactSupport (allocatedFixedPathLiftDensity B P R σ hB lower width r) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Output → ℝ) 2)
  intro z hz
  exact allocatedFixedPathLiftDensity_zero_off_ball B P R σ hR hB lower width hwidth
    ha hδ hprincipal hw hl r hr z
    (by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hz)

end Erdos3.VectorPolynomial

end

end OAI
