import OAI.Combinatorics.Progressions.Estimates.ActiveProfileNoise

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

noncomputable def partitionedIdealRadius (α : Type*) [Fintype α] (degree : ℕ) : ℝ :=
  1 / 4 + 2 ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ degree

theorem partitionedIdealRadius_nonneg (α : Type*) [Fintype α] (degree : ℕ) :
    0 ≤ partitionedIdealRadius α degree := by
  unfold partitionedIdealRadius
  positivity

theorem partitionedIdealMap_norm_le {D G Z α : Type*}
    [Fintype D] [Fintype G] [Fintype Z] [Fintype α] [DecidableEq α]
    {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
    (P : D → Prop) [DecidablePred P]
    {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)] (sets : ∀ d, O d → Finset α)
    {degree : ℕ} (hdegree : ∀ d, h d ≤ degree)
    (y : PartitionedProfileNoiseIndex G Z α B h P → ℝ) (hy : ∀ j, |y j| ≤ 1)
    (x : PrincipalAxisParameter (B := B) (h := h) (α := α) (fun d => ¬P d) → ℝ)
    (hx : ‖x‖ ≤ 1) :
    ‖partitionedIdealMap h P sets y x‖ ≤ partitionedIdealRadius α degree := by
  apply (pi_norm_le_iff_of_nonneg (partitionedIdealRadius_nonneg α degree)).mpr
  intro o
  have hs := partitionedProfilePrincipal_unit_sum h P y hy o.1
  have hp := jointBooleanSampler_coordinate_abs_le (fun d : {d // ¬P d} => h d.val)
    (partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B)) y) sets x hx o
  have hb : |jointBooleanSampler (fun d : {d // ¬P d} => h d.val)
      (partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B)) y) sets x o| ≤
      (2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ degree := by
    apply hp.trans
    have hpow : (2 : ℝ) ^ (sets o.1 o.2).card ≤ 2 ^ Fintype.card α :=
      pow_le_pow_right₀ (by norm_num) (Finset.card_le_univ (sets o.1 o.2))
    have hdp : ((Fintype.card α : ℝ) + 1) ^ h o.1.val ≤
        ((Fintype.card α : ℝ) + 1) ^ degree :=
      pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card α)]) (hdegree o.1.val)
    have hinner := mul_le_mul hs hdp (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using mul_le_mul hpow hinner (by positivity) (by positivity)
  have hc : |booleanConstantJet sets (partitionedProfileConstant h P (fun _ => 1 / 4) y) o| ≤ 1 / 4 := by
    unfold booleanConstantJet
    split_ifs
    · dsimp only [partitionedProfileConstant]
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
      exact mul_le_of_le_one_right (by norm_num) (hy _)
    · norm_num
  rw [Real.norm_eq_abs]
  change |booleanConstantJet sets (partitionedProfileConstant h P (fun _ => 1 / 4) y) o +
    jointBooleanSampler (fun d : {d // ¬P d} => h d.val)
      (partitionedProfilePrincipal h P (unitProfilePrincipalSize (B := B)) y) sets x o| ≤ _
  exact (abs_add_le _ _).trans (add_le_add hc hb)

theorem partitionedRegularizedIdeal_zero_outside {D G Z α : Type*}
    [Fintype D] [Fintype G] [Fintype Z] [Fintype α] [DecidableEq α]
    {B : D → Type*} [∀ d, Fintype (B d)] (h : D → ℕ)
    (P : D → Prop) [DecidablePred P]
    {O : {d // ¬P d} → Type*} [∀ d, Fintype (O d)] (sets : ∀ d, O d → Finset α)
    {degree : ℕ} (hdegree : ∀ d, h d ≤ degree)
    (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (y : PartitionedProfileNoiseIndex G Z α B h P → ℝ) (hy : ∀ j, |y j| ≤ 1)
    (v : (Σ d, O d) → ℝ) (hv : partitionedIdealRadius α degree + 1 < ‖v‖) :
    partitionedRegularizedIdeal h P sets δ y v = 0 := by
  have hs := regularizedImageDensity_support
    (jointBooleanSource (fun d : {d // ¬P d} => h d.val))
    (partitionedIdealMap h P sets y) δ hδ (partitionedIdealRadius_nonneg α degree)
  apply hs
  · filter_upwards [jointBooleanSource_ae_closedBall
      (α := α) (fun d : {d // ¬P d} => B d.val) (fun d => h d.val)] with x hx
    exact partitionedIdealMap_norm_le h P sets hdegree y hy x
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hx)
  · have hd : (δ : ℝ) ≤ 1 := hδ1
    linarith

end Erdos3

end

end OAI
