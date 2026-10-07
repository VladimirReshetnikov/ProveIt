import OAI.Combinatorics.Progressions.Estimates.BooleanMinorDimension
import OAI.Combinatorics.Progressions.Probability.ScalarCubeDomainDensity

namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def scalarCubeLinearMap {α : Type*} [Fintype α] [DecidableEq α] (t : Finset α) :
    (Option α → ℝ) →L[ℝ] ℝ :=
  ∑ r : Option α, (booleanFeature r t : ℝ) • ContinuousLinearMap.proj r

theorem scalarCubeLinearMap_apply {α : Type*} [Fintype α] [DecidableEq α]
    (t : Finset α) (a : Option α → ℝ) : scalarCubeLinearMap t a = scalarCubeValue a t := by
  simp only [scalarCubeLinearMap, sum_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, scalarCubeValue]

theorem scalarCubeLinearMap_single {α : Type*} [Fintype α] [DecidableEq α]
    (t : Finset α) (r : Option α) :
    scalarCubeLinearMap t (Pi.single r 1) = (booleanFeature r t : ℝ) := by
  rw [scalarCubeLinearMap_apply]
  simp [scalarCubeValue, Pi.single_apply, mul_ite]

theorem scalarCubeLinearMap_norm_le {α : Type*} [Fintype α] [DecidableEq α] (t : Finset α) :
    ‖scalarCubeLinearMap t‖ ≤ (Fintype.card α : ℝ) + 1 := by
  have h := clm_norm_le_card_mul_of_basis (scalarCubeLinearMap t) zero_le_one (fun r => by
    rw [scalarCubeLinearMap_single, Real.norm_eq_abs]
    exact booleanFeature_abs_le_one r t)
  simpa only [Fintype.card_option, Nat.cast_add, Nat.cast_one, mul_one] using h

theorem scalarCubeValue_fderiv_norm_le {α : Type*} [Fintype α] [DecidableEq α]
    (t : Finset α) (a : Option α → ℝ) :
    ‖fderiv ℝ (fun x => scalarCubeValue x t) a‖ ≤ (Fintype.card α : ℝ) + 1 := by
  have heq : (fun x => scalarCubeValue x t) = scalarCubeLinearMap t :=
    funext (fun x => (scalarCubeLinearMap_apply t x).symm)
  rw [heq, ContinuousLinearMap.fderiv]
  exact scalarCubeLinearMap_norm_le t

theorem scalarCubeFace_fderiv_norm_le {α : Type*} [Fintype α] [DecidableEq α]
    (i : Bool × Finset α) (a : Option α → ℝ) :
    ‖fderiv ℝ (scalarCubeFace i) a‖ ≤ (Fintype.card α : ℝ) + 1 := by
  rcases i with ⟨b, t⟩
  cases b with
  | false => exact scalarCubeValue_fderiv_norm_le t a
  | true =>
    change ‖fderiv ℝ (fun x => 1 - scalarCubeValue x t) a‖ ≤ _
    rw [fderiv_const_sub, norm_neg]
    exact scalarCubeValue_fderiv_norm_le t a

theorem scalarCubeBoundaryCutoff_compact (α : Type*) [Fintype α] [DecidableEq α]
    {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (inequalityBoundaryCutoff (fun _ : Bool × Finset α => r) scalarCubeFace) := by
  apply inequalityBoundaryCutoff_compact _ (fun _ => hr) _ (fun i => (scalarCubeFace_contDiff i).continuous)
  rw [positiveInequalityDomain_scalarCubeFace]
  exact scalarCubeDomain_isBounded α

theorem scalarCubeBoundaryCutoff_fderiv_norm_le {α : Type*} [Fintype α] [DecidableEq α]
    (A : ℝ≥0) (hLip : LipschitzWith A Real.smoothTransition) {r : ℝ} (hr : 0 < r)
    (a : Option α → ℝ) :
    ‖fderiv ℝ (inequalityBoundaryCutoff (fun _ : Bool × Finset α => r) scalarCubeFace) a‖ ≤
      ((2 * 2 ^ Fintype.card α : ℕ) : ℝ) * ((A : ℝ) / r * ((Fintype.card α : ℝ) + 1)) := by
  apply (inequalityBoundaryCutoff_fderiv_norm_le A hLip _ (fun _ => hr)
    scalarCubeFace scalarCubeFace_contDiff a).trans
  calc
    _ ≤ ∑ _i : Bool × Finset α, (A : ℝ) / r * ((Fintype.card α : ℝ) + 1) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (scalarCubeFace_fderiv_norm_le i a)
        (div_nonneg A.coe_nonneg hr.le))
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, scalarCubeFace_card, nsmul_eq_mul]

end Erdos3

end

end OAI
