import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Bounded
import OAI.Combinatorics.Progressions.Dynamics.ProductCutoffBudget
import OAI.Combinatorics.Progressions.Estimates.SmoothHalfspaceCutoff
import OAI.Combinatorics.Progressions.Polynomial.PolynomialDeterminantDerivativeBound

namespace OAI

section

namespace Erdos3

open scoped BigOperators ContDiff NNReal

def positiveInequalityDomain {I E : Type*} (d : I → E → ℝ) : Set E :=
  {x | ∀ i, 0 < d i x}

theorem positiveInequalityDomain_isOpen {I E : Type*} [Fintype I] [TopologicalSpace E]
    (d : I → E → ℝ) (hd : ∀ i, Continuous (d i)) : IsOpen (positiveInequalityDomain d) := by
  have heq : positiveInequalityDomain d = ⋂ i, {x | 0 < d i x} := by
    ext x
    simp [positiveInequalityDomain]
  rw [heq]
  exact isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (hd i))

noncomputable def inequalityBoundaryCutoff {I E : Type*} [Fintype I]
    (r : I → ℝ) (d : I → E → ℝ) (x : E) : ℝ :=
  ∏ i, halfspaceCutoff (r i) (d i) x

theorem inequalityBoundaryCutoff_range {I E : Type*} [Fintype I]
    (r : I → ℝ) (d : I → E → ℝ) (x : E) :
    inequalityBoundaryCutoff r d x ∈ Set.Icc (0 : ℝ) 1 :=
  product_cutoff_range _ (fun i => halfspaceCutoff_range (r i) (d i) x)

theorem inequalityBoundaryCutoff_smooth {I E : Type*} [Fintype I]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (r : I → ℝ) (d : I → E → ℝ)
    (hd : ∀ i, ContDiff ℝ ∞ (d i)) : ContDiff ℝ ∞ (inequalityBoundaryCutoff r d) :=
  contDiff_prod (fun i _ => contDiff_halfspaceCutoff (r i) (d i) (hd i))

theorem inequalityBoundaryCutoff_tsupport_subset {I E : Type*} [Fintype I]
    [TopologicalSpace E] (r : I → ℝ) (hr : ∀ i, 0 < r i)
    (d : I → E → ℝ) (hd : ∀ i, Continuous (d i)) :
    tsupport (inequalityBoundaryCutoff r d) ⊆ {x | ∀ i, r i ≤ d i x} := by
  intro x hx i
  exact halfspaceCutoff_tsupport_subset (hr i) (d i) (hd i)
    (product_cutoff_tsupport_subset (fun j => halfspaceCutoff (r j) (d j)) i hx)

theorem inequalityBoundaryCutoff_tsupport_domain {I E : Type*} [Fintype I]
    [TopologicalSpace E] (r : I → ℝ) (hr : ∀ i, 0 < r i)
    (d : I → E → ℝ) (hd : ∀ i, Continuous (d i)) :
    tsupport (inequalityBoundaryCutoff r d) ⊆ positiveInequalityDomain d := by
  intro x hx i
  exact (hr i).trans_le (inequalityBoundaryCutoff_tsupport_subset r hr d hd hx i)

theorem inequalityBoundaryCutoff_compact {I E : Type*} [Fintype I]
    [MetricSpace E] [ProperSpace E] (r : I → ℝ) (hr : ∀ i, 0 < r i)
    (d : I → E → ℝ) (hd : ∀ i, Continuous (d i))
    (hbounded : Bornology.IsBounded (positiveInequalityDomain d)) :
    HasCompactSupport (inequalityBoundaryCutoff r d) := by
  apply Metric.isCompact_of_isClosed_isBounded (isClosed_tsupport _)
  exact hbounded.subset (inequalityBoundaryCutoff_tsupport_domain r hr d hd)

theorem inequalityBoundaryCutoff_eq_one {I E : Type*} [Fintype I]
    (r : I → ℝ) (hr : ∀ i, 0 < r i) (d : I → E → ℝ) {x : E}
    (hx : ∀ i, 2 * r i ≤ d i x) : inequalityBoundaryCutoff r d x = 1 :=
  Finset.prod_eq_one (fun i _ => halfspaceCutoff_eq_one (hr i) (d i) (hx i))

theorem inequalityBoundaryCutoff_fderiv_norm_le {I E : Type*} [Fintype I]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ℝ≥0) (hLip : LipschitzWith A Real.smoothTransition)
    (r : I → ℝ) (hr : ∀ i, 0 < r i) (d : I → E → ℝ) (hd : ∀ i, ContDiff ℝ ∞ (d i)) (x : E) :
    ‖fderiv ℝ (inequalityBoundaryCutoff r d) x‖ ≤
      ∑ i, ((A : ℝ) / r i) * ‖fderiv ℝ (d i) x‖ := by
  apply (product_cutoff_fderiv_norm_le (fun i => halfspaceCutoff (r i) (d i)) x
    (fun i => ((contDiff_halfspaceCutoff (r i) (d i) (hd i)).differentiable (by norm_num)).differentiableAt)
    (fun i => halfspaceCutoff_range (r i) (d i) x)).trans
  exact Finset.sum_le_sum (fun i _ => halfspaceCutoff_fderiv_norm_le A hLip (hr i) (d i)
    (((hd i).differentiable (by norm_num)).differentiableAt))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem halfspaceCutoff_measurable {E : Type*} [MeasurableSpace E]
    (r : ℝ) (d : E → ℝ) (hd : Measurable d) : Measurable (halfspaceCutoff r d) :=
  Real.smoothTransition.continuous.measurable.comp ((hd.div_const r).sub_const 1)

theorem halfspaceCutoff_integral_loss_le {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] {r : ℝ} (hr : 0 < r)
    (d : E → ℝ) (hd : Measurable d) :
    (∫ x, 1 - halfspaceCutoff r d x ∂μ) ≤ μ.real {x | d x < 2 * r} := by
  let s := {x | d x < 2 * r}
  have hs : MeasurableSet s := measurableSet_lt hd measurable_const
  have hfi := cutoff_integrable μ _ (halfspaceCutoff_measurable r d hd) (halfspaceCutoff_range r d)
  calc
    _ ≤ ∫ x, s.indicator (fun _ => (1 : ℝ)) x ∂μ := by
      apply integral_mono ((integrable_const (1 : ℝ)).sub hfi)
        ((integrable_const (1 : ℝ)).indicator hs)
      intro x
      change 1 - halfspaceCutoff r d x ≤ s.indicator (fun _ => (1 : ℝ)) x
      by_cases hx : x ∈ s
      · rw [Set.indicator_of_mem hx]
        linarith [(halfspaceCutoff_range r d x).1]
      · rw [Set.indicator_of_notMem hx, halfspaceCutoff_eq_one hr d (le_of_not_gt hx)]
        norm_num
    _ = _ := integral_indicator_one hs

theorem inequalityBoundaryCutoff_integral_loss_le {I E : Type*} [Fintype I] [MeasurableSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (r : I → ℝ) (hr : ∀ i, 0 < r i)
    (d : I → E → ℝ) (hd : ∀ i, Measurable (d i)) :
    (∫ x, 1 - inequalityBoundaryCutoff r d x ∂μ) ≤ ∑ i, μ.real {x | d i x < 2 * r i} := by
  apply (product_cutoff_integral_loss_le μ (fun i => halfspaceCutoff (r i) (d i))
    (fun i => halfspaceCutoff_measurable (r i) (d i) (hd i))
    (fun i => halfspaceCutoff_range (r i) (d i))).trans
  exact Finset.sum_le_sum (fun i _ => halfspaceCutoff_integral_loss_le μ (hr i) (d i) (hd i))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators ContDiff

noncomputable def scalarCubeValue {α : Type*} [Fintype α] [DecidableEq α]
    (a : Option α → ℝ) (t : Finset α) : ℝ :=
  ∑ r : Option α, (booleanFeature r t : ℝ) * a r

theorem scalarCubeValue_empty {α : Type*} [Fintype α] [DecidableEq α]
    (a : Option α → ℝ) : scalarCubeValue a ∅ = a none := by
  simp [scalarCubeValue, Fintype.sum_option, booleanFeature]

theorem scalarCubeValue_singleton {α : Type*} [Fintype α] [DecidableEq α]
    (a : Option α → ℝ) (i : α) : scalarCubeValue a {i} = a none + a (some i) := by
  simp [scalarCubeValue, Fintype.sum_option, booleanFeature]

theorem scalarCubeValue_contDiff {α : Type*} [Fintype α] [DecidableEq α] (t : Finset α) :
    ContDiff ℝ ∞ (fun a : Option α → ℝ => scalarCubeValue a t) := by
  unfold scalarCubeValue
  apply ContDiff.sum
  intro r _
  exact contDiff_const.mul (ContinuousLinearMap.proj r : (Option α → ℝ) →L[ℝ] ℝ).contDiff

def scalarCubeDomain (α : Type*) [Fintype α] [DecidableEq α] : Set (Option α → ℝ) :=
  {a | ∀ t : Finset α, scalarCubeValue a t ∈ Set.Ioo (0 : ℝ) 1}

noncomputable def scalarCubeFace {α : Type*} [Fintype α] [DecidableEq α]
    (i : Bool × Finset α) (a : Option α → ℝ) : ℝ :=
  if i.1 then 1 - scalarCubeValue a i.2 else scalarCubeValue a i.2

theorem scalarCubeFace_contDiff {α : Type*} [Fintype α] [DecidableEq α] (i : Bool × Finset α) :
    ContDiff ℝ ∞ (scalarCubeFace i) := by
  rcases i with ⟨b, t⟩
  cases b with
  | false => exact scalarCubeValue_contDiff t
  | true => exact contDiff_const.sub (scalarCubeValue_contDiff t)

theorem positiveInequalityDomain_scalarCubeFace (α : Type*) [Fintype α] [DecidableEq α] :
    positiveInequalityDomain (@scalarCubeFace α _ _) = scalarCubeDomain α := by
  ext a
  constructor
  · intro ha t
    have hlo : 0 < scalarCubeValue a t := ha (false, t)
    have hhi : 0 < 1 - scalarCubeValue a t := ha (true, t)
    exact ⟨hlo, by linarith⟩
  · intro ha i
    rcases i with ⟨b, t⟩
    cases b with
    | false => exact (ha t).1
    | true => exact sub_pos.mpr (ha t).2

theorem scalarCubeDomain_isOpen (α : Type*) [Fintype α] [DecidableEq α] :
    IsOpen (scalarCubeDomain α) := by
  rw [← positiveInequalityDomain_scalarCubeFace α]
  exact positiveInequalityDomain_isOpen _ (fun i => (scalarCubeFace_contDiff i).continuous)

theorem scalarCubeDomain_coordinate_abs_lt_one {α : Type*} [Fintype α] [DecidableEq α]
    {a : Option α → ℝ} (ha : a ∈ scalarCubeDomain α) (r : Option α) : |a r| < 1 := by
  have hzero := ha ∅
  rw [scalarCubeValue_empty] at hzero
  cases r with
  | none => exact abs_lt.mpr ⟨by linarith [hzero.1], hzero.2⟩
  | some i =>
    have hi := ha {i}
    rw [scalarCubeValue_singleton] at hi
    exact abs_lt.mpr ⟨by linarith [hzero.1, hzero.2, hi.1], by linarith [hzero.1, hi.2]⟩

theorem scalarCubeDomain_isBounded (α : Type*) [Fintype α] [DecidableEq α] :
    Bornology.IsBounded (scalarCubeDomain α) := by
  apply (Metric.isBounded_closedBall (x := (0 : Option α → ℝ)) (r := 1)).subset
  intro a ha
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro r
  simpa only [Real.norm_eq_abs] using (scalarCubeDomain_coordinate_abs_lt_one ha r).le

noncomputable def scalarCubeCenter (α : Type*) : Option α → ℝ
  | none => 1 / 2
  | some _ => 0

theorem scalarCubeValue_center {α : Type*} [Fintype α] [DecidableEq α] (t : Finset α) :
    scalarCubeValue (scalarCubeCenter α) t = 1 / 2 := by
  simp [scalarCubeValue, Fintype.sum_option, scalarCubeCenter, booleanFeature]

theorem scalarCubeDomain_nonempty (α : Type*) [Fintype α] [DecidableEq α] :
    (scalarCubeDomain α).Nonempty := by
  refine ⟨scalarCubeCenter α, ?_⟩
  intro t
  rw [scalarCubeValue_center]
  norm_num

theorem scalarCubeFace_card (α : Type*) [Fintype α] :
    Fintype.card (Bool × Finset α) = 2 * 2 ^ Fintype.card α := by simp

theorem booleanAffinePolynomial_eval_scalarCubeValue {B F α : Type*}
    [Fintype α] [DecidableEq α] (a : BlockParameter B F α → ℝ) (b : B) (v : F) (t : Finset α) :
    MvPolynomial.eval a (booleanAffinePolynomial b v t) = scalarCubeValue (fun r => a (b, v, r)) t :=
  booleanAffinePolynomial_eval a b v t

end Erdos3

end

end OAI
