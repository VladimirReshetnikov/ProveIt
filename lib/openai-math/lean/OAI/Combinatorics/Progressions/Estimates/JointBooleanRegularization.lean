/- Modified for ProveIt: prove finite regularity below infinity explicitly
for the older ContDiff order API. Mathematical statements unchanged. -/
import OAI.Combinatorics.Progressions.Dynamics.BooleanCanonicalLogBudget
import OAI.Combinatorics.Progressions.Dynamics.BudgetedOpenImageComparison
import OAI.Combinatorics.Progressions.Dynamics.JointBooleanWeightBudget
import OAI.Combinatorics.Progressions.Probability.JointBooleanCutoffLaw
import OAI.Combinatorics.Progressions.Probability.RegularizedSigmaDensity

namespace OAI

section

namespace Erdos3

variable {D : Type*} [Fintype D] {I O : D → Type*}
  [∀ d, Fintype (I d)] [∀ d, Fintype (O d)]

noncomputable def sigmaAxisOperatorMap :
    (∀ d, (I d → ℝ) →L[ℝ] (O d → ℝ)) →L[ℝ]
      (((Σ d, I d) → ℝ) →L[ℝ] ((Σ d, O d) → ℝ)) :=
  ({ toFun := sigmaAxisOperator
     map_add' := by
       intro A B
       ext x s
       simp only [sigmaAxisOperator_apply, Pi.add_apply, add_apply]
     map_smul' := by
       intro t A
       ext x s
       simp only [sigmaAxisOperator_apply, Pi.smul_apply, smul_apply, RingHom.id_apply] } :
    (∀ d, (I d → ℝ) →L[ℝ] (O d → ℝ)) →ₗ[ℝ]
      (((Σ d, I d) → ℝ) →L[ℝ] ((Σ d, O d) → ℝ))).mkContinuous 1 (fun A => by
        rw [one_mul]
        exact sigmaAxisOperator_norm_le A (norm_nonneg A) (norm_le_pi_norm A))

theorem sigmaAxisOperatorMap_apply (A : ∀ d, (I d → ℝ) →L[ℝ] (O d → ℝ)) :
    sigmaAxisOperatorMap A = sigmaAxisOperator A := rfl

theorem sigmaAxisOperatorMap_norm_le_one :
    ‖sigmaAxisOperatorMap (I := I) (O := O)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro A
  rw [one_mul]
  exact sigmaAxisOperator_norm_le A (norm_nonneg A) (norm_le_pi_norm A)

theorem sigmaAxisFamily_fderiv_norm_le {E : D → Type*}
    [∀ d, NormedAddCommGroup (E d)] [∀ d, NormedSpace ℝ (E d)]
    (f : ∀ d, (I d → ℝ) → E d) (x : (Σ d, I d) → ℝ)
    (hf : ∀ d, DifferentiableAt ℝ (f d) (sigmaAxisProjection I d x))
    {H : ℝ} (hH : 0 ≤ H)
    (hbound : ∀ d, ‖fderiv ℝ (f d) (sigmaAxisProjection I d x)‖ ≤ H) :
    ‖fderiv ℝ (fun y d => f d (sigmaAxisProjection I d y)) x‖ ≤ H := by
  have hd := hasFDerivAt_pi.mpr (fun d =>
    (hf d).hasFDerivAt.comp x (sigmaAxisProjection I d).hasFDerivAt)
  simp only [Function.comp_def] at hd
  rw [hd.fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ hH
  intro v
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hH (norm_nonneg v))).mpr
  intro d
  change ‖fderiv ℝ (f d) (sigmaAxisProjection I d x) (sigmaAxisProjection I d v)‖ ≤ H * ‖v‖
  exact ((fderiv ℝ (f d) (sigmaAxisProjection I d x)).le_opNorm _).trans
    (mul_le_mul (hbound d) (sigmaAxisProjection_norm_apply_le I d v) (norm_nonneg _) hH)

theorem sigmaAxisOperatorFamily_fderiv_norm_le
    (A : ∀ d, (I d → ℝ) → ((O d → ℝ) →L[ℝ] (O d → ℝ))) (x : (Σ d, I d) → ℝ)
    (hA : ∀ d, DifferentiableAt ℝ (A d) (sigmaAxisProjection I d x))
    {H : ℝ} (hH : 0 ≤ H)
    (hbound : ∀ d, ‖fderiv ℝ (A d) (sigmaAxisProjection I d x)‖ ≤ H) :
    ‖fderiv ℝ (fun y => sigmaAxisOperator (fun d => A d (sigmaAxisProjection I d y))) x‖ ≤ H := by
  let F := fun y d => A d (sigmaAxisProjection I d y)
  let L : (∀ d, (O d → ℝ) →L[ℝ] (O d → ℝ)) →L[ℝ]
      (((Σ d, O d) → ℝ) →L[ℝ] ((Σ d, O d) → ℝ)) := sigmaAxisOperatorMap
  have hF : DifferentiableAt ℝ F x := differentiableAt_pi.mpr (fun d =>
    (hA d).comp x (sigmaAxisProjection I d).differentiableAt)
  have he : (fun y => sigmaAxisOperator (fun d => A d (sigmaAxisProjection I d y))) =
      L ∘ F := rfl
  rw [he, fderiv_comp x L.differentiableAt hF, L.fderiv]
  have hL : ‖L‖ ≤ 1 := sigmaAxisOperatorMap_norm_le_one
  have hfbound : ‖fderiv ℝ F x‖ ≤ H := sigmaAxisFamily_fderiv_norm_le A x hA hH hbound
  have hnF : 0 ≤ ‖fderiv ℝ F x‖ := norm_nonneg (fderiv ℝ F x)
  calc
    _ ≤ ‖L‖ * ‖fderiv ℝ F x‖ := L.opNorm_comp_le _
    _ ≤ 1 * H := mul_le_mul hL hfbound hnF zero_le_one
    _ = H := one_mul H

theorem sigmaAxisSampler_selected_fderiv_norm_le
    (U : ∀ d, (I d → ℝ) → (O d → ℝ)) (hU : ∀ d, ContDiff ℝ 2 (U d))
    (J : ∀ d, (O d → ℝ) →L[ℝ] (I d → ℝ)) (x : (Σ d, I d) → ℝ)
    {H : ℝ} (hH : 0 ≤ H)
    (hbound : ∀ d, ‖fderiv ℝ (selectedDerivative (U d) (J d)) (sigmaAxisProjection I d x)‖ ≤ H) :
    ‖fderiv ℝ (selectedDerivative (sigmaAxisSampler U) (sigmaAxisOperator J)) x‖ ≤ H := by
  have he : selectedDerivative (sigmaAxisSampler U) (sigmaAxisOperator J) =
      fun y => sigmaAxisOperator (fun d => selectedDerivative (U d) (J d) (sigmaAxisProjection I d y)) := by
    funext y
    exact sigmaAxisSampler_selectedDerivative U J y (fun d => (hU d).differentiable (by norm_num) _)
  rw [he]
  apply sigmaAxisOperatorFamily_fderiv_norm_le _ x _ hH hbound
  intro d
  have hc : ContDiff ℝ 1 (selectedDerivative (U d) (J d)) :=
    ((hU d).fderiv_right (by norm_num)).clm_comp contDiff_const
  exact hc.differentiable one_ne_zero _

end Erdos3

end

section

namespace Erdos3

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

theorem jointBoolean_selected_inverse_bound {h : D → ℕ}
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α) (block : ∀ d, O d → B d)
    (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α)
    (hcard : ∀ d o, (sets d o).card ≤ h d) (x : JointBlockParameter B h α → ℝ)
    (C R κ : D → ℝ) (hC : ∀ d, 0 ≤ C d) (hR : ∀ d, 0 ≤ R d) (hκ : ∀ d, 0 < κ d)
    (hc : ∀ d o, |c d (block d o)| ≤ C d) (hx : ∀ s, |x s| ≤ R s.1)
    (hdet : ∀ d, κ d ≤ |booleanMinorDeterminant (c d) (sets d) (block d) (v d) (sel d)
      (fun i => x ⟨d, i⟩)|)
    {K : ℝ} (hK : 0 ≤ K)
    (hcap : ∀ d, productMinorInverseBound (Fintype.card (O d)) (Fintype.card α)
      (h d) (C d) (R d) (κ d) ≤ K) :
    (selectedDerivative (jointBooleanSampler h c sets) (jointBooleanInjection block v sel) x).IsInvertible ∧
      ‖(selectedDerivative (jointBooleanSampler h c sets) (jointBooleanInjection block v sel) x).inverse‖ ≤ K := by
  have haxis (d : D) := boolean_selected_inverse_bound (c d) (sets d) (block d) (v d) (sel d)
    (hcard d) (fun i => x ⟨d, i⟩) (hC d) (hR d) (hc d) (fun i => hx ⟨d, i⟩) (hκ d) (hdet d)
  exact sigmaAxisSampler_inverse_bound _ _ x
    (fun d => (booleanSamplerMap_contDiff (c d) (sets d)).differentiable (by norm_num) _)
    (fun d => (haxis d).1) hK (fun d => (haxis d).2.trans (hcap d))

end Erdos3

end

section

namespace Erdos3

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

theorem jointBoolean_selected_derivative_bound {h : D → ℕ}
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α) (block : ∀ d, O d → B d)
    (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α)
    (hcard : ∀ d o, (sets d o).card ≤ h d) (x : JointBlockParameter B h α → ℝ)
    (C R : D → ℝ) (hC : ∀ d, 0 ≤ C d) (hR : ∀ d, 1 ≤ R d)
    (hc : ∀ d o, |c d (block d o)| ≤ C d) (hx : ∀ s, |x s| ≤ R s.1)
    {H : ℝ} (hH : 0 ≤ H)
    (hcap : ∀ d, productMinorDerivativeBound (Fintype.card (BlockParameter (B d) (Fin (h d)) α))
      (Fintype.card (O d)) (Fintype.card α) (h d) (C d) (R d) ≤ H) :
    ‖fderiv ℝ (selectedDerivative (jointBooleanSampler h c sets) (jointBooleanInjection block v sel)) x‖ ≤ H := by
  apply sigmaAxisSampler_selected_fderiv_norm_le _
    (fun d => (booleanSamplerMap_contDiff (c d) (sets d)).of_le (by first | exact WithTop.coe_le_coe.mpr le_top | norm_num)) _ x hH
  intro d
  exact (boolean_selected_derivative_bound (c d) (sets d) (block d) (v d) (sel d)
    (hcard d) (fun i => x ⟨d, i⟩) (hC d) (hR d) (hc d) (fun i => hx ⟨d, i⟩)).trans (hcap d)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem regularizedImageMap_mappedTest {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsFiniteMeasure μ] (U : Ω → I → ℝ) (hU : Measurable U) (δ : ℝ≥0)
    (φ : (I → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    mappedTest (μ.prod (unitCoefficientSource I)) (regularizedImageMap δ U) φ =
      ∫ r, mappedTest μ U (fun x => φ (x+(δ : ℝ) • r)) ∂unitCoefficientSource I := by
  have hi := mappedTest_integrable (μ.prod (unitCoefficientSource I)) (regularizedImageMap δ U)
    (regularizedImageMap_measurable δ U hU) φ hφ hbound
  change (∫ p, φ (U p.1+(δ : ℝ) • p.2) ∂μ.prod (unitCoefficientSource I)) = _
  exact (integral_prod _ hi).trans (integral_integral_swap hi)

theorem regularizedImageMap_error {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → I → ℝ) (hU : Measurable U)
    (δ H : ℝ≥0) (η : ℝ) (φ : (I → ℝ) → ℝ) (hφ : Measurable φ)
    (hbound : ∀ x, ‖φ x‖ ≤ 1)
    (hmove : ∀ z, |mappedTest μ U (fun x => φ (x+z))-mappedTest μ U φ| ≤ η+H*dist z 0) :
    |mappedTest (μ.prod (unitCoefficientSource I)) (regularizedImageMap δ U) φ - mappedTest μ U φ| ≤
      η+H*δ := by
  let F := fun r : I → ℝ => mappedTest μ U (fun x => φ (x+(δ : ℝ) • r))
  have hfm : Measurable F := (mappedTest_shift_measurable μ U hU φ hφ).comp
    (measurable_id.const_smul (δ : ℝ))
  have hfi : Integrable F (unitCoefficientSource I) :=
    (integrable_const (μ.real Set.univ)).mono' hfm.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun r => mappedTest_norm_le μ U _ (fun x => hbound _)))
  have heq : mappedTest (μ.prod (unitCoefficientSource I)) (regularizedImageMap δ U) φ - mappedTest μ U φ =
      ∫ r, F r-mappedTest μ U φ ∂unitCoefficientSource I := by
    rw [regularizedImageMap_mappedTest μ U hU δ φ hφ hbound,
      integral_sub hfi (integrable_const _)]
    simp only [integral_const, probReal_univ, one_smul, F]
  have hb : ∀ᵐ r ∂unitCoefficientSource I, ‖F r-mappedTest μ U φ‖ ≤ η+(H : ℝ)*δ := by
    filter_upwards [unitCoefficientSource_norm_le I] with r hr
    have hd : dist ((δ : ℝ) • r) 0 ≤ (δ : ℝ) := by
      rw [dist_zero_right, norm_smul, Real.norm_of_nonneg δ.coe_nonneg]
      exact mul_le_of_le_one_right δ.coe_nonneg hr
    exact (hmove ((δ : ℝ) • r)).trans
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hd H.coe_nonneg))
  have hi := norm_integral_le_of_norm_le (integrable_const (η+(H : ℝ)*δ)) hb
  rw [integral_const, probReal_univ, one_smul, Real.norm_eq_abs] at hi
  rw [heq]
  exact hi

theorem regularizedImageDensity_test_error {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → I → ℝ) (hU : Measurable U)
    (δ : ℝ≥0) (hδ : 0 < δ) (H : ℝ≥0) (η : ℝ)
    (φ : (I → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1)
    (hmove : ∀ z, |mappedTest μ U (fun x => φ (x+z))-mappedTest μ U φ| ≤ η+H*dist z 0) :
    |(∫ x, regularizedImageDensity μ U δ x*φ x)-mappedTest μ U φ| ≤ η+H*δ := by
  have he := mappedTest_eq_density (μ.prod (unitCoefficientSource I)) volume (regularizedImageMap δ U)
    (regularizedImageMap_measurable δ U hU) (regularizedImageDensity μ U δ)
    (regularizedImageDensity_measurable μ U hU δ) (regularizedImageDensity_probability μ U hU δ hδ).1
    (regularizedImageDensity_image_law μ U hU δ hδ) φ hφ
  rw [← he]
  exact regularizedImageMap_error μ U hU δ H η φ hφ hbound hmove

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

theorem jointBoolean_selected_inverse_perturbation {h : D → ℕ}
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α)
    (hcard : ∀ d o, (sets d o).card ≤ h d) (x : JointBlockParameter B h α → ℝ)
    (C R κ : D → ℝ) (hC : ∀ d, 0 ≤ C d) (hR : ∀ d, 0 ≤ R d) (hκ : ∀ d, 0 < κ d)
    (hc : ∀ d o, |c d (block d o)| ≤ C d) (hx : ∀ s, |x s| ≤ R s.1)
    (hdet : ∀ d, κ d ≤ |booleanMinorDeterminant (c d) (sets d) (block d) (v d) (sel d)
      (fun i => x ⟨d, i⟩)|)
    (K : ℝ≥0)
    (hcap : ∀ d, productMinorInverseBound (Fintype.card (O d)) (Fintype.card α)
      (h d) (C d) (R d) (κ d) ≤ K)
    (V : (JointBlockParameter B h α → ℝ) → ((Σ d, O d) → ℝ))
    (hsmall : (K : ℝ) * ‖fderiv ℝ V x - fderiv ℝ (jointBooleanSampler h c sets) x‖ ≤ 1 / 2) :
    (selectedDerivative V (jointBooleanInjection block v sel) x).IsInvertible ∧
      ‖(selectedDerivative V (jointBooleanInjection block v sel) x).inverse‖ ≤ 2 * K := by
  obtain ⟨hinv, hbound⟩ := jointBoolean_selected_inverse_bound c sets block v sel hcard x
    C R κ hC hR hκ hc hx hdet K.coe_nonneg hcap
  have hJ := jointBooleanInjection_norm_le block hblock v sel
  apply selected_inverse_perturbation (jointBooleanSampler h c sets) V
    (jointBooleanInjection block v sel) x hinv K hbound
  apply le_trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hJ (norm_nonneg _)) K.coe_nonneg)
  simpa only [mul_one] using hsmall

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

theorem jointBoolean_divergence_bound {h : D → ℕ}
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α)
    (hcard : ∀ d o, (sets d o).card ≤ h d)
    (C R κ : D → ℝ) (hC : ∀ d, 0 ≤ C d) (hR : ∀ d, 1 ≤ R d) (hκ : ∀ d, 0 < κ d)
    (hc : ∀ d o, |c d (block d o)| ≤ C d)
    (K H : ℝ≥0)
    (hK : ∀ d, productMinorInverseBound (Fintype.card (O d)) (Fintype.card α)
      (h d) (C d) (R d) (κ d) ≤ K)
    (hH : ∀ d, productMinorDerivativeBound (Fintype.card (BlockParameter (B d) (Fin (h d)) α))
      (Fintype.card (O d)) (Fintype.card α) (h d) (C d) (R d) ≤ H)
    (w : (JointBlockParameter B h α → ℝ) → ℝ) (hw : ContDiff ℝ 1 w) (hs : HasCompactSupport w)
    (hbox : ∀ x ∈ tsupport w, ∀ s, |x s| ≤ R s.1)
    (hdet : ∀ x ∈ tsupport w, ∀ d, κ d ≤
      |booleanMinorDeterminant (c d) (sets d) (block d) (v d) (sel d) (fun i => x ⟨d, i⟩)|)
    (i : Σ d, O d) :
    (∫ x, |coordinateDivergence (fun j x => w x * selectedInverseField
      (jointBooleanSampler h c sets) (jointBooleanInjection block v sel) i j x) x|) ≤
      (K : ℝ) * (∑ j, ∫ x, |fderiv ℝ w x (Pi.single j 1)|) +
        (Fintype.card (JointBlockParameter B h α) : ℝ) * ((K : ℝ) ^ 2 * H) * ∫ x, |w x| := by
  let U := jointBooleanSampler h c sets
  let J := jointBooleanInjection block v sel
  have hU : ContDiff ℝ 2 U := (jointBooleanSampler_contDiff h c sets).of_le (by first | exact WithTop.coe_le_coe.mpr le_top | norm_num)
  have hinfo (x) (hx : x ∈ tsupport w) := jointBoolean_selected_inverse_bound
    c sets block v sel hcard x C R κ hC (fun d => zero_le_one.trans (hR d)) hκ hc
    (hbox x hx) (hdet x hx) K.coe_nonneg hK
  have hder (x) (hx : x ∈ tsupport w) := jointBoolean_selected_derivative_bound
    c sets block v sel hcard x C R hC hR hc (hbox x hx) H.coe_nonneg hH
  have hbase := selected_inverse_divergence_bound U J w hw hs
    (fun _ _ => hU.contDiffAt) (fun x hx => (hinfo x hx).1) K H
    (fun x hx => (hinfo x hx).2) hder i
  have hJ : ‖J‖ ≤ 1 := jointBooleanInjection_norm_le block hblock v sel
  have hS : 0 ≤ ∑ j, ∫ x, |fderiv ℝ w x (Pi.single j 1)| :=
    Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => abs_nonneg _))
  have hW : 0 ≤ ∫ x, |w x| := integral_nonneg (fun _ => abs_nonneg _)
  apply hbase.trans
  have hJK : ‖J‖ * (K : ℝ) ≤ K := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hJ K.coe_nonneg
  have hJKH : ‖J‖ * (K : ℝ) ^ 2 * H ≤ (K : ℝ) ^ 2 * H := by
    have ht := mul_le_mul_of_nonneg_right hJ (sq_nonneg (K : ℝ))
    rw [one_mul] at ht
    exact mul_le_mul_of_nonneg_right ht H.coe_nonneg
  exact add_le_add (mul_le_mul_of_nonneg_right hJK hS)
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hJKH (Nat.cast_nonneg _)) hW)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem cutoff_translation_error {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (w : Ω → ℝ) (hw : Measurable w) (hw01 : ∀ a, w a ∈ Set.Icc (0 : ℝ) 1)
    (U : Ω → I → ℝ) (hU : Measurable U) (H : ℝ≥0)
    (hmove : ImageTranslationBound (realDensityMeasure μ w) U H)
    {η : ℝ} (hcut : (∫ a, 1-w a ∂μ) ≤ η)
    (φ : (I → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) (z : I → ℝ) :
    |mappedTest μ U (fun x => φ (x+z))-mappedTest μ U φ| ≤ 2*η+H*dist z 0 := by
  have hshift := (mappedTest_cutoff_error μ w hw hw01 U hU (fun x => φ (x+z))
    (hφ.comp (measurable_id.add_const z)) (fun x => hbound (x+z))).trans hcut
  have hbase := (mappedTest_cutoff_error μ w hw hw01 U hU φ hφ hbound).trans hcut
  have hmiddle := hmove φ hφ hbound z
  have ht := abs_sub_le (mappedTest μ U (fun x => φ (x+z)))
    (mappedTest (realDensityMeasure μ w) U (fun x => φ (x+z))) (mappedTest μ U φ)
  have hu := abs_sub_le (mappedTest (realDensityMeasure μ w) U (fun x => φ (x+z)))
    (mappedTest (realDensityMeasure μ w) U φ) (mappedTest μ U φ)
  rw [abs_sub_comm (mappedTest (realDensityMeasure μ w) U φ) (mappedTest μ U φ)] at hu
  linarith

theorem regularizedImageDensity_cutoff_error {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (w : Ω → ℝ) (hw : Measurable w) (hw01 : ∀ a, w a ∈ Set.Icc (0 : ℝ) 1)
    (U : Ω → I → ℝ) (hU : Measurable U) (H : ℝ≥0)
    (hmove : ImageTranslationBound (realDensityMeasure μ w) U H)
    {η : ℝ} (hcut : (∫ a, 1-w a ∂μ) ≤ η) (δ : ℝ≥0) (hδ : 0 < δ)
    (φ : (I → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    |(∫ x, regularizedImageDensity μ U δ x*φ x)-mappedTest μ U φ| ≤ 2*η+H*δ :=
  regularizedImageDensity_test_error μ U hU δ hδ H (2*η) φ hφ hbound
    (cutoff_translation_error μ w hw hw01 U hU H hmove hcut φ hφ hbound)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem regularizedImageDensity_test_integral {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → I → ℝ) (hU : Measurable U)
    (δ : ℝ≥0) (hδ : 0 < δ) (φ : (I → ℝ) → ℝ) (hφ : Measurable φ) :
    (∫ x, regularizedImageDensity μ U δ x*φ x) =
      mappedTest (μ.prod (unitCoefficientSource I)) (regularizedImageMap δ U) φ :=
  (mappedTest_eq_density (μ.prod (unitCoefficientSource I)) volume (regularizedImageMap δ U)
    (regularizedImageMap_measurable δ U hU) (regularizedImageDensity μ U δ)
    (regularizedImageDensity_measurable μ U hU δ) (regularizedImageDensity_probability μ U hU δ hδ).1
    (regularizedImageDensity_image_law μ U hU δ hδ) φ hφ).symm

theorem regularizedImageDensity_translate_test {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → I → ℝ) (hU : Measurable U)
    (δ : ℝ≥0) (hδ : 0 < δ) (b : I → ℝ) (φ : (I → ℝ) → ℝ) (hφ : Measurable φ) :
    (∫ x, regularizedImageDensity μ (fun a => b+U a) δ x*φ x) =
      ∫ x, regularizedImageDensity μ U δ x*φ (b+x) := by
  rw [regularizedImageDensity_test_integral μ (fun a => b+U a) (measurable_const.add hU) δ hδ φ hφ,
    regularizedImageDensity_test_integral μ U hU δ hδ (fun x => φ (b+x))
      (hφ.comp (measurable_const.add measurable_id))]
  simp only [mappedTest, regularizedImageMap, add_assoc]

theorem regularizedImageDensity_translate_error {Ω I : Type*} [MeasurableSpace Ω] [Fintype I]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Ω → I → ℝ) (hU : Measurable U)
    (δ : ℝ≥0) (hδ : 0 < δ) {ε : ℝ}
    (herr : ∀ φ : (I → ℝ) → ℝ, Measurable φ → (∀ x, ‖φ x‖ ≤ 1) →
      |(∫ x, regularizedImageDensity μ U δ x*φ x)-mappedTest μ U φ| ≤ ε)
    (b : I → ℝ) (φ : (I → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    |(∫ x, regularizedImageDensity μ (fun a => b+U a) δ x*φ x)-
      mappedTest μ (fun a => b+U a) φ| ≤ ε := by
  rw [regularizedImageDensity_translate_test μ U hU δ hδ b φ hφ]
  exact herr (fun x => φ (b+x)) (hφ.comp (measurable_const.add measurable_id)) (fun x => hbound (b+x))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

theorem jointBooleanGoodWeight_translation_bound {h : D → ℕ}
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α)
    (hcard : ∀ d o, (sets d o).card ≤ h d)
    (C : D → ℝ) (hC : ∀ d, 0 ≤ C d) (hc : ∀ d o, |c d (block d o)| ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (r : ∀ d, B d × Fin (h d) → ℝ) (hr : ∀ d i, 0 < r d i)
    (κ : D → ℝ) (hκ : ∀ d, 0 < κ d) (K H : ℝ≥0)
    (hK : ∀ d, productMinorInverseBound (Fintype.card (O d)) (Fintype.card α)
      (h d) (C d) 1 (κ d) ≤ K)
    (hH : ∀ d, productMinorDerivativeBound (Fintype.card (BlockParameter (B d) (Fin (h d)) α))
      (Fintype.card (O d)) (Fintype.card α) (h d) (C d) 1 ≤ H) :
    let n := fun d => Fintype.card (BlockParameter (B d) (Fin (h d)) α)
    let G := fun d => productMinorDeterminantDerivativeBound (n d) (Fintype.card (O d))
      (Fintype.card α) (h d) (C d) 1
    let S := ∑ d, ((∑ i, ((2 * 2 ^ Fintype.card α : ℕ) : ℝ) *
      ((Fintype.card α : ℝ) + 1) ^ 2 * T / r d i) + (n d : ℝ) * ((A : ℝ) / κ d * G d))
    ∃ L : ℝ≥0, (L : ℝ) = (Fintype.card (Σ d, O d) : ℝ) *
      ((K : ℝ) * S + (Fintype.card (JointBlockParameter B h α) : ℝ) * ((K : ℝ) ^ 2 * H)) ∧
      ImageTranslationBound
        (realDensityMeasure volume (jointBooleanGoodWeight c sets block v sel ψ r κ))
        (jointBooleanSampler h c sets) L := by
  let n := fun d => Fintype.card (BlockParameter (B d) (Fin (h d)) α)
  let G := fun d => productMinorDeterminantDerivativeBound (n d) (Fintype.card (O d))
    (Fintype.card α) (h d) (C d) 1
  let S := ∑ d, ((∑ i, ((2 * 2 ^ Fintype.card α : ℕ) : ℝ) *
    ((Fintype.card α : ℝ) + 1) ^ 2 * T / r d i) + (n d : ℝ) * ((A : ℝ) / κ d * G d))
  let w := jointBooleanGoodWeight c sets block v sel ψ r κ
  let U := jointBooleanSampler h c sets
  let J := jointBooleanInjection block v sel
  have hs := jointBooleanGoodWeight_spec c sets block v sel ψ hψ hrange hzero r hr κ hκ
  have hb := jointBooleanGoodWeight_derivative_budget c sets block v sel hcard C hC hc
    ψ hψ hrange hzero A T hLip hTransition r hr κ hκ
  have hS : 0 ≤ S := (Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => abs_nonneg _))).trans hb
  let Q : ℝ≥0 := ⟨(K : ℝ) * S + (Fintype.card (JointBlockParameter B h α) : ℝ) *
    ((K : ℝ) ^ 2 * H), by positivity⟩
  have hi (x) (hx : x ∈ tsupport w) := jointBoolean_selected_inverse_bound c sets block v sel
    hcard x C (fun _ => 1) κ hC (fun _ => zero_le_one) hκ hc (hs.2.2.2.2 x hx).1
    (hs.2.2.2.2 x hx).2 K.coe_nonneg hK
  have hdiv (i : Σ d, O d) :
      (∫ x, |coordinateDivergence (fun j x => w x * selectedInverseField U J i j x) x|) ≤ Q := by
    have hd := jointBoolean_divergence_bound c sets block hblock v sel hcard C (fun _ => 1) κ
      hC (fun _ => le_rfl) hκ hc K H hK hH w hs.1 hs.2.1
      (fun x hx => (hs.2.2.2.2 x hx).1) (fun x hx => (hs.2.2.2.2 x hx).2) i
    apply hd.trans
    exact add_le_add (mul_le_mul_of_nonneg_left hb K.coe_nonneg)
      (mul_le_of_le_one_right (by positivity) hs.2.2.2.1)
  refine ⟨∑ _ : Σ d, O d, Q, ?_, ?_⟩
  · simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, NNReal.coe_mul, NNReal.coe_natCast]
    rfl
  · exact imageTranslationBound_of_selected_inverse U
      ((jointBooleanSampler_contDiff h c sets).of_le (by first | exact WithTop.coe_le_coe.mpr le_top | norm_num)) J w hs.1 hs.2.1 hs.2.2.1
      (fun x hx => (hi x hx).1) (fun _ => Q) hdiv

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal ContDiff BigOperators

noncomputable def jointBooleanTranslationBudget {D α : Type*} [Fintype D] [Fintype α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
    (h : D → ℕ) (C : D → ℝ) (A T : ℝ≥0)
    (r : ∀ d, B d × Fin (h d) → ℝ) (κ : D → ℝ) : ℝ≥0 :=
  let K := jointBooleanInverseBudget (O := O) (α := α) h C κ
  let H := jointBooleanDerivativeBudget (B := B) (O := O) (α := α) h C
  Real.toNNReal ((Fintype.card (Σ d, O d) : ℝ) *
    ((K : ℝ)*jointBooleanWeightBudget (O := O) (α := α) h C A T r κ +
      (Fintype.card (JointBlockParameter B h α) : ℝ)*((K : ℝ)^2*H)))

theorem jointBooleanGoodWeight_translation_budget {D α : Type*}
    [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    [∀ d, Fintype (O d)] [∀ d, DecidableEq (O d)]
    (h : D → ℕ) (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α)
    (hcard : ∀ d o, (sets d o).card ≤ h d)
    (C : D → ℝ) (hC : ∀ d, 0 ≤ C d) (hc : ∀ d o, |c d (block d o)| ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (r : ∀ d, B d × Fin (h d) → ℝ) (hr : ∀ d i, 0 < r d i)
    (κ : D → ℝ) (hκ : ∀ d, 0 < κ d) :
    ImageTranslationBound (realDensityMeasure (jointBooleanSource h) (jointBooleanCutoff c sets block v sel ψ r κ))
      (jointBooleanSampler h c sets) (jointBooleanTranslationBudget (O := O) (α := α) h C A T r κ) := by
  rw [← jointBooleanGoodWeight_measure c sets block v sel ψ hψ hrange hzero r hr κ hκ]
  let K := jointBooleanInverseBudget (O := O) (α := α) h C κ
  let H := jointBooleanDerivativeBudget (B := B) (O := O) (α := α) h C
  obtain ⟨L, hL, htrans⟩ := jointBooleanGoodWeight_translation_bound c sets block hblock v sel hcard C hC hc
    ψ hψ hrange hzero A T hLip hTransition r hr κ hκ K H
    (jointBooleanInverseBudget_le h C κ) (jointBooleanDerivativeBudget_le h C)
  have hLbound : (L : ℝ) ≤ jointBooleanTranslationBudget (O := O) (α := α) h C A T r κ := by
    rw [hL]
    exact Real.le_coe_toNNReal _
  intro φ hφ hbound z
  exact (htrans φ hφ hbound z).trans (mul_le_mul_of_nonneg_right hLbound dist_nonneg)

theorem jointBooleanCutoff_loss {D α : Type*}
    [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    [∀ d, Fintype (O d)] [∀ d, DecidableEq (O d)] {h : D → ℕ}
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α) (block : ∀ d, O d → B d)
    (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0)
    (r : ∀ d, B d × Fin (h d) → ℝ) (hr : ∀ d i, 0 < r d i)
    (κ : D → ℝ) (hκ : ∀ d, 0 < κ d) {η : ℝ}
    (hmass : 1-η ≤ ∫ x, jointBooleanGoodWeight c sets block v sel ψ r κ x) :
    (∫ x, 1-jointBooleanCutoff c sets block v sel ψ r κ x ∂jointBooleanSource h) ≤ η := by
  let : IsProbabilityMeasure (jointBooleanSource (B := B) (α := α) h) := jointBooleanSource_probability h
  have hs := jointBooleanGoodWeight_spec c sets block v sel ψ hψ hrange hzero r hr κ hκ
  have hwi : Integrable (jointBooleanGoodWeight c sets block v sel ψ r κ) :=
    hs.1.continuous.integrable_of_hasCompactSupport hs.2.1
  have hw0 : ∀ x, 0 ≤ jointBooleanGoodWeight c sets block v sel ψ r κ x := hs.2.2.1
  have hχ : Measurable (jointBooleanCutoff c sets block v sel ψ r κ) :=
    (jointBooleanCutoff_contDiff c sets block v sel ψ hψ r κ).continuous.measurable
  have hχ01 : ∀ x, jointBooleanCutoff c sets block v sel ψ r κ x ∈ Set.Icc (0 : ℝ) 1 :=
    jointBooleanCutoff_range c sets block v sel ψ hrange r κ
  have hlaw : realDensityMeasure volume (jointBooleanGoodWeight c sets block v sel ψ r κ) =
      realDensityMeasure (jointBooleanSource (B := B) (α := α) h) (jointBooleanCutoff c sets block v sel ψ r κ) :=
    jointBooleanGoodWeight_measure c sets block v sel ψ hψ hrange hzero r hr κ hκ
  exact cutoff_loss_of_density_mass (X := JointBlockParameter B h α → ℝ)
    (jointBooleanSource (B := B) (α := α) h) volume
    (jointBooleanCutoff c sets block v sel ψ r κ) (jointBooleanGoodWeight c sets block v sel ψ r κ)
    hχ hχ01 hwi hw0 hlaw hmass

theorem jointBoolean_regularization_error {D α : Type*}
    [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    [∀ d, Fintype (O d)] [∀ d, DecidableEq (O d)]
    (h : D → ℕ) (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α)
    (hcard : ∀ d o, (sets d o).card ≤ h d)
    (C : D → ℝ) (hC : ∀ d, 0 ≤ C d) (hc : ∀ d o, |c d (block d o)| ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (r : ∀ d, B d × Fin (h d) → ℝ) (hr : ∀ d i, 0 < r d i)
    (κ : D → ℝ) (hκ : ∀ d, 0 < κ d) {η : ℝ}
    (hmass : 1-η ≤ ∫ x, jointBooleanGoodWeight c sets block v sel ψ r κ x)
    (δ : ℝ≥0) (hδ : 0 < δ) (φ : ((Σ d, O d) → ℝ) → ℝ)
    (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    |(∫ x, regularizedImageDensity (jointBooleanSource h) (jointBooleanSampler h c sets) δ x*φ x) -
      mappedTest (jointBooleanSource h) (jointBooleanSampler h c sets) φ| ≤
      2*η+jointBooleanTranslationBudget (O := O) (α := α) h C A T r κ*δ := by
  have htrans := jointBooleanGoodWeight_translation_budget h c sets block hblock v sel hcard C hC hc
    ψ hψ hrange hzero A T hLip hTransition r hr κ hκ
  have hcut := jointBooleanCutoff_loss c sets block v sel ψ hψ hrange hzero r hr κ hκ hmass
  exact regularizedImageDensity_cutoff_error (jointBooleanSource h) (jointBooleanCutoff c sets block v sel ψ r κ)
    (jointBooleanCutoff_contDiff c sets block v sel ψ hψ r κ).continuous.measurable
    (jointBooleanCutoff_range c sets block v sel ψ hrange r κ)
    (jointBooleanSampler h c sets) (jointBooleanSampler_contDiff h c sets).continuous.measurable
    (jointBooleanTranslationBudget (O := O) (α := α) h C A T r κ) htrans hcut δ hδ φ hφ hbound

end Erdos3

end

end OAI
