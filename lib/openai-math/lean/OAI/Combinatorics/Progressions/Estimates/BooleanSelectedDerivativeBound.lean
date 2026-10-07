/- Modified for ProveIt: prove finite regularity below infinity explicitly
for the older ContDiff order API. Mathematical statements unchanged. -/
import OAI.Combinatorics.Progressions.Estimates.BooleanMinorDimension
import OAI.Combinatorics.Progressions.Estimates.FiniteInversePerturbation
import OAI.Combinatorics.Progressions.Geometry.CutoffBoxImageComparison
import OAI.Combinatorics.Progressions.Geometry.ImageCoordinateDerivative
import OAI.Combinatorics.Progressions.Geometry.LocalCoordinateDivergence
import OAI.Combinatorics.Progressions.Linear.SelectedCoordinateMatrix
import OAI.Combinatorics.Progressions.Polynomial.PolynomialParameterContinuity

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]

theorem imageTranslationBound_of_weighted_fields
    (U : (κ → ℝ) → (ι → ℝ)) (hU : ContDiff ℝ 1 U)
    (w : (κ → ℝ) → ℝ) (hw : Measurable w) (hwi : Integrable w) (hw0 : ∀ x, 0 ≤ w x)
    (Q : ι → κ → (κ → ℝ) → ℝ) (hQ : ∀ i j, ContDiff ℝ 1 (Q i j))
    (hs : ∀ i j, HasCompactSupport (Q i j))
    (hcolumn : ∀ i x, fderiv ℝ U x (fun j => Q i j x) = w x • Pi.single i 1)
    (B : ι → ℝ≥0) (hdiv : ∀ i, (∫ x, |coordinateDivergence (Q i) x|) ≤ B i) :
    ImageTranslationBound (realDensityMeasure volume w) U (∑ i, B i) := by
  let : IsFiniteMeasure (realDensityMeasure volume w) := realDensityMeasure_finite volume w hwi hw0
  apply imageTranslationBound_of_coordinate_derivatives _ U hU.continuous.measurable B
  intro φ hc _ hb i
  exact weighted_image_derivative_bound U hU w hw hw0 (Q i) (hQ i) (hs i)
    (Pi.single i 1) (hcolumn i) (hdiv i) φ (hc.of_le (by simp)) hb

theorem imageTranslationBound_of_right_inverse_fields
    (U : (κ → ℝ) → (ι → ℝ)) (hU : ContDiff ℝ 1 U)
    (w : (κ → ℝ) → ℝ) (hw : ContDiff ℝ 1 w) (hws : HasCompactSupport w) (hw0 : ∀ x, 0 ≤ w x)
    (V : ι → κ → (κ → ℝ) → ℝ) (hV : ∀ i j, ContDiff ℝ 1 (V i j))
    (hcolumn : ∀ i x, w x ≠ 0 → fderiv ℝ U x (fun j => V i j x) = Pi.single i 1)
    (B : ι → ℝ≥0)
    (hdiv : ∀ i, (∫ x, |coordinateDivergence (fun j x => w x * V i j x) x|) ≤ B i) :
    ImageTranslationBound (realDensityMeasure volume w) U (∑ i, B i) := by
  apply imageTranslationBound_of_weighted_fields U hU w hw.continuous.measurable
    (hw.continuous.integrable_of_hasCompactSupport hws) hw0
    (fun i j x => w x * V i j x) (fun i j => hw.mul (hV i j)) (fun _ _ => hws.mul_right)
    _ B hdiv
  intro i x
  change fderiv ℝ U x (w x • (fun j => V i j x)) = _
  rw [map_smul]
  by_cases hx : w x = 0
  · simp only [hx, zero_smul]
  · rw [hcolumn i x hx]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]

theorem divergence_image_comparison
    (ρ χ : (κ → ℝ) → ℝ) (hρ : Measurable ρ) (hρi : Integrable ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρmass : (∫ x, ρ x) = 1)
    (hχ : Measurable χ) (hχ01 : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (F : Fin 2 → (κ → ℝ) → (ι → ℝ)) (hF : ∀ t, ContDiff ℝ 1 (F t))
    (Q : Fin 2 → ι → κ → (κ → ℝ) → ℝ)
    (hQ : ∀ t i j, ContDiff ℝ 1 (Q t i j)) (hs : ∀ t i j, HasCompactSupport (Q t i j))
    (hcolumn : ∀ t i x, fderiv ℝ (F t) x (fun j => Q t i j x) = (ρ x * χ x) • Pi.single i 1)
    (B : ℝ≥0) (hdiv : ∀ t i, (∫ x, |coordinateDivergence (Q t i) x|) ≤ B)
    {ε η : ℝ} (hε : 0 ≤ ε) (hcut : (∫ x, ρ x * (1 - χ x)) ≤ η)
    (hclose : ∀ x, ρ x * χ x ≠ 0 → dist (F 0 x) (F 1 x) ≤ ε)
    (δ : ℝ) (hδ : 0 < δ) (φ : (ι → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    |(∫ x, ρ x * φ (F 0 x)) - ∫ x, ρ x * φ (F 1 x)| ≤
      2 * η + 2 * (Fintype.card ι : ℝ) * B * δ + 2 * (Fintype.card ι : ℝ) * ε / δ := by
  let μ := realDensityMeasure volume ρ
  let : IsProbabilityMeasure μ := realDensityMeasure_probability volume ρ hρi hρ0 hρmass
  have hwi : Integrable (fun x => ρ x * χ x) := hρi.mul_bdd hχ.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_of_nonneg (hχ01 x).1]
      exact (hχ01 x).2))
  have hT (t : Fin 2) : ImageTranslationBound (realDensityMeasure μ χ) (F t)
      ((Fintype.card ι : ℝ≥0) * B) := by
    rw [realDensityMeasure_mul volume ρ χ hρ hχ hρ0]
    have h := imageTranslationBound_of_weighted_fields (F t) (hF t) (fun x => ρ x * χ x)
      (hρ.mul hχ) hwi (fun x => mul_nonneg (hρ0 x) (hχ01 x).1) (Q t) (hQ t) (hs t)
      (hcolumn t) (fun _ => B) (hdiv t)
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using h
  have hcut' : (∫ x, 1 - χ x ∂μ) ≤ η := by
    rw [realDensityMeasure_integral volume ρ hρ hρ0]
    exact hcut
  have hclose' : ∀ᵐ x ∂realDensityMeasure μ χ, dist (F 0 x) (F 1 x) ≤ ε := by
    rw [realDensityMeasure_mul volume ρ χ hρ hχ hρ0]
    exact ae_realDensityMeasure_of_forall_nonzero volume _ (hρ.mul hχ) _ hclose
  have h := cutoff_box_image_comparison μ χ hχ hχ01 (F 0) (F 1)
    (hF 0).continuous.measurable (hF 1).continuous.measurable _ _ (hT 0) (hT 1)
    hε hcut' hclose' δ hδ φ hφ hbound
  unfold mappedTest at h
  rw [realDensityMeasure_integral volume ρ hρ hρ0, realDensityMeasure_integral volume ρ hρ hρ0] at h
  apply h.trans_eq
  push_cast
  ring

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators ContDiff

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι]

theorem local_weighted_image_derivative_identity
    (U : (κ → ℝ) → (ι → ℝ)) (w : (κ → ℝ) → ℝ)
    (hU : ∀ x ∈ tsupport w, ContDiffAt ℝ 1 U x)
    (Q : κ → (κ → ℝ) → ℝ) (hQ : ∀ j, ContDiff ℝ 1 (Q j))
    (hs : ∀ j, HasCompactSupport (Q j)) (hQs : ∀ j, tsupport (Q j) ⊆ tsupport w)
    (z : ι → ℝ) (hcolumn : ∀ x, fderiv ℝ U x (fun j => Q j x) = w x • z)
    (φ : (ι → ℝ) → ℝ) (hφ : ContDiff ℝ 1 φ) :
    (∫ x, w x * fderiv ℝ φ (U x) z) = -∫ x, coordinateDivergence Q x * φ (U x) := by
  have hpoint (x : κ → ℝ) : fderiv ℝ (fun x => φ (U x)) x (fun j => Q j x) =
      w x * fderiv ℝ φ (U x) z := by
    by_cases hx : x ∈ tsupport w
    · change fderiv ℝ (φ ∘ U) x (fun j => Q j x) = _
      rw [fderiv_comp x (hφ.differentiable (by norm_num) _) ((hU x hx).differentiableAt (by norm_num)),
        ContinuousLinearMap.comp_apply, hcolumn, map_smul, smul_eq_mul]
    · have hw0 : w x = 0 := image_eq_zero_of_notMem_tsupport hx
      have hQ0 : (fun j => Q j x) = 0 := funext fun j =>
        image_eq_zero_of_notMem_tsupport (fun h => hx (hQs j h))
      rw [hQ0, map_zero, hw0, zero_mul]
  have h := local_coordinate_vectorField_integration_by_parts Q hQ hs (fun x => φ (U x))
    (fun j x hx => hφ.contDiffAt.comp x (hU x (hQs j hx)))
  simpa only [hpoint] using h

theorem local_weighted_image_derivative_bound
    (U : (κ → ℝ) → (ι → ℝ)) (w : (κ → ℝ) → ℝ)
    (hU : ∀ x ∈ tsupport w, ContDiffAt ℝ 1 U x) (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
    (Q : κ → (κ → ℝ) → ℝ) (hQ : ∀ j, ContDiff ℝ 1 (Q j))
    (hs : ∀ j, HasCompactSupport (Q j)) (hQs : ∀ j, tsupport (Q j) ⊆ tsupport w)
    (z : ι → ℝ) (hcolumn : ∀ x, fderiv ℝ U x (fun j => Q j x) = w x • z)
    {B : ℝ} (hdiv : (∫ x, |coordinateDivergence Q x|) ≤ B)
    (φ : (ι → ℝ) → ℝ) (hφ : ContDiff ℝ 1 φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    |∫ x, fderiv ℝ φ (U x) z ∂realDensityMeasure volume w| ≤ B := by
  rw [realDensityMeasure_integral volume w hw hw0,
    local_weighted_image_derivative_identity U w hU Q hQ hs hQs z hcolumn φ hφ, abs_neg]
  have hi : Integrable (coordinateDivergence Q) volume :=
    (coordinateDivergence_continuous Q hQ).integrable_of_hasCompactSupport
      (coordinateDivergence_hasCompactSupport Q hs)
  have hnorm : Integrable (fun x => |coordinateDivergence Q x|) := by
    simpa only [Real.norm_eq_abs] using hi.norm
  have hp (x : κ → ℝ) : ‖coordinateDivergence Q x * φ (U x)‖ ≤ |coordinateDivergence Q x| := by
    rw [norm_mul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_left (hbound _) (abs_nonneg _)).trans_eq (mul_one _)
  have h := norm_integral_le_of_norm_le hnorm (Filter.Eventually.of_forall hp)
  rw [Real.norm_eq_abs] at h
  exact h.trans hdiv

theorem imageTranslationBound_of_local_weighted_fields [DecidableEq ι]
    (U : (κ → ℝ) → (ι → ℝ)) (hm : Measurable U) (w : (κ → ℝ) → ℝ)
    (hU : ∀ x ∈ tsupport w, ContDiffAt ℝ 1 U x)
    (hw : Measurable w) (hwi : Integrable w) (hw0 : ∀ x, 0 ≤ w x)
    (Q : ι → κ → (κ → ℝ) → ℝ) (hQ : ∀ i j, ContDiff ℝ 1 (Q i j))
    (hs : ∀ i j, HasCompactSupport (Q i j)) (hQs : ∀ i j, tsupport (Q i j) ⊆ tsupport w)
    (hcolumn : ∀ i x, fderiv ℝ U x (fun j => Q i j x) = w x • Pi.single i 1)
    (B : ι → ℝ≥0) (hdiv : ∀ i, (∫ x, |coordinateDivergence (Q i) x|) ≤ B i) :
    ImageTranslationBound (realDensityMeasure volume w) U (∑ i, B i) := by
  let : IsFiniteMeasure (realDensityMeasure volume w) := realDensityMeasure_finite volume w hwi hw0
  apply imageTranslationBound_of_coordinate_derivatives _ U hm B
  intro φ hc _ hb i
  exact local_weighted_image_derivative_bound U w hU hw hw0 (Q i) (hQ i) (hs i) (hQs i)
    (Pi.single i 1) (hcolumn i) (hdiv i) φ (hc.of_le (by simp)) hb

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped Topology NNReal BigOperators

theorem contDiff_mul_of_local_right {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : E → ℝ} (hf : ContDiff ℝ 1 f)
    (hg : ∀ x ∈ tsupport f, ContDiffAt ℝ 1 g x) : ContDiff ℝ 1 (fun x => f x * g x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport f
  · exact hf.contDiffAt.mul (hg x hx)
  · have hz := notMem_tsupport_iff_eventuallyEq.mp hx
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [hz] with y hy
    simp only [hy, Pi.zero_apply, zero_mul]

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]

noncomputable def selectedDerivative (U : (κ → ℝ) → (ι → ℝ))
    (J : (ι → ℝ) →L[ℝ] (κ → ℝ)) (x : κ → ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  (fderiv ℝ U x).comp J

noncomputable def selectedInverseField (U : (κ → ℝ) → (ι → ℝ))
    (J : (ι → ℝ) →L[ℝ] (κ → ℝ)) (i : ι) (j : κ) (x : κ → ℝ) : ℝ :=
  J ((selectedDerivative U J x).inverse (Pi.single i 1)) j

theorem selectedInverseField_contDiffAt (U : (κ → ℝ) → (ι → ℝ)) (hU : ContDiff ℝ 2 U)
    (J : (ι → ℝ) →L[ℝ] (κ → ℝ)) {x : κ → ℝ}
    (hx : (selectedDerivative U J x).IsInvertible) (i : ι) (j : κ) :
    ContDiffAt ℝ 1 (selectedInverseField U J i j) x := by
  have hA : ContDiff ℝ 1 (selectedDerivative U J) :=
    (hU.fderiv_right (by norm_num)).clm_comp contDiff_const
  have hi : ContDiffAt ℝ 1 (fun y => (selectedDerivative U J y).inverse) x :=
    hx.contDiffAt_map_inverse.comp x hA.contDiffAt
  have hv : ContDiffAt ℝ 1 (fun y => J ((selectedDerivative U J y).inverse (Pi.single i 1))) x :=
    J.contDiff.contDiffAt.comp x (hi.clm_apply contDiffAt_const)
  exact (contDiffAt_apply ℝ ℝ j _).comp x hv

omit [Fintype κ] [Fintype ι] in
theorem selectedInverseField_column (U : (κ → ℝ) → (ι → ℝ))
    (J : (ι → ℝ) →L[ℝ] (κ → ℝ)) {x : κ → ℝ}
    (hx : (selectedDerivative U J x).IsInvertible) (i : ι) :
    fderiv ℝ U x (fun j => selectedInverseField U J i j x) = Pi.single i 1 := by
  change selectedDerivative U J x ((selectedDerivative U J x).inverse (Pi.single i 1)) = _
  exact hx.self_apply_inverse _

theorem selectedWeightedField_spec (U : (κ → ℝ) → (ι → ℝ)) (hU : ContDiff ℝ 2 U)
    (J : (ι → ℝ) →L[ℝ] (κ → ℝ)) (w : (κ → ℝ) → ℝ) (hw : ContDiff ℝ 1 w)
    (hws : HasCompactSupport w)
    (hinv : ∀ x ∈ tsupport w, (selectedDerivative U J x).IsInvertible) :
    (∀ i j, ContDiff ℝ 1 (fun x => w x * selectedInverseField U J i j x)) ∧
      (∀ i j, HasCompactSupport (fun x => w x * selectedInverseField U J i j x)) ∧
      (∀ i x, fderiv ℝ U x (fun j => w x * selectedInverseField U J i j x) = w x • Pi.single i 1) := by
  refine ⟨fun i j => contDiff_mul_of_local_right hw (fun x hx =>
      selectedInverseField_contDiffAt U hU J (hinv x hx) i j),
    fun _ _ => hws.mul_right, ?_⟩
  intro i x
  change fderiv ℝ U x (w x • (fun j => selectedInverseField U J i j x)) = _
  rw [map_smul]
  by_cases hx : w x = 0
  · simp only [hx, zero_smul]
  · rw [selectedInverseField_column U J (hinv x (subset_tsupport w hx))]

theorem imageTranslationBound_of_selected_inverse [DecidableEq κ]
    (U : (κ → ℝ) → (ι → ℝ)) (hU : ContDiff ℝ 2 U)
    (J : (ι → ℝ) →L[ℝ] (κ → ℝ)) (w : (κ → ℝ) → ℝ) (hw : ContDiff ℝ 1 w)
    (hws : HasCompactSupport w) (hw0 : ∀ x, 0 ≤ w x)
    (hinv : ∀ x ∈ tsupport w, (selectedDerivative U J x).IsInvertible) (B : ι → ℝ≥0)
    (hdiv : ∀ i, (∫ x, |coordinateDivergence (fun j x => w x * selectedInverseField U J i j x) x|) ≤ B i) :
    ImageTranslationBound (realDensityMeasure volume w) U (∑ i, B i) := by
  obtain ⟨hc, hs, hcolumn⟩ := selectedWeightedField_spec U hU J w hw hws hinv
  exact imageTranslationBound_of_weighted_fields U (hU.of_le (by norm_num)) w
    hw.continuous.measurable (hw.continuous.integrable_of_hasCompactSupport hws) hw0
    (fun i j x => w x * selectedInverseField U J i j x) hc hs hcolumn B hdiv

end Erdos3

end

section

namespace Erdos3

noncomputable def booleanSelectedInjection {B O F α : Type*}
    [Fintype O] [DecidableEq B] [DecidableEq F] [DecidableEq α]
    (block : O → B) (v : F) (r : O → Option α) :
    (O → ℝ) →L[ℝ] (BlockParameter B F α → ℝ) :=
  coordinateInjection (fun col => (block col, v, r col))

theorem booleanSelectedInjection_norm_le {B O F α : Type*}
    [Fintype B] [Fintype O] [Fintype F] [Fintype α]
    [DecidableEq B] [DecidableEq F] [DecidableEq α]
    (block : O → B) (hblock : Function.Injective block) (v : F) (r : O → Option α) :
    ‖booleanSelectedInjection block v r‖ ≤ 1 := by
  apply coordinateInjection_norm_le
  intro i j hij
  exact hblock (congrArg Prod.fst hij)

theorem booleanSelectedDerivative_eq {B O F α : Type*}
    [Fintype B] [Fintype O] [Fintype F] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq F] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (block : O → B) (v : F) (r : O → Option α)
    (a : BlockParameter B F α → ℝ) :
    selectedDerivative (booleanSamplerMap (F := F) c sets) (booleanSelectedInjection block v r) a =
      matrixSupCLM ((booleanSelectedMinor c sets block v r).map (MvPolynomial.eval a)) := by
  unfold selectedDerivative booleanSelectedInjection
  rw [clm_coordinateInjection_matrix]
  apply congrArg matrixSupCLM
  funext row col
  exact booleanSelectedMinor_fderiv c sets block v r a row col

noncomputable def productMinorInverseBound (j q h : ℕ) (C R κ : ℝ) : ℝ :=
  j * (j.factorial * (productMinorEntryBound q h C R) ^ (j - 1) / κ)

theorem productMinorInverseBound_nonneg (j q h : ℕ) {C R κ : ℝ}
    (hC : 0 ≤ C) (hR : 0 ≤ R) (hκ : 0 ≤ κ) :
    0 ≤ productMinorInverseBound j q h C R κ := by
  have hH := productMinorEntryBound_nonneg q h hC hR
  unfold productMinorInverseBound
  positivity

theorem boolean_selected_inverse_bound {B O α : Type*}
    [Fintype B] [Fintype O] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (block : O → B) {h : ℕ}
    (v : Fin h) (r : O → Option α) (hcard : ∀ o, (sets o).card ≤ h)
    (a : BlockParameter B (Fin h) α → ℝ) {C R κ : ℝ}
    (hC : 0 ≤ C) (hR : 0 ≤ R) (hc : ∀ o, |c (block o)| ≤ C) (ha : ∀ j, |a j| ≤ R)
    (hκ : 0 < κ)
    (hdet : κ ≤ |((booleanSelectedMinor c sets block v r).map (MvPolynomial.eval a)).det|) :
    (selectedDerivative (booleanSamplerMap c sets) (booleanSelectedInjection block v r) a).IsInvertible ∧
      ‖(selectedDerivative (booleanSamplerMap c sets) (booleanSelectedInjection block v r) a).inverse‖ ≤
        productMinorInverseBound (Fintype.card O) (Fintype.card α) h C R κ := by
  rw [booleanSelectedDerivative_eq]
  exact matrixSupCLM_inverse_norm_le _ (productMinorEntryBound_nonneg _ _ hC hR)
    (booleanSelectedMinor_entry_bound c sets block v r hcard a hC hR hc ha) hκ hdet

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]

theorem selectedInverseField_contDiffAt_of_local
    (U : (κ → ℝ) → (ι → ℝ)) (J : (ι → ℝ) →L[ℝ] (κ → ℝ)) {x : κ → ℝ}
    (hU : ContDiffAt ℝ 2 U x) (hx : (selectedDerivative U J x).IsInvertible) (i : ι) (j : κ) :
    ContDiffAt ℝ 1 (selectedInverseField U J i j) x := by
  have hA : ContDiffAt ℝ 1 (selectedDerivative U J) x :=
    (hU.fderiv_right (by norm_num)).clm_comp contDiffAt_const
  have hi : ContDiffAt ℝ 1 (fun y => (selectedDerivative U J y).inverse) x :=
    hx.contDiffAt_map_inverse.comp x hA
  have hv : ContDiffAt ℝ 1 (fun y => J ((selectedDerivative U J y).inverse (Pi.single i 1))) x :=
    J.contDiff.contDiffAt.comp x (hi.clm_apply contDiffAt_const)
  exact (contDiffAt_apply ℝ ℝ j _).comp x hv

theorem local_selectedWeightedField_spec
    (U : (κ → ℝ) → (ι → ℝ)) (J : (ι → ℝ) →L[ℝ] (κ → ℝ))
    (w : (κ → ℝ) → ℝ) (hw : ContDiff ℝ 1 w) (hws : HasCompactSupport w)
    (hU : ∀ x ∈ tsupport w, ContDiffAt ℝ 2 U x)
    (hinv : ∀ x ∈ tsupport w, (selectedDerivative U J x).IsInvertible) :
    (∀ i j, ContDiff ℝ 1 (fun x => w x * selectedInverseField U J i j x)) ∧
      (∀ i j, HasCompactSupport (fun x => w x * selectedInverseField U J i j x)) ∧
      (∀ i j, tsupport (fun x => w x * selectedInverseField U J i j x) ⊆ tsupport w) ∧
      (∀ i x, fderiv ℝ U x (fun j => w x * selectedInverseField U J i j x) = w x • Pi.single i 1) := by
  refine ⟨fun i j => contDiff_mul_of_local_right hw (fun x hx =>
      selectedInverseField_contDiffAt_of_local U J (hU x hx) (hinv x hx) i j),
    fun _ _ => hws.mul_right, ?_, ?_⟩
  · intro i j
    exact tsupport_smul_subset_left w (selectedInverseField U J i j)
  · intro i x
    change fderiv ℝ U x (w x • (fun j => selectedInverseField U J i j x)) = _
    rw [map_smul]
    by_cases hx : w x = 0
    · simp only [hx, zero_smul]
    · rw [selectedInverseField_column U J (hinv x (subset_tsupport w hx))]

theorem imageTranslationBound_of_local_selected_inverse [DecidableEq κ]
    (U : (κ → ℝ) → (ι → ℝ)) (hm : Measurable U) (J : (ι → ℝ) →L[ℝ] (κ → ℝ))
    (w : (κ → ℝ) → ℝ) (hw : ContDiff ℝ 1 w) (hws : HasCompactSupport w) (hw0 : ∀ x, 0 ≤ w x)
    (hU : ∀ x ∈ tsupport w, ContDiffAt ℝ 2 U x)
    (hinv : ∀ x ∈ tsupport w, (selectedDerivative U J x).IsInvertible) (B : ι → ℝ≥0)
    (hdiv : ∀ i, (∫ x, |coordinateDivergence (fun j x => w x * selectedInverseField U J i j x) x|) ≤ B i) :
    ImageTranslationBound (realDensityMeasure volume w) U (∑ i, B i) := by
  obtain ⟨hc, hs, hQs, hcolumn⟩ := local_selectedWeightedField_spec U J w hw hws hU hinv
  exact imageTranslationBound_of_local_weighted_fields U hm w
    (fun x hx => (hU x hx).of_le (by norm_num)) hw.continuous.measurable
    (hw.continuous.integrable_of_hasCompactSupport hws) hw0
    (fun i j x => w x * selectedInverseField U J i j x) hc hs hQs hcolumn B hdiv

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem selected_inverse_image_comparison_sqrt
    {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    (ρ χ : (κ → ℝ) → ℝ) (hρ : Measurable ρ) (hρi : Integrable ρ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρmass : (∫ x, ρ x) = 1)
    (hχ : Measurable χ) (hχ01 : ∀ x, χ x ∈ Set.Icc (0 : ℝ) 1)
    (hw : ContDiff ℝ 1 (fun x => ρ x * χ x)) (hws : HasCompactSupport (fun x => ρ x * χ x))
    (F : Fin 2 → (κ → ℝ) → (ι → ℝ)) (hF : ∀ t, ContDiff ℝ 2 (F t))
    (J : (ι → ℝ) →L[ℝ] (κ → ℝ))
    (hinv : ∀ t x, x ∈ tsupport (fun x => ρ x * χ x) → (selectedDerivative (F t) J x).IsInvertible)
    (B : ℝ≥0) (hB : 0 < (B : ℝ))
    (hdiv : ∀ t i, (∫ x, |coordinateDivergence
      (fun j x => (ρ x * χ x) * selectedInverseField (F t) J i j x) x|) ≤ B)
    {ε η : ℝ} (hε : 0 < ε) (hcut : (∫ x, ρ x * (1 - χ x)) ≤ η)
    (hclose : ∀ x, ρ x * χ x ≠ 0 → dist (F 0 x) (F 1 x) ≤ ε)
    (φ : (ι → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    |(∫ x, ρ x * φ (F 0 x)) - ∫ x, ρ x * φ (F 1 x)| ≤
      2 * η + 4 * (Fintype.card ι : ℝ) * Real.sqrt ((B : ℝ) * ε) := by
  have hfields (t : Fin 2) := selectedWeightedField_spec (F t) (hF t) J
    (fun x => ρ x * χ x) hw hws (hinv t)
  have h := divergence_image_comparison ρ χ hρ hρi hρ0 hρmass hχ hχ01 F
    (fun t => (hF t).of_le (by norm_num))
    (fun t i j x => (ρ x * χ x) * selectedInverseField (F t) J i j x)
    (fun t => (hfields t).1) (fun t => (hfields t).2.1) (fun t => (hfields t).2.2)
    B hdiv hε.le hcut hclose (Real.sqrt (ε / (B : ℝ)))
    (Real.sqrt_pos.mpr (div_pos hε hB)) φ hφ hbound
  apply h.trans_eq
  have hbal := sqrt_smoothing_balance hB hε
  calc
    2 * η + 2 * (Fintype.card ι : ℝ) * B * Real.sqrt (ε / (B : ℝ)) +
        2 * (Fintype.card ι : ℝ) * ε / Real.sqrt (ε / (B : ℝ)) =
      2 * η + 2 * (Fintype.card ι : ℝ) *
        ((B : ℝ) * Real.sqrt (ε / (B : ℝ)) + ε / Real.sqrt (ε / (B : ℝ))) := by ring
    _ = 2 * η + 4 * (Fintype.card ι : ℝ) * Real.sqrt ((B : ℝ) * ε) := by rw [hbal]; ring

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {κ ι : Type*} [Fintype κ] [Fintype ι]

theorem selectedDerivative_sub_norm_le
    (U V : (κ → ℝ) → (ι → ℝ)) (J : (ι → ℝ) →L[ℝ] (κ → ℝ)) (x : κ → ℝ) :
    ‖selectedDerivative V J x - selectedDerivative U J x‖ ≤
      ‖fderiv ℝ V x - fderiv ℝ U x‖ * ‖J‖ := by
  unfold selectedDerivative
  rw [← ContinuousLinearMap.sub_comp]
  exact (fderiv ℝ V x - fderiv ℝ U x).opNorm_comp_le J

theorem selected_inverse_perturbation
    (U V : (κ → ℝ) → (ι → ℝ)) (J : (ι → ℝ) →L[ℝ] (κ → ℝ)) (x : κ → ℝ)
    (hinv : (selectedDerivative U J x).IsInvertible) (K : ℝ≥0)
    (hK : ‖(selectedDerivative U J x).inverse‖ ≤ K)
    (hsmall : (K : ℝ) * (‖fderiv ℝ V x - fderiv ℝ U x‖ * ‖J‖) ≤ 1 / 2) :
    (selectedDerivative V J x).IsInvertible ∧
      ‖(selectedDerivative V J x).inverse‖ ≤ 2 * (K : ℝ) := by
  apply inverse_perturbation_bound (selectedDerivative U J x) (selectedDerivative V J x) hinv K hK
  exact (mul_le_mul_of_nonneg_left (selectedDerivative_sub_norm_le U V J x) K.coe_nonneg).trans hsmall

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

theorem booleanSelectedInjection_single {B O F α : Type*}
    [Fintype O] [DecidableEq O] [DecidableEq B] [DecidableEq F] [DecidableEq α]
    (block : O → B) (v : F) (r : O → Option α) (col : O) :
    booleanSelectedInjection block v r (Pi.single col 1) = Pi.single (block col, v, r col) 1 :=
  coordinateInjection_single _ col

theorem booleanSelectedDerivative_entry {B O F α : Type*}
    [Fintype B] [Fintype O] [Fintype F] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq F] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (block : O → B) (v : F) (r : O → Option α)
    (a : BlockParameter B F α → ℝ) (row col : O) :
    selectedDerivative (booleanSamplerMap c sets) (booleanSelectedInjection block v r) a
      (Pi.single col 1) row = MvPolynomial.eval a (booleanSelectedMinor c sets block v r row col) := by
  change fderiv ℝ (booleanSamplerMap c sets) a
    (booleanSelectedInjection block v r (Pi.single col 1)) row = _
  rw [booleanSelectedInjection_single]
  exact booleanSelectedMinor_fderiv c sets block v r a row col

theorem booleanSelectedDerivative_contDiff {B O F α : Type*}
    [Fintype B] [Fintype O] [Fintype F] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq F] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (block : O → B) (v : F) (r : O → Option α) :
    ContDiff ℝ 1 (selectedDerivative (booleanSamplerMap c sets) (booleanSelectedInjection block v r)) := by
  have hU : ContDiff ℝ 2 (booleanSamplerMap (F := F) c sets) :=
    (booleanSamplerMap_contDiff c sets).of_le (WithTop.coe_le_coe.mpr le_top)
  exact (hU.fderiv_right (by norm_num)).clm_comp contDiff_const

def productMinorDerivativeBound (n j q h : ℕ) (C R : ℝ) : ℝ :=
  n * (j * productMinorPartialBound q h C R)

theorem productMinorDerivativeBound_nonneg (n j q h : ℕ) {C R : ℝ}
    (hC : 0 ≤ C) (hR : 0 ≤ R) : 0 ≤ productMinorDerivativeBound n j q h C R := by
  have hM := productMinorPartialBound_nonneg q h hC hR
  unfold productMinorDerivativeBound
  positivity

theorem boolean_selected_derivative_bound {B O α : Type*}
    [Fintype B] [Fintype O] [Fintype α]
    [DecidableEq B] [DecidableEq O] [DecidableEq α]
    (c : B → ℝ) (sets : O → Finset α) (block : O → B) {h : ℕ}
    (v : Fin h) (r : O → Option α) (hcard : ∀ o, (sets o).card ≤ h)
    (a : BlockParameter B (Fin h) α → ℝ) {C R : ℝ} (hC : 0 ≤ C) (hR : 1 ≤ R)
    (hc : ∀ o, |c (block o)| ≤ C) (ha : ∀ j, |a j| ≤ R) :
    ‖fderiv ℝ (selectedDerivative (booleanSamplerMap c sets) (booleanSelectedInjection block v r)) a‖ ≤
      productMinorDerivativeBound (Fintype.card (BlockParameter B (Fin h) α))
        (Fintype.card O) (Fintype.card α) h C R := by
  have hA := (booleanSelectedDerivative_contDiff c sets block v r).differentiable (by norm_num)
  exact polynomialOperator_fderiv_norm_le
    (selectedDerivative (booleanSamplerMap c sets) (booleanSelectedInjection block v r))
    (booleanSelectedMinor c sets block v r) (booleanSelectedDerivative_entry c sets block v r)
    a (hA a) (productMinorPartialBound_nonneg _ _ hC (zero_le_one.trans hR))
    (booleanSelectedMinor_partial_bound c sets block v r hcard a hC hR hc ha)

end Erdos3

end

end OAI
