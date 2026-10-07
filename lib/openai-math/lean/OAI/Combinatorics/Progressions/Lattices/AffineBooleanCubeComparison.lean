/- Modified for ProveIt: prove finite regularity below infinity explicitly
for the older ContDiff order API. Mathematical statements unchanged. -/
import OAI.Combinatorics.Progressions.Estimates.JointBooleanStability
import OAI.Combinatorics.Progressions.Lattices.AffineCubeMinorGoodMass

namespace OAI

section

namespace Erdos3

variable {I O : Type*} [Fintype I] [fintypeO : Fintype O]

noncomputable def affineSelectedInjection (L : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (J : (O → ℝ) →L[ℝ] (I → ℝ)) (δ : ℝ) : (O → ℝ) →L[ℝ] (I → ℝ) :=
  δ • (L.symm.toContinuousLinearMap.comp J)

theorem affineSelectedInjection_norm_le (L : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (J : (O → ℝ) →L[ℝ] (I → ℝ)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hL : δ * ‖L.symm.toContinuousLinearMap‖ ≤ 1) (hJ : ‖J‖ ≤ 1) :
    ‖affineSelectedInjection L J δ‖ ≤ 1 := by
  unfold affineSelectedInjection
  rw [norm_smul, Real.norm_of_nonneg hδ]
  calc
    _ ≤ δ * (‖L.symm.toContinuousLinearMap‖ * ‖J‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) hδ
    _ = (δ * ‖L.symm.toContinuousLinearMap‖) * ‖J‖ := by ring
    _ ≤ 1 * 1 := mul_le_mul hL hJ (norm_nonneg _) zero_le_one
    _ = 1 := one_mul _

theorem selectedDerivative_affine (U : (I → ℝ) → (O → ℝ))
    (L : (I → ℝ) ≃L[ℝ] (I → ℝ)) (b : I → ℝ)
    (J : (O → ℝ) →L[ℝ] (I → ℝ)) (δ : ℝ) (x : I → ℝ)
    (hU : DifferentiableAt ℝ U (b + L x)) :
    selectedDerivative (fun y => U (b + L y)) (affineSelectedInjection L J δ) x =
      δ • selectedDerivative U J (b + L x) := by
  unfold selectedDerivative
  change (fderiv ℝ (fun y => U (b + L.toContinuousLinearMap y)) x).comp _ = _
  rw [affineSlice_fderiv U b L.toContinuousLinearMap x hU]
  ext y i
  simp [affineSelectedInjection]

omit fintypeO in
theorem invertible_smul_inverse [Fintype O] {A : (O → ℝ) →L[ℝ] (O → ℝ)}
    (hA : A.IsInvertible) {δ : ℝ} (hδ : δ ≠ 0) :
    (δ • A).IsInvertible ∧ (δ • A).inverse = δ⁻¹ • A.inverse := by
  have hr : (δ • A).comp (δ⁻¹ • A.inverse) = ContinuousLinearMap.id ℝ (O → ℝ) := by
    ext x i
    simp [smul_smul, hA.self_apply_inverse, hδ]
  have hl : (δ⁻¹ • A.inverse).comp (δ • A) = ContinuousLinearMap.id ℝ (O → ℝ) := by
    ext x i
    simp [smul_smul, hA.inverse_apply_self, hδ]
  exact ⟨ContinuousLinearMap.IsInvertible.of_inverse hr hl, ContinuousLinearMap.inverse_eq hr hl⟩

theorem selectedDerivative_affine_inverse_bound (U : (I → ℝ) → (O → ℝ))
    (L : (I → ℝ) ≃L[ℝ] (I → ℝ)) (b : I → ℝ)
    (J : (O → ℝ) →L[ℝ] (I → ℝ)) {δ K : ℝ} (hδ : 0 < δ) (x : I → ℝ)
    (hU : DifferentiableAt ℝ U (b + L x))
    (hinv : (selectedDerivative U J (b + L x)).IsInvertible)
    (hK : ‖(selectedDerivative U J (b + L x)).inverse‖ ≤ K) :
    (selectedDerivative (fun y => U (b + L y)) (affineSelectedInjection L J δ) x).IsInvertible ∧
      ‖(selectedDerivative (fun y => U (b + L y))
        (affineSelectedInjection L J δ) x).inverse‖ ≤ δ⁻¹ * K := by
  rw [selectedDerivative_affine U L b J δ x hU]
  obtain ⟨hi, he⟩ := invertible_smul_inverse hinv hδ.ne'
  refine ⟨hi, ?_⟩
  rw [he, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hδ.le)]
  exact mul_le_mul_of_nonneg_left hK (inv_nonneg.mpr hδ.le)

theorem selectedDerivative_affine_derivative_bound (U : (I → ℝ) → (O → ℝ))
    (hU : ContDiff ℝ 2 U) (L : (I → ℝ) ≃L[ℝ] (I → ℝ)) (b : I → ℝ)
    (J : (O → ℝ) →L[ℝ] (I → ℝ)) {δ H : ℝ} (hδ : 0 ≤ δ) (x : I → ℝ)
    (hH : ‖fderiv ℝ (selectedDerivative U J) (b + L x)‖ ≤ H) :
    ‖fderiv ℝ (selectedDerivative (fun y => U (b + L y))
      (affineSelectedInjection L J δ)) x‖ ≤ δ * H * ‖L.toContinuousLinearMap‖ := by
  let : NormedSpace ℝ ((O → ℝ) →L[ℝ] (O → ℝ)) := ContinuousLinearMap.toNormedSpace
  let : NormedSpace ℝ ((I → ℝ) →L[ℝ] ((O → ℝ) →L[ℝ] (O → ℝ))) :=
    ContinuousLinearMap.toNormedSpace
  have hA : ContDiff ℝ 1 (selectedDerivative U J) :=
    (hU.fderiv_right (by norm_num)).clm_comp contDiff_const
  have he : selectedDerivative (fun y => U (b + L y)) (affineSelectedInjection L J δ) =
      fun y => δ • selectedDerivative U J (b + L y) := by
    funext y
    exact selectedDerivative_affine U L b J δ y (hU.differentiable (by norm_num) _)
  rw [he]
  have hd := ((hA.differentiable one_ne_zero (b + L x)).hasFDerivAt.comp x
    (L.toContinuousLinearMap.hasFDerivAt.const_add b)).const_smul δ
  change ‖fderiv ℝ (δ • selectedDerivative U J ∘
    (fun y => b + L.toContinuousLinearMap y)) x‖ ≤ _
  rw [hd.fderiv]
  calc
    _ ≤ δ * ‖(fderiv ℝ (selectedDerivative U J) (b + L x)).comp L.toContinuousLinearMap‖ := by
      simpa only [Real.norm_of_nonneg hδ] using norm_smul_le δ
        ((fderiv ℝ (selectedDerivative U J) (b + L x)).comp L.toContinuousLinearMap)
    _ ≤ δ * (‖fderiv ℝ (selectedDerivative U J) (b + L x)‖ * ‖L.toContinuousLinearMap‖) :=
      mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) hδ
    _ ≤ δ * (H * ‖L.toContinuousLinearMap‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hH (norm_nonneg _)) hδ
    _ = _ := by ring

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [decidableEqB : ∀ d, DecidableEq (B d)] [decidableEqO : ∀ d, DecidableEq (O d)] {h : D → ℕ}

noncomputable def jointAffineBooleanSampler (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α)
    (L : ∀ d, (BlockParameter (B d) (Fin (h d)) α → ℝ) ≃L[ℝ]
      (BlockParameter (B d) (Fin (h d)) α → ℝ))
    (b : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ) :
    (JointBlockParameter B h α → ℝ) → ((Σ d, O d) → ℝ) :=
  sigmaAxisSampler (fun d x => booleanSamplerMap (c d) (sets d) (b d + L d x))

noncomputable def jointAffineBooleanInjection
    (block : ∀ d, O d → B d) (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α)
    (L : ∀ d, (BlockParameter (B d) (Fin (h d)) α → ℝ) ≃L[ℝ]
      (BlockParameter (B d) (Fin (h d)) α → ℝ)) (δ : D → ℝ) :
    ((Σ d, O d) → ℝ) →L[ℝ] (JointBlockParameter B h α → ℝ) :=
  sigmaAxisOperator (fun d => affineSelectedInjection (L d)
    (booleanSelectedInjection (block d) (v d) (sel d)) (δ d))

variable (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α)
  (block : ∀ d, O d → B d) (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α)
  (L : ∀ d, (BlockParameter (B d) (Fin (h d)) α → ℝ) ≃L[ℝ]
    (BlockParameter (B d) (Fin (h d)) α → ℝ))
  (b : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ) (δ : D → ℝ)

omit decidableEqB decidableEqO in
theorem jointAffineBooleanSampler_contDiff
    [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] :
    ContDiff ℝ ∞ (jointAffineBooleanSampler c sets L b) :=
  sigmaAxisSampler_contDiff _ (fun d =>
    (booleanSamplerMap_contDiff (c d) (sets d)).comp (contDiff_const.add (L d).contDiff))

omit decidableEqO in
theorem jointAffineBooleanInjection_norm_le [∀ d, DecidableEq (O d)]
    (hblock : ∀ d, Function.Injective (block d)) (hδ : ∀ d, 0 ≤ δ d)
    (hL : ∀ d, δ d * ‖(L d).symm.toContinuousLinearMap‖ ≤ 1) :
    ‖jointAffineBooleanInjection block v sel L δ‖ ≤ 1 :=
  sigmaAxisOperator_norm_le _ zero_le_one (fun d => affineSelectedInjection_norm_le
    (L d) _ (hδ d) (hL d) (booleanSelectedInjection_norm_le (block d) (hblock d) (v d) (sel d)))

theorem jointAffineBoolean_selected_inverse_bound
    (hcard : ∀ d o, (sets d o).card ≤ h d) (x : JointBlockParameter B h α → ℝ)
    (C κ : D → ℝ) (hC : ∀ d, 0 ≤ C d) (hκ : ∀ d, 0 < κ d) (hδ : ∀ d, 0 < δ d)
    (hc : ∀ d o, |c d (block d o)| ≤ C d)
    (hx : ∀ d z, |(b d + L d (fun i => x ⟨d, i⟩)) z| ≤ 1)
    (hdet : ∀ d, κ d ≤ |booleanMinorDeterminant (c d) (sets d) (block d) (v d) (sel d)
      (b d + L d (fun i => x ⟨d, i⟩))|)
    {K : ℝ} (hK : 0 ≤ K)
    (hcap : ∀ d, (δ d)⁻¹ * productMinorInverseBound (Fintype.card (O d)) (Fintype.card α)
      (h d) (C d) 1 (κ d) ≤ K) :
    (selectedDerivative (jointAffineBooleanSampler c sets L b)
      (jointAffineBooleanInjection block v sel L δ) x).IsInvertible ∧
    ‖(selectedDerivative (jointAffineBooleanSampler c sets L b)
      (jointAffineBooleanInjection block v sel L δ) x).inverse‖ ≤ K := by
  have haxis (d) := boolean_selected_inverse_bound (c d) (sets d) (block d) (v d) (sel d)
    (hcard d) (b d + L d (fun i => x ⟨d, i⟩)) (hC d) zero_le_one (hc d) (hx d) (hκ d) (hdet d)
  have hi (d) := selectedDerivative_affine_inverse_bound (booleanSamplerMap (c d) (sets d))
    (L d) (b d) (booleanSelectedInjection (block d) (v d) (sel d)) (hδ d) (fun i => x ⟨d, i⟩)
    ((booleanSamplerMap_contDiff (c d) (sets d)).differentiable (by norm_num) _) (haxis d).1 (haxis d).2
  exact sigmaAxisSampler_inverse_bound _ _ x
    (fun d => ((booleanSamplerMap_contDiff (c d) (sets d)).comp
      (contDiff_const.add (L d).contDiff)).differentiable (by norm_num) _)
    (fun d => (hi d).1) hK (fun d => (hi d).2.trans (hcap d))

theorem jointAffineBoolean_selected_derivative_bound
    (hcard : ∀ d o, (sets d o).card ≤ h d) (x : JointBlockParameter B h α → ℝ)
    (C : D → ℝ) (hC : ∀ d, 0 ≤ C d) (hδ : ∀ d, 0 ≤ δ d) (hδone : ∀ d, δ d ≤ 1)
    (hL : ∀ d, ‖(L d).toContinuousLinearMap‖ ≤ 1)
    (hc : ∀ d o, |c d (block d o)| ≤ C d)
    (hx : ∀ d z, |(b d + L d (fun i => x ⟨d, i⟩)) z| ≤ 1)
    {H : ℝ} (hH : 0 ≤ H)
    (hcap : ∀ d, productMinorDerivativeBound (Fintype.card (BlockParameter (B d) (Fin (h d)) α))
      (Fintype.card (O d)) (Fintype.card α) (h d) (C d) 1 ≤ H) :
    ‖fderiv ℝ (selectedDerivative (jointAffineBooleanSampler c sets L b)
      (jointAffineBooleanInjection block v sel L δ)) x‖ ≤ H := by
  apply sigmaAxisSampler_selected_fderiv_norm_le _
    (fun d => ((booleanSamplerMap_contDiff (c d) (sets d)).comp
      (contDiff_const.add (L d).contDiff)).of_le (by first | exact WithTop.coe_le_coe.mpr le_top | norm_num)) _ x hH
  intro d
  have hd := selectedDerivative_affine_derivative_bound (booleanSamplerMap (c d) (sets d))
    ((booleanSamplerMap_contDiff (c d) (sets d)).of_le (by first | exact WithTop.coe_le_coe.mpr le_top | norm_num)) (L d) (b d)
    (booleanSelectedInjection (block d) (v d) (sel d)) (hδ d) (fun i => x ⟨d, i⟩)
    ((boolean_selected_derivative_bound (c d) (sets d) (block d) (v d) (sel d)
      (hcard d) (b d + L d (fun i => x ⟨d, i⟩)) (hC d) le_rfl (hc d) (hx d)).trans (hcap d))
  exact hd.trans ((mul_le_mul (mul_le_of_le_one_left hH (hδone d)) (hL d)
    (norm_nonneg _) hH).trans_eq (mul_one _))

end Erdos3

end

section

namespace Erdos3

open scoped ContDiff

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [decidableEqB : ∀ d, DecidableEq (B d)] [decidableEqO : ∀ d, DecidableEq (O d)] {h : D → ℕ}

omit decidableEqB decidableEqO in
theorem jointAffineBoolean_c2_error_transport
    [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α)
    (L : ∀ d, (BlockParameter (B d) (Fin (h d)) α → ℝ) ≃L[ℝ]
      (BlockParameter (B d) (Fin (h d)) α → ℝ))
    (b : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ)
    (hL : ∀ d, ‖(L d).toContinuousLinearMap‖ ≤ 1)
    (hbox : ∀ d x, (∀ z, |x z| ≤ 1) → ∀ z, |(b d + L d x) z| ≤ 1)
    (V : (JointBlockParameter B h α → ℝ) → ((Σ d, O d) → ℝ)) (hV : ContDiff ℝ 2 V)
    {ε : ℝ} (herr : ∀ x, (∀ z, |x z| ≤ 1) →
      ‖V x - jointBooleanSampler h c sets x‖ ≤ ε ∧
      ‖fderiv ℝ V x - fderiv ℝ (jointBooleanSampler h c sets) x‖ ≤ ε ∧
      ‖fderiv ℝ (fderiv ℝ V) x - fderiv ℝ (fderiv ℝ (jointBooleanSampler h c sets)) x‖ ≤ ε) :
    let slice := fun x : JointBlockParameter B h α → ℝ =>
      (fun s => b s.1 s.2) + sigmaAxisOperator (fun d => (L d).toContinuousLinearMap) x
    ∀ x, (∀ z, |x z| ≤ 1) →
      ‖V (slice x) - jointAffineBooleanSampler c sets L b x‖ ≤ ε ∧
      ‖fderiv ℝ (V ∘ slice) x - fderiv ℝ (jointAffineBooleanSampler c sets L b) x‖ ≤ ε ∧
      ‖fderiv ℝ (fderiv ℝ (V ∘ slice)) x -
        fderiv ℝ (fderiv ℝ (jointAffineBooleanSampler c sets L b)) x‖ ≤ ε := by
  intro slice x hx
  let b₀ : JointBlockParameter B h α → ℝ := fun s => b s.1 s.2
  let L₀ := sigmaAxisOperator (fun d => (L d).toContinuousLinearMap)
  have hnorm : ‖L₀‖ ≤ 1 := sigmaAxisOperator_norm_le _ zero_le_one hL
  have hbx (s : JointBlockParameter B h α) : |(b₀ + L₀ x) s| ≤ 1 :=
    hbox s.1 (fun i => x ⟨s.1, i⟩) (fun i => hx ⟨s.1, i⟩) s.2
  have ht := affineSlice_c2_difference_bound V (jointBooleanSampler h c sets) hV
    ((jointBooleanSampler_contDiff h c sets).of_le (by first | exact WithTop.coe_le_coe.mpr le_top | norm_num)) b₀ L₀ hnorm x (herr _ hbx)
  have he : (fun y => jointBooleanSampler h c sets (b₀ + L₀ y)) =
      jointAffineBooleanSampler c sets L b := rfl
  rw [he] at ht
  exact ht

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff BigOperators NNReal

variable {B O α : Type*} [Fintype B] [Fintype O] [Fintype α]
  [DecidableEq B] [DecidableEq O] [DecidableEq α] {h : ℕ}

theorem affineBooleanCube_comparison
    (c : B → ℝ) (sets : O → Finset α) (block : O → B)
    (hblock : Function.Injective block) (v : Fin h) (sel : O → Option α)
    (hcard : ∀ o, (sets o).card ≤ h)
    (L : (BlockParameter B (Fin h) α → ℝ) ≃L[ℝ] (BlockParameter B (Fin h) α → ℝ))
    (b : BlockParameter B (Fin h) α → ℝ) (hL : ‖L.toContinuousLinearMap‖ ≤ 1)
    (hbox : ∀ x : BlockParameter B (Fin h) α → ℝ, (∀ z, |x z| ≤ 1) →
      ∀ z, |(b + L x) z| ≤ 1)
    {δ C κ ε : ℝ} (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hLinv : δ * ‖L.symm.toContinuousLinearMap‖ ≤ 1)
    (hC : 0 ≤ C) (hc : ∀ o, |c (block o)| ≤ C) (hκ : 0 < κ)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (r : B × Fin h → ℝ) (hr : ∀ i, 0 < r i)
    (K H S : ℝ≥0)
    (hK : δ⁻¹ * productMinorInverseBound (Fintype.card O) (Fintype.card α) h C 1 κ ≤ K)
    (hH : productMinorDerivativeBound (Fintype.card (BlockParameter B (Fin h) α))
      (Fintype.card O) (Fintype.card α) h C 1 + 1 ≤ H)
    (hS : (∑ i, ((2 * 2 ^ Fintype.card α : ℕ) : ℝ) * ((Fintype.card α : ℝ) + 1) ^ 2 * T / r i) +
      (Fintype.card (B × Fin h) : ℝ) * ((Fintype.card α : ℝ) + 1) *
        ((A : ℝ) / κ * productMinorDeterminantDerivativeBound
          (Fintype.card (BlockParameter B (Fin h) α)) (Fintype.card O) (Fintype.card α) h C 1) ≤ S)
    (V : (BlockParameter B (Fin h) α → ℝ) → (O → ℝ)) (hV : ContDiff ℝ 2 V)
    (hε : 0 < ε) (hεone : ε ≤ 1) (hsmall : (K : ℝ) * ε ≤ 1 / 2)
    (herr : ∀ x, (∀ z, |x z| ≤ 1) →
      ‖V x - booleanSamplerMap c sets (b + L x)‖ ≤ ε ∧
      ‖fderiv ℝ V x - fderiv ℝ (fun y => booleanSamplerMap c sets (b + L y)) x‖ ≤ ε ∧
      ‖fderiv ℝ (fderiv ℝ V) x -
        fderiv ℝ (fderiv ℝ (fun y => booleanSamplerMap c sets (b + L y))) x‖ ≤ ε)
    (φ : (O → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ y, ‖φ y‖ ≤ 1) :
    let η := scalarCubeBoundaryConstant α * ∑ i, r i +
      (blockCubeMeasure B (Fin h) α).real
        {x | |booleanMinorDeterminant c sets block v sel (b + L x)| < 2 * κ}
    let Q := 1 + 2 * (K : ℝ) * S +
      (Fintype.card (BlockParameter B (Fin h) α) : ℝ) * ((2 * (K : ℝ)) ^ 2 * H)
    |mappedTest (blockCubeMeasure B (Fin h) α) (fun x => booleanSamplerMap c sets (b + L x)) φ -
      mappedTest (blockCubeMeasure B (Fin h) α) V φ| ≤
      2 * η + 4 * (Fintype.card O : ℝ) * Real.sqrt (Q * ε) := by
  let U := booleanSamplerMap (F := Fin h) c sets
  let Us := fun x => U (b + L x)
  let J := booleanSelectedInjection block v sel
  let Js := affineSelectedInjection L J δ
  let w := affineBooleanCubeGoodWeight (fun _ : Unit => c) sets (fun _ => block) v
    (fun _ => sel) L.toContinuousLinearMap b ψ r (fun _ => κ)
  let χ := affineBooleanCubeCutoff (fun _ : Unit => c) sets (fun _ => block) v
    (fun _ => sel) L.toContinuousLinearMap b ψ r (fun _ => κ)
  let H₀ := productMinorDerivativeBound (Fintype.card (BlockParameter B (Fin h) α))
    (Fintype.card O) (Fintype.card α) h C 1
  have hH₀ : 0 ≤ H₀ := productMinorDerivativeBound_nonneg _ _ _ _ hC zero_le_one
  have hU : ContDiff ℝ 2 U := (booleanSamplerMap_contDiff c sets).of_le (by first | exact WithTop.coe_le_coe.mpr le_top | norm_num)
  have hUs : ContDiff ℝ 2 Us := hU.comp (contDiff_const.add L.contDiff)
  have hJs : ‖Js‖ ≤ 1 := affineSelectedInjection_norm_le L J hδ.le hLinv
    (booleanSelectedInjection_norm_le block hblock v sel)
  have hw := affineBooleanCubeGoodWeight_spec (fun _ : Unit => c) sets (fun _ => block) v
    (fun _ => sel) L.toContinuousLinearMap b ψ r (fun _ => κ) hψ hrange hzero hr (fun _ => hκ)
  have hb (x) (hx : x ∈ tsupport w) : ∀ z, |x z| ≤ 1 := (hw.2.2.2.2 x hx).1
  have hi (x) (hx : x ∈ tsupport w) :
      (selectedDerivative Us Js x).IsInvertible ∧ ‖(selectedDerivative Us Js x).inverse‖ ≤ K := by
    have hi₀ := boolean_selected_inverse_bound c sets block v sel hcard (b + L x)
      hC zero_le_one hc (hbox x (hb x hx)) hκ ((hw.2.2.2.2 x hx).2 ())
    have hi₁ := selectedDerivative_affine_inverse_bound U L b J hδ x
      (hU.differentiable (by norm_num) _) hi₀.1 hi₀.2
    exact ⟨hi₁.1, hi₁.2.trans hK⟩
  have hHU₀ (x) (hx : x ∈ tsupport w) : ‖fderiv ℝ (selectedDerivative Us Js) x‖ ≤ H₀ := by
    have hd := selectedDerivative_affine_derivative_bound U hU L b J hδ.le x
      (boolean_selected_derivative_bound c sets block v sel hcard (b + L x)
        hC le_rfl hc (hbox x (hb x hx)))
    exact hd.trans ((mul_le_mul
      (mul_le_of_le_one_left hH₀ hδone) hL (norm_nonneg _) hH₀).trans_eq (mul_one _))
  have hHU (x) (hx : x ∈ tsupport w) : ‖fderiv ℝ (selectedDerivative Us Js) x‖ ≤ H :=
    (hHU₀ x hx).trans ((le_add_of_nonneg_right zero_le_one).trans hH)
  have hHV (x) (hx : x ∈ tsupport w) : ‖fderiv ℝ (selectedDerivative V Js) x‖ ≤ H :=
    (selectedDerivative_bound_of_second_error Us V hUs hV Js hJs x (hHU₀ x hx)
      (herr x (hb x hx)).2.2).trans ((add_le_add le_rfl hεone).trans hH)
  have hder : (∑ z, ∫ x, |fderiv ℝ w x (Pi.single z 1)|) ≤ S := by
    have hd := affineBooleanCubeGoodWeight_derivative_budget (fun _ : Unit => c) sets (fun _ => block)
      v (fun _ => sel) hcard L.toContinuousLinearMap b hL
      (fun x hx => hbox _ (blockCubeFlatten_box hx)) (fun _ => C) (fun _ => hC) (fun _ => hc)
      ψ hψ hrange A T hLip hTransition r hr (fun _ => κ) (fun _ => hκ)
    simp only [Fintype.sum_unique] at hd
    exact hd.trans hS
  have hmass := affineBooleanCubeGoodWeight_mass_lower (fun _ : Unit => c) sets (fun _ => block) v
    (fun _ => sel) L.toContinuousLinearMap b ψ r (fun _ => κ) hψ hrange hone hr (fun _ => hκ)
  simp only [Fintype.sum_unique] at hmass
  apply selected_cutoff_comparison_of_close_derivatives (blockCubeMeasure B (Fin h) α) χ w
    (affineBooleanCubeCutoff_contDiff _ _ _ _ _ _ _ _ _ _ hψ).continuous.measurable
    (affineBooleanCubeCutoff_range _ _ _ _ _ _ _ _ _ _ hrange) hw.1 hw.2.1 hw.2.2.1
    (affineBooleanCubeGoodWeight_measure _ _ _ _ _ _ _ _ _ _ hψ hrange hzero hr (fun _ => hκ))
    Us V hUs hV Js hJs K H S (fun x hx => (hi x hx).1) (fun x hx => (hi x hx).2)
    (fun x hx => (mul_le_mul_of_nonneg_left (herr x (hb x hx)).2.1 K.coe_nonneg).trans hsmall)
    hHU hHV hder hε _ _ φ hφ hbound
  · simpa only [sub_add_eq_sub_sub, w, ContinuousLinearEquiv.coe_coe] using hmass
  · intro x hx
    rw [dist_comm, dist_eq_norm]
    exact (herr x (hb x (subset_tsupport w hx))).1

end Erdos3

end

end OAI
