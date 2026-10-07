import OAI.Combinatorics.Progressions.Lattices.JointAffineBooleanSource

namespace OAI

section

namespace Erdos3
open scoped BigOperators NNReal

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

noncomputable def jointAffineSourceBoundaryRadius (h : D → ℕ) (E : ℝ)
    (d : D) (_ : B d × Fin (h d)) : ℝ :=
  scalarCubeProductBoundaryRadius (B d × Fin (h d)) α
    ((E / (12 * ((Fintype.card D : ℝ) + 1))) / 2)

noncomputable def jointAffineSourceMinorThreshold (h : D → ℕ) (c₀ : D → ℝ) (δ E : ℝ)
    (d : D) : ℝ :=
  canonicalAffineCubeMinorThreshold (O d) α (h d) (c₀ d) δ
    (E / (12 * ((Fintype.card D : ℝ) + 1)))

noncomputable def jointAffineSourceRadius (h : D → ℕ) (c₀ C : D → ℝ)
    (A T : ℝ≥0) (δ E : ℝ) : ℝ :=
  let r := jointAffineSourceBoundaryRadius (B := B) (α := α) h E
  let κ := jointAffineSourceMinorThreshold (O := O) (α := α) h c₀ δ E
  let K := jointAffineBooleanInverseBudget (O := O) (α := α) h C κ δ
  let H := jointBooleanDerivativeBudget (B := B) (O := O) (α := α) h C
  let L := jointAffineBooleanTranslationBudget (O := O) (α := α) C A T r κ K H
  min 1 (E / (3 * (1 + (L : ℝ))))

noncomputable def jointAffineSourceTolerance (h : D → ℕ) (c₀ C : D → ℝ)
    (A T : ℝ≥0) (δ E : ℝ) : ℝ :=
  let r := jointAffineSourceBoundaryRadius (B := B) (α := α) h E
  let κ := jointAffineSourceMinorThreshold (O := O) (α := α) h c₀ δ E
  let K := jointAffineBooleanInverseBudget (O := O) (α := α) h C κ δ
  let Q := jointAffineBooleanErrorBudget (O := O) (α := α) h C κ A T r δ
  polynomialPerturbationScale K 1 Q (E / 3) (Fintype.card (Σ d, O d))

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators ContDiff NNReal

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]

theorem exists_uniform_joint_affine_source_tolerance_with_scales
    (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (δ : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1) {E : ℝ} (hE : 0 < E) :
    ∃ ρ : ℝ≥0, 0 < ρ ∧ ρ ≤ 1 ∧
    (ρ : ℝ) = jointAffineSourceRadius (B := B) (O := O) (α := α) h c₀ C A T δ E ∧
    ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
    t = jointAffineSourceTolerance (B := B) (O := O) (α := α) h c₀ C A T δ E ∧
    ∀ (c : ∀ d, B d → ℝ), (∀ d o, c₀ d ≤ |c d (block d o)|) →
    (∀ d o, |c d (block d o)| ≤ C d) →
    ∀ (center width : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ)
      (hw : ∀ d z, width d z ≠ 0),
    (∀ d z, δ ≤ |width d z|) → (∀ d z, |center d z| + |width d z| ≤ 1) →
    let L := fun d => (coordinateScaleEquiv (width d) (hw d)).toContinuousLinearEquiv
    let slice := fun x : JointBlockParameter B h α → ℝ =>
      (fun s => center s.1 s.2) + sigmaAxisOperator (fun d => (L d).toContinuousLinearMap) x
    let f := regularizedImageDensity (jointBooleanSource h) (jointAffineBooleanSampler c sets L center) ρ
    (∀ x, f x ∈ Set.Icc (0 : ℝ) (ρ⁻¹ ^ Fintype.card (Σ d, O d) : ℝ≥0)) ∧
    Integrable f ∧ (∫ x, f x) = 1 ∧ LipschitzWith (affineProductProfileLip (Σ d, O d) ρ) f ∧
    ∀ (V : (JointBlockParameter B h α → ℝ) → ((Σ d, O d) → ℝ)), ContDiff ℝ 2 V →
    (∀ x, (∀ z, |x z| ≤ 1) →
      ‖V x - jointBooleanSampler h c sets x‖ ≤ t ∧
      ‖fderiv ℝ V x - fderiv ℝ (jointBooleanSampler h c sets) x‖ ≤ t ∧
      ‖fderiv ℝ (fderiv ℝ V) x - fderiv ℝ (fderiv ℝ (jointBooleanSampler h c sets)) x‖ ≤ t) →
    ∀ φ : ((Σ d, O d) → ℝ) → ℝ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
      |(∫ y, f y * φ y) - mappedTest (jointBooleanSource h) (V ∘ slice) φ| ≤ E := by
  let η : D → ℝ := fun _ => E / (12 * ((Fintype.card D : ℝ) + 1))
  have hη : ∀ d, 0 < η d := fun _ => div_pos hE (by positivity)
  have hmass : 4 * (∑ d, η d) ≤ E / 3 := by
    have hn : (0 : ℝ) ≤ Fintype.card D := Nat.cast_nonneg _
    have hv : 0 ≤ E / (12 * ((Fintype.card D : ℝ) + 1)) := (div_pos hE (by positivity)).le
    have he : ((Fintype.card D : ℝ) + 1) * (E / (12 * ((Fintype.card D : ℝ) + 1))) = E / 12 := by
      field_simp
    have hm := mul_le_mul_of_nonneg_right (show (Fintype.card D : ℝ) ≤ (Fintype.card D : ℝ) + 1 by linarith) hv
    rw [he] at hm
    simp only [η, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    linarith
  let r := fun d (_ : B d × Fin (h d)) => scalarCubeProductBoundaryRadius (B d × Fin (h d)) α (η d / 2)
  let κ := fun d => canonicalAffineCubeMinorThreshold (O d) α (h d) (c₀ d) δ (η d)
  let K := jointAffineBooleanInverseBudget (O := O) (α := α) h C κ δ
  let H := jointBooleanDerivativeBudget (B := B) (O := O) (α := α) h C
  let Q := jointAffineBooleanErrorBudget (O := O) (α := α) h C κ A T r δ
  let L := jointAffineBooleanTranslationBudget (O := O) (α := α) C A T r κ K H
  have hr : ∀ d i, 0 ≤ r d i := fun d _ => (scalarCubeProductBoundaryRadius_pos _ _ (half_pos (hη d))).le
  have hκ : ∀ d, 0 ≤ κ d := fun d => (canonicalAffineCubeMinorThreshold_pos (O d) α (hh d) (hc₀ d) hδ (hη d)).le
  have hQ : 0 ≤ Q := by
    have hS := jointBooleanWeightBudget_nonneg (O := O) (α := α) h C hC A T r hr κ hκ
    dsimp only [Q, jointAffineBooleanErrorBudget]
    positivity
  let ρ : ℝ≥0 := ⟨min 1 (E / (3 * (1 + (L : ℝ)))), by positivity⟩
  have hρ : 0 < ρ := lt_min zero_lt_one (div_pos hE (by positivity))
  have hρone : ρ ≤ 1 := by
    change min (1 : ℝ) (E / (3 * (1 + (L : ℝ)))) ≤ 1
    exact min_le_left _ _
  have hnoise : (L : ℝ) * ρ ≤ E / 3 := by
    have hd : (ρ : ℝ) ≤ E / (3 * (1 + (L : ℝ))) := min_le_right _ _
    have he := (le_div_iff₀ (show 0 < 3 * (1 + (L : ℝ)) by positivity)).mp hd
    nlinarith [ρ.coe_nonneg]
  let t := polynomialPerturbationScale K 1 Q (E / 3) (Fintype.card (Σ d, O d))
  have ht := polynomialPerturbationScale_spec K.coe_nonneg (show (0 : ℝ) ≤ 1 by norm_num)
    hQ (show 0 < E / 3 by positivity) (Fintype.card (Σ d, O d))
  have hsmall : (K : ℝ) * t ≤ 1 / 2 := by simpa only [mul_one] using ht.2.2.1
  have hroot : 4 * (Fintype.card (Σ d, O d) : ℝ) * Real.sqrt (Q * t) ≤ E / 3 := by
    apply le_trans _ ht.2.2.2.2
    gcongr
    nlinarith [ht.1]
  refine ⟨ρ, hρ, hρone, rfl, t, ht.1, ht.2.1, rfl, ?_⟩
  intro c hclow hcup center width hw hwidth hbox
  have hs := jointAffineBoolean_source_density_comparison h hh c sets hsets hcard block hblock
    c₀ C hc₀ hC hclow hcup ψ hψ hrange hzero hone A T hLip hTransition δ hδ hδone η hη
    center width hw hwidth hbox ρ hρ
  refine ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, ?_⟩
  intro V hV herr φ hφ hbound
  have he := hs.2.2.2.2 V hV t ht.1 ht.2.1 hsmall herr φ hφ hbound
  exact he.trans (by change 4 * (∑ d, η d) + (L : ℝ) * ρ +
    4 * (Fintype.card (Σ d, O d) : ℝ) * Real.sqrt (Q * t) ≤ E; linarith only [hmass, hnoise, hroot])

theorem exists_uniform_joint_affine_source_tolerance
    (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (δ : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1) {E : ℝ} (hE : 0 < E) :
    ∃ ρ : ℝ≥0, 0 < ρ ∧ ρ ≤ 1 ∧ ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧
    ∀ (c : ∀ d, B d → ℝ), (∀ d o, c₀ d ≤ |c d (block d o)|) →
    (∀ d o, |c d (block d o)| ≤ C d) →
    ∀ (center width : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ)
      (hw : ∀ d z, width d z ≠ 0),
    (∀ d z, δ ≤ |width d z|) → (∀ d z, |center d z| + |width d z| ≤ 1) →
    let L := fun d => (coordinateScaleEquiv (width d) (hw d)).toContinuousLinearEquiv
    let slice := fun x : JointBlockParameter B h α → ℝ =>
      (fun s => center s.1 s.2) + sigmaAxisOperator (fun d => (L d).toContinuousLinearMap) x
    let f := regularizedImageDensity (jointBooleanSource h) (jointAffineBooleanSampler c sets L center) ρ
    (∀ x, f x ∈ Set.Icc (0 : ℝ) (ρ⁻¹ ^ Fintype.card (Σ d, O d) : ℝ≥0)) ∧
    Integrable f ∧ (∫ x, f x) = 1 ∧ LipschitzWith (affineProductProfileLip (Σ d, O d) ρ) f ∧
    ∀ (V : (JointBlockParameter B h α → ℝ) → ((Σ d, O d) → ℝ)), ContDiff ℝ 2 V →
    (∀ x, (∀ z, |x z| ≤ 1) →
      ‖V x - jointBooleanSampler h c sets x‖ ≤ t ∧
      ‖fderiv ℝ V x - fderiv ℝ (jointBooleanSampler h c sets) x‖ ≤ t ∧
      ‖fderiv ℝ (fderiv ℝ V) x - fderiv ℝ (fderiv ℝ (jointBooleanSampler h c sets)) x‖ ≤ t) →
    ∀ φ : ((Σ d, O d) → ℝ) → ℝ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
      |(∫ y, f y * φ y) - mappedTest (jointBooleanSource h) (V ∘ slice) φ| ≤ E := by
  obtain ⟨ρ, hρ, hρone, _, t, ht, htone, _, hs⟩ :=
    exists_uniform_joint_affine_source_tolerance_with_scales h hh sets hsets hcard block hblock
      c₀ C hc₀ hC ψ hψ hrange hzero hone A T hLip hTransition δ hδ hδone hE
  exact ⟨ρ, hρ, hρone, t, ht, htone, hs⟩

end Erdos3

end

end OAI
