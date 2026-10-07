/- Modified for ProveIt: prove finite regularity below infinity explicitly
for the older ContDiff order API. Mathematical statements unchanged. -/
import OAI.Combinatorics.Progressions.Estimates.DiagonalSliceBounds
import OAI.Combinatorics.Progressions.Lattices.AffineBooleanCubeComparison

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff BigOperators

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] {h : D → ℕ}
  (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α) (block : ∀ d, O d → B d)
  (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α)
  (L : ∀ d, (BlockParameter (B d) (Fin (h d)) α → ℝ) →L[ℝ]
    (BlockParameter (B d) (Fin (h d)) α → ℝ))
  (b : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ)
  (ψ : ℝ → ℝ) (r : ∀ d, B d × Fin (h d) → ℝ) (κ : D → ℝ)

noncomputable def jointAffineBooleanGoodWeight : (JointBlockParameter B h α → ℝ) → ℝ :=
  sigmaAxisWeight (fun d => affineBooleanCubeGoodWeight (fun _ : Unit => c d) (sets d)
    (fun _ => block d) (v d) (fun _ => sel d) (L d) (b d) ψ (r d) (fun _ => κ d))

noncomputable def jointAffineBooleanCutoff : (JointBlockParameter B h α → ℝ) → ℝ :=
  sigmaAxisWeight (fun d => affineBooleanCubeCutoff (fun _ : Unit => c d) (sets d)
    (fun _ => block d) (v d) (fun _ => sel d) (L d) (b d) ψ (r d) (fun _ => κ d))

theorem jointAffineBooleanCutoff_contDiff (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ 1 (jointAffineBooleanCutoff c sets block v sel L b ψ r κ) :=
  sigmaAxisWeight_contDiff _ (fun d =>
    (affineBooleanCubeCutoff_contDiff (fun _ : Unit => c d) (sets d)
      (fun _ => block d) (v d) (fun _ => sel d) (L d) (b d) ψ (r d) (fun _ => κ d) hψ).of_le
        (by norm_num))

theorem jointAffineBooleanCutoff_range (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (x : JointBlockParameter B h α → ℝ) :
    jointAffineBooleanCutoff c sets block v sel L b ψ r κ x ∈ Set.Icc (0 : ℝ) 1 :=
  product_cutoff_range _ (fun d => affineBooleanCubeCutoff_range (fun _ : Unit => c d) (sets d)
    (fun _ => block d) (v d) (fun _ => sel d) (L d) (b d) ψ (r d) (fun _ => κ d) hrange _)

theorem jointAffineBooleanGoodWeight_spec
    (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hr : ∀ d i, 0 < r d i) (hκ : ∀ d, 0 < κ d) :
    let w := jointAffineBooleanGoodWeight c sets block v sel L b ψ r κ
    ContDiff ℝ 1 w ∧ HasCompactSupport w ∧ (∀ x, 0 ≤ w x) ∧ (∫ x, |w x|) ≤ 1 ∧
      ∀ x ∈ tsupport w, (∀ s, |x s| ≤ 1) ∧ ∀ d, κ d ≤
        |booleanMinorDeterminant (c d) (sets d) (block d) (v d) (sel d)
          (b d + L d (fun i => x ⟨d, i⟩))| := by
  have hs (d) := affineBooleanCubeGoodWeight_spec (fun _ : Unit => c d) (sets d)
    (fun _ => block d) (v d) (fun _ => sel d) (L d) (b d) ψ (r d) (fun _ => κ d)
    hψ hrange hzero (hr d) (fun _ => hκ d)
  refine ⟨sigmaAxisWeight_contDiff _ (fun d => (hs d).1),
    sigmaAxisWeight_compact _ (fun d => (hs d).2.1),
    sigmaAxisWeight_nonneg _ (fun d => (hs d).2.2.1),
    sigmaAxisWeight_abs_mass_le_one _ (fun d => (hs d).2.2.2.1), ?_⟩
  intro x hx
  have hp (d) := (hs d).2.2.2.2 _ (sigmaAxisWeight_tsupport _ hx d)
  exact ⟨fun s => (hp s.1).1 s.2, fun d => (hp d).2 ()⟩

theorem jointAffineBooleanGoodWeight_measure
    (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hr : ∀ d i, 0 < r d i) (hκ : ∀ d, 0 < κ d) :
    realDensityMeasure volume (jointAffineBooleanGoodWeight c sets block v sel L b ψ r κ) =
      realDensityMeasure (jointBooleanSource h) (jointAffineBooleanCutoff c sets block v sel L b ψ r κ) := by
  let w := fun d => affineBooleanCubeGoodWeight (fun _ : Unit => c d) (sets d)
    (fun _ => block d) (v d) (fun _ => sel d) (L d) (b d) ψ (r d) (fun _ => κ d)
  let χ := fun d => affineBooleanCubeCutoff (fun _ : Unit => c d) (sets d)
    (fun _ => block d) (v d) (fun _ => sel d) (L d) (b d) ψ (r d) (fun _ => κ d)
  have hw (d) := affineBooleanCubeGoodWeight_spec (fun _ : Unit => c d) (sets d)
    (fun _ => block d) (v d) (fun _ => sel d) (L d) (b d) ψ (r d) (fun _ => κ d)
    hψ hrange hzero (hr d) (fun _ => hκ d)
  have hm (d) : Measurable (χ d) := (affineBooleanCubeCutoff_contDiff (fun _ : Unit => c d) (sets d)
    (fun _ => block d) (v d) (fun _ => sel d) (L d) (b d) ψ (r d) (fun _ => κ d) hψ).continuous.measurable
  have h01 (d) := affineBooleanCubeCutoff_range (fun _ : Unit => c d) (sets d)
    (fun _ => block d) (v d) (fun _ => sel d) (L d) (b d) ψ (r d) (fun _ => κ d) hrange
  change realDensityMeasure volume (sigmaAxisWeight w) =
    realDensityMeasure (sigmaAxisMeasure _) (sigmaAxisWeight χ)
  rw [← sigmaAxisMeasure_density w (fun d =>
    (hw d).1.continuous.integrable_of_hasCompactSupport (hw d).2.1) (fun d => (hw d).2.2.1)]
  have hlaw (d) : realDensityMeasure volume (w d) =
      realDensityMeasure (blockCubeMeasure (B d) (Fin (h d)) α) (χ d) :=
    affineBooleanCubeGoodWeight_measure (fun _ : Unit => c d) (sets d)
      (fun _ => block d) (v d) (fun _ => sel d) (L d) (b d) ψ (r d) (fun _ => κ d)
      hψ hrange hzero (hr d) (fun _ => hκ d)
  simp_rw [hlaw]
  exact sigmaAxisMeasure_withDensity _ χ (fun d => cutoff_integrable _ _ (hm d) (h01 d))
    (fun d x => (h01 d x).1)

theorem jointAffineBooleanGoodWeight_mass_lower
    (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (hr : ∀ d i, 0 < r d i) (hκ : ∀ d, 0 < κ d) :
    1 - ∑ d, (scalarCubeBoundaryConstant α * ∑ i, r d i +
      (blockCubeMeasure (B d) (Fin (h d)) α).real
        {a | |booleanMinorDeterminant (c d) (sets d) (block d) (v d) (sel d) (b d + L d a)| < 2 * κ d}) ≤
      ∫ x, jointAffineBooleanGoodWeight c sets block v sel L b ψ r κ x := by
  let w := fun d => affineBooleanCubeGoodWeight (fun _ : Unit => c d) (sets d)
    (fun _ => block d) (v d) (fun _ => sel d) (L d) (b d) ψ (r d) (fun _ => κ d)
  have hs (d) := affineBooleanCubeGoodWeight_spec (fun _ : Unit => c d) (sets d)
    (fun _ => block d) (v d) (fun _ => sel d) (L d) (b d) ψ (r d) (fun _ => κ d)
    hψ hrange hzero (hr d) (fun _ => hκ d)
  have hm (d) : (∫ y, w d y) ≤ 1 := by
    have he : (fun y => |w d y|) = w d := funext (fun y => abs_of_nonneg ((hs d).2.2.1 y))
    have hm := (hs d).2.2.2.1
    change (∫ y, |w d y|) ≤ 1 at hm
    rw [he] at hm
    exact hm
  apply sigmaAxisWeight_mass_loss w (fun d => (hs d).2.2.1) hm
  intro d
  have hd := affineBooleanCubeGoodWeight_mass_lower (fun _ : Unit => c d) (sets d)
    (fun _ => block d) (v d) (fun _ => sel d) (L d) (b d) ψ (r d) (fun _ => κ d)
    hψ hrange hone (hr d) (fun _ => hκ d)
  simpa only [Fintype.sum_unique, sub_add_eq_sub_sub] using hd

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff

variable {D α : Type*} [Fintype D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

theorem exists_joint_affine_boolean_good_mass
    (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (N : D → ℕ) (e : ∀ d, BlockParameter (O d) (Fin (h d)) α ≃ Fin (N d))
    (hN : ∀ d, 0 < N d) (degree : D → ℕ) (hdegree : ∀ d, 0 < degree d)
    (hdeg : ∀ d, Fintype.card (O d) * (h d - 1) ≤ degree d)
    (c₀ : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hc : ∀ d o, c₀ d ≤ |c d (block d o)|)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1) :
    ∃ sel : ∀ d, O d → Option α, ∀ (δ : ℝ) (η : D → ℝ), 0 < δ → (∀ d, 0 < η d) →
      ∀ (center width : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ)
        (hw : ∀ d z, width d z ≠ 0),
      (∀ d z, δ ≤ |restrictBlockParameters (block d) (width d) z|) →
      (∀ d z, |restrictBlockParameters (block d) (center d) z| +
        |restrictBlockParameters (block d) (width d) z| ≤ 1) →
      1 - ∑ d, η d ≤ ∫ x, jointAffineBooleanGoodWeight c sets block
        (fun d => (⟨0, hh d⟩ : Fin (h d))) sel
        (fun d => (coordinateScaleEquiv (width d) (hw d)).toContinuousLinearEquiv.toContinuousLinearMap)
        center ψ (fun d _ => scalarCubeProductBoundaryRadius (B d × Fin (h d)) α (η d / 2))
        (fun d => affineCubeMinorThreshold Unit (O d) α (h d) (N d) (degree d) (c₀ d) δ (η d)) x := by
  choose sel hs using fun d => exists_affine_cube_good_mass (fun _ : Unit => c d) (sets d) (hsets d)
    (h d) (hh d) (hcard d) (fun _ => block d) (fun _ => hblock d) (e d) (hN d)
    (degree d) (hdegree d) (hdeg d) (hc₀ d) (fun _ => hc d) ψ hψ hrange hone
  refine ⟨fun d => sel d (), ?_⟩
  intro δ η hδ hη center width hw hwidth hbox
  let κ := fun d => affineCubeMinorThreshold Unit (O d) α (h d) (N d) (degree d) (c₀ d) δ (η d)
  let r := fun d (_ : B d × Fin (h d)) => scalarCubeProductBoundaryRadius (B d × Fin (h d)) α (η d / 2)
  let w := fun d => affineBooleanCubeGoodWeight (fun _ : Unit => c d) (sets d) (fun _ => block d)
    (⟨0, hh d⟩ : Fin (h d)) (fun _ => sel d ())
    (coordinateScaleEquiv (width d) (hw d)).toContinuousLinearEquiv.toContinuousLinearMap
    (center d) ψ (r d) (fun _ => κ d)
  have hspec (d) := affineBooleanCubeGoodWeight_spec (fun _ : Unit => c d) (sets d) (fun _ => block d)
    (⟨0, hh d⟩ : Fin (h d)) (fun _ => sel d ())
    (coordinateScaleEquiv (width d) (hw d)).toContinuousLinearEquiv.toContinuousLinearMap
    (center d) ψ (r d) (fun _ => κ d) hψ hrange hzero
    (fun _ => scalarCubeProductBoundaryRadius_pos _ _ (half_pos (hη d)))
    (fun _ => affineCubeMinorThreshold_pos Unit (O d) α (h d) (hN d) (degree d) (hc₀ d) hδ (hη d))
  have hu (d) : (∫ y, w d y) ≤ 1 := by
    have he : (fun y => |w d y|) = w d := funext (fun y => abs_of_nonneg ((hspec d).2.2.1 y))
    have hu := (hspec d).2.2.2.1
    change (∫ y, |w d y|) ≤ 1 at hu
    rw [he] at hu
    exact hu
  apply sigmaAxisWeight_mass_loss w (fun d => (hspec d).2.2.1) hu η
  intro d
  have he : (fun _ : Unit => sel d ()) = sel d := funext (fun j => by cases j; rfl)
  change 1 - η d ≤ ∫ a, affineBooleanCubeGoodWeight _ _ _ _ (fun _ : Unit => sel d ()) _ _ _ _ _ a
  rw [he]
  exact hs d δ (η d) hδ (hη d) (center d) (width d) (hw d) (fun _ => hwidth d) (fun _ => hbox d)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)]

theorem jointAffineBooleanGoodWeight_derivative_budget {h : D → ℕ}
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α) (block : ∀ d, O d → B d)
    (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α)
    (hcard : ∀ d o, (sets d o).card ≤ h d)
    (L : ∀ d, (BlockParameter (B d) (Fin (h d)) α → ℝ) →L[ℝ]
      (BlockParameter (B d) (Fin (h d)) α → ℝ))
    (b : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ)
    (hL : ∀ d, ‖L d‖ ≤ 1)
    (hbox : ∀ d x, x ∈ scalarCubeProductDomain (B d × Fin (h d)) α →
      ∀ z, |(b d + L d (blockCubeFlatten (B d) (Fin (h d)) α x)) z| ≤ 1)
    (C : D → ℝ) (hC : ∀ d, 0 ≤ C d) (hc : ∀ d o, |c d (block d o)| ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (r : ∀ d, B d × Fin (h d) → ℝ) (hr : ∀ d i, 0 < r d i)
    (κ : D → ℝ) (hκ : ∀ d, 0 < κ d) :
    (∑ s : JointBlockParameter B h α, ∫ x,
      |fderiv ℝ (jointAffineBooleanGoodWeight c sets block v sel L b ψ r κ) x (Pi.single s 1)|) ≤
      jointBooleanWeightBudget (O := O) (α := α) h C A T r κ := by
  have hs (d) := affineBooleanCubeGoodWeight_spec (fun _ : Unit => c d) (sets d)
    (fun _ => block d) (v d) (fun _ => sel d) (L d) (b d) ψ (r d) (fun _ => κ d)
    hψ hrange hzero (hr d) (fun _ => hκ d)
  apply (sigmaAxisWeight_derivative_sum_le _ (fun d => (hs d).1)
    (fun d => (hs d).2.2.2.1)).trans
  unfold jointBooleanWeightBudget
  apply Finset.sum_le_sum
  intro d _
  have hb := affineBooleanCubeGoodWeight_derivative_budget (fun _ : Unit => c d) (sets d)
    (fun _ => block d) (v d) (fun _ => sel d) (hcard d) (L d) (b d) (hL d) (hbox d)
    (fun _ => C d) (fun _ => hC d) (fun _ => hc d) ψ hψ hrange A T hLip hTransition
    (r d) (hr d) (fun _ => κ d) (fun _ => hκ d)
  simpa only [Fintype.sum_unique, BlockParameter, Fintype.card_prod, Fintype.card_option,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_assoc] using hb

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff NNReal BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] {h : D → ℕ}

theorem jointAffineBoolean_good_weight_comparison
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α) (block : ∀ d, O d → B d)
    (hblock : ∀ d, Function.Injective (block d))
    (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α) (hcard : ∀ d o, (sets d o).card ≤ h d)
    (L : ∀ d, (BlockParameter (B d) (Fin (h d)) α → ℝ) ≃L[ℝ]
      (BlockParameter (B d) (Fin (h d)) α → ℝ))
    (b : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ)
    (δ : D → ℝ) (hδ : ∀ d, 0 < δ d) (hδone : ∀ d, δ d ≤ 1)
    (hL : ∀ d, ‖(L d).toContinuousLinearMap‖ ≤ 1)
    (hLinv : ∀ d, δ d * ‖(L d).symm.toContinuousLinearMap‖ ≤ 1)
    (hbox : ∀ d x, (∀ z, |x z| ≤ 1) → ∀ z, |(b d + L d x) z| ≤ 1)
    (C : D → ℝ) (hC : ∀ d, 0 ≤ C d) (hc : ∀ d o, |c d (block d o)| ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (r : ∀ d, B d × Fin (h d) → ℝ) (hr : ∀ d i, 0 < r d i)
    (κ : D → ℝ) (hκ : ∀ d, 0 < κ d) (K H₀ : ℝ≥0)
    (hK : ∀ d, (δ d)⁻¹ * productMinorInverseBound (Fintype.card (O d)) (Fintype.card α)
      (h d) (C d) 1 (κ d) ≤ K)
    (hH : ∀ d, productMinorDerivativeBound (Fintype.card (BlockParameter (B d) (Fin (h d)) α))
      (Fintype.card (O d)) (Fintype.card α) (h d) (C d) 1 ≤ H₀)
    (V : (JointBlockParameter B h α → ℝ) → ((Σ d, O d) → ℝ)) (hV : ContDiff ℝ 2 V)
    {ε η : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1) (hsmall : (K : ℝ) * ε ≤ 1 / 2)
    (hmass : 1 - η ≤ ∫ x, jointAffineBooleanGoodWeight c sets block v sel
      (fun d => (L d).toContinuousLinearMap) b ψ r κ x)
    (herr : ∀ x, (∀ z, |x z| ≤ 1) →
      ‖V x - jointAffineBooleanSampler c sets L b x‖ ≤ ε ∧
      ‖fderiv ℝ V x - fderiv ℝ (jointAffineBooleanSampler c sets L b) x‖ ≤ ε ∧
      ‖fderiv ℝ (fderiv ℝ V) x - fderiv ℝ (fderiv ℝ (jointAffineBooleanSampler c sets L b)) x‖ ≤ ε)
    (φ : ((Σ d, O d) → ℝ) → ℝ) (hφ : Measurable φ) (hbound : ∀ y, ‖φ y‖ ≤ 1) :
    let S := jointBooleanWeightBudget (O := O) (α := α) h C A T r κ
    let Q := 1 + 2 * (K : ℝ) * S +
      (Fintype.card (JointBlockParameter B h α) : ℝ) * ((2 * (K : ℝ)) ^ 2 * ((H₀ : ℝ) + 1))
    |mappedTest (jointBooleanSource h) (jointAffineBooleanSampler c sets L b) φ -
      mappedTest (jointBooleanSource h) V φ| ≤
      2 * η + 4 * (Fintype.card (Σ d, O d) : ℝ) * Real.sqrt (Q * ε) := by
  let w := jointAffineBooleanGoodWeight c sets block v sel (fun d => (L d).toContinuousLinearMap) b ψ r κ
  let χ := jointAffineBooleanCutoff c sets block v sel (fun d => (L d).toContinuousLinearMap) b ψ r κ
  let U := jointAffineBooleanSampler c sets L b
  let J := jointAffineBooleanInjection block v sel L δ
  let S : ℝ≥0 := ⟨jointBooleanWeightBudget (O := O) (α := α) h C A T r κ,
    jointBooleanWeightBudget_nonneg h C hC A T r (fun d i => (hr d i).le) κ (fun d => (hκ d).le)⟩
  have hU : ContDiff ℝ 2 U := (jointAffineBooleanSampler_contDiff c sets L b).of_le (by first | exact WithTop.coe_le_coe.mpr le_top | norm_num)
  have hJ : ‖J‖ ≤ 1 := jointAffineBooleanInjection_norm_le block v sel L δ hblock
    (fun d => (hδ d).le) hLinv
  have hw := jointAffineBooleanGoodWeight_spec c sets block v sel (fun d => (L d).toContinuousLinearMap)
    b ψ r κ hψ hrange hzero hr hκ
  have hb (x) (hx : x ∈ tsupport w) : ∀ z, |x z| ≤ 1 := (hw.2.2.2.2 x hx).1
  have hbx (x) (hx : x ∈ tsupport w) (d) (z) :
      |(b d + L d (fun i => x ⟨d, i⟩)) z| ≤ 1 := hbox d _ (fun i => hb x hx ⟨d, i⟩) z
  have hi (x) (hx : x ∈ tsupport w) := jointAffineBoolean_selected_inverse_bound c sets block v sel L b δ
    hcard x C κ hC hκ hδ hc (hbx x hx) ((hw.2.2.2.2 x hx).2) K.coe_nonneg hK
  have hHU₀ (x) (hx : x ∈ tsupport w) : ‖fderiv ℝ (selectedDerivative U J) x‖ ≤ H₀ :=
    jointAffineBoolean_selected_derivative_bound c sets block v sel L b δ hcard x C hC
      (fun d => (hδ d).le) hδone hL hc (hbx x hx) H₀.coe_nonneg hH
  have hHU (x) (hx : x ∈ tsupport w) : ‖fderiv ℝ (selectedDerivative U J) x‖ ≤ (H₀ + 1 : ℝ≥0) :=
    (hHU₀ x hx).trans (by simp only [NNReal.coe_add, NNReal.coe_one]; linarith)
  have hHV (x) (hx : x ∈ tsupport w) : ‖fderiv ℝ (selectedDerivative V J) x‖ ≤ (H₀ + 1 : ℝ≥0) :=
    (selectedDerivative_bound_of_second_error U V hU hV J hJ x (hHU₀ x hx)
      (herr x (hb x hx)).2.2).trans (by exact add_le_add le_rfl hεone)
  have ht := selected_cutoff_comparison_of_close_derivatives (jointBooleanSource h) χ w
    (jointAffineBooleanCutoff_contDiff _ _ _ _ _ _ _ _ _ _ hψ).continuous.measurable
    (jointAffineBooleanCutoff_range _ _ _ _ _ _ _ _ _ _ hrange) hw.1 hw.2.1 hw.2.2.1
    (jointAffineBooleanGoodWeight_measure _ _ _ _ _ _ _ _ _ _ hψ hrange hzero hr hκ)
    U V hU hV J hJ K (H₀ + 1) S (fun x hx => (hi x hx).1) (fun x hx => (hi x hx).2)
    (fun x hx => (mul_le_mul_of_nonneg_left (herr x (hb x hx)).2.1 K.coe_nonneg).trans hsmall)
    hHU hHV (jointAffineBooleanGoodWeight_derivative_budget c sets block v sel hcard
      (fun d => (L d).toContinuousLinearMap) b hL
      (fun d x hx => hbox d _ (blockCubeFlatten_box hx)) C hC hc ψ hψ hrange hzero A T hLip hTransition r hr κ hκ)
    hε hmass (fun x hx => by
      rw [dist_comm, dist_eq_norm]
      exact (herr x (hb x (subset_tsupport w hx))).1) φ hφ hbound
  have hScoe : (S : ℝ) = jointBooleanWeightBudget (O := O) (α := α) h C A T r κ := rfl
  simp only [NNReal.coe_add, NNReal.coe_one, hScoe] at ht
  exact ht

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped ContDiff NNReal BigOperators

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] {h : D → ℕ}

noncomputable def jointAffineBooleanTranslationBudget
    (C : D → ℝ) (A T : ℝ≥0) (r : ∀ d, B d × Fin (h d) → ℝ)
    (κ : D → ℝ) (K H : ℝ≥0) : ℝ≥0 :=
  (Fintype.card (Σ d, O d) : ℝ≥0) *
    (K * Real.toNNReal (jointBooleanWeightBudget (O := O) (α := α) h C A T r κ) +
      (Fintype.card (JointBlockParameter B h α) : ℝ≥0) * (K ^ 2 * H))

theorem jointAffineBoolean_translation_bound
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α) (block : ∀ d, O d → B d)
    (hblock : ∀ d, Function.Injective (block d))
    (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α) (hcard : ∀ d o, (sets d o).card ≤ h d)
    (L : ∀ d, (BlockParameter (B d) (Fin (h d)) α → ℝ) ≃L[ℝ]
      (BlockParameter (B d) (Fin (h d)) α → ℝ))
    (b : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ)
    (δ : D → ℝ) (hδ : ∀ d, 0 < δ d) (hδone : ∀ d, δ d ≤ 1)
    (hL : ∀ d, ‖(L d).toContinuousLinearMap‖ ≤ 1)
    (hLinv : ∀ d, δ d * ‖(L d).symm.toContinuousLinearMap‖ ≤ 1)
    (hbox : ∀ d x, (∀ z, |x z| ≤ 1) → ∀ z, |(b d + L d x) z| ≤ 1)
    (C : D → ℝ) (hC : ∀ d, 0 ≤ C d) (hc : ∀ d o, |c d (block d o)| ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (r : ∀ d, B d × Fin (h d) → ℝ) (hr : ∀ d i, 0 < r d i)
    (κ : D → ℝ) (hκ : ∀ d, 0 < κ d) (K H : ℝ≥0)
    (hK : ∀ d, (δ d)⁻¹ * productMinorInverseBound (Fintype.card (O d)) (Fintype.card α)
      (h d) (C d) 1 (κ d) ≤ K)
    (hH : ∀ d, productMinorDerivativeBound (Fintype.card (BlockParameter (B d) (Fin (h d)) α))
      (Fintype.card (O d)) (Fintype.card α) (h d) (C d) 1 ≤ H)
    : ImageTranslationBound
      (realDensityMeasure (jointBooleanSource h)
        (jointAffineBooleanCutoff c sets block v sel (fun d => (L d).toContinuousLinearMap) b ψ r κ))
      (jointAffineBooleanSampler c sets L b)
      (jointAffineBooleanTranslationBudget (O := O) (α := α) C A T r κ K H) := by
  let w := jointAffineBooleanGoodWeight c sets block v sel (fun d => (L d).toContinuousLinearMap) b ψ r κ
  let U := jointAffineBooleanSampler c sets L b
  let J := jointAffineBooleanInjection block v sel L δ
  let S : ℝ≥0 := ⟨jointBooleanWeightBudget (O := O) (α := α) h C A T r κ,
    jointBooleanWeightBudget_nonneg h C hC A T r (fun d i => (hr d i).le) κ (fun d => (hκ d).le)⟩
  have hU : ContDiff ℝ 2 U := (jointAffineBooleanSampler_contDiff c sets L b).of_le (by first | exact WithTop.coe_le_coe.mpr le_top | norm_num)
  have hJ : ‖J‖ ≤ 1 := jointAffineBooleanInjection_norm_le block v sel L δ hblock
    (fun d => (hδ d).le) hLinv
  have hw := jointAffineBooleanGoodWeight_spec c sets block v sel (fun d => (L d).toContinuousLinearMap)
    b ψ r κ hψ hrange hzero hr hκ
  have hb (x) (hx : x ∈ tsupport w) : ∀ z, |x z| ≤ 1 := (hw.2.2.2.2 x hx).1
  have hbx (x) (hx : x ∈ tsupport w) (d) (z) :
      |(b d + L d (fun i => x ⟨d, i⟩)) z| ≤ 1 := hbox d _ (fun i => hb x hx ⟨d, i⟩) z
  have hi (x) (hx : x ∈ tsupport w) := jointAffineBoolean_selected_inverse_bound c sets block v sel L b δ
    hcard x C κ hC hκ hδ hc (hbx x hx) ((hw.2.2.2.2 x hx).2) K.coe_nonneg hK
  have hHU₀ (x) (hx : x ∈ tsupport w) : ‖fderiv ℝ (selectedDerivative U J) x‖ ≤ H :=
    jointAffineBoolean_selected_derivative_bound c sets block v sel L b δ hcard x C hC
      (fun d => (hδ d).le) hδone hL hc (hbx x hx) H.coe_nonneg hH
  have hS := jointAffineBooleanGoodWeight_derivative_budget c sets block v sel hcard
    (fun d => (L d).toContinuousLinearMap) b hL
    (fun d x hx => hbox d _ (blockCubeFlatten_box hx)) C hC hc ψ hψ hrange hzero
    A T hLip hTransition r hr κ hκ
  let Q : ℝ≥0 := K * S + (Fintype.card (JointBlockParameter B h α) : ℝ≥0) * (K ^ 2 * H)
  have ht := imageTranslationBound_of_inverse_budget U hU J hJ w hw.1 hw.2.1 hw.2.2.1
    hw.2.2.2.1 K H S Q (fun x hx => (hi x hx).1) (fun x hx => (hi x hx).2)
    hHU₀ hS (by simp only [Q, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_pow]; exact le_rfl)
  have hSdef : S = Real.toNNReal (jointBooleanWeightBudget (O := O) (α := α) h C A T r κ) := by
    ext
    exact (Real.coe_toNNReal _ S.coe_nonneg).symm
  rw [jointAffineBooleanGoodWeight_measure c sets block v sel
    (fun d => (L d).toContinuousLinearMap) b ψ r κ hψ hrange hzero hr hκ] at ht
  simpa only [Q, hSdef, jointAffineBooleanTranslationBudget] using ht

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators ContDiff NNReal

noncomputable def canonicalAffineCubeMinorThreshold (O α : Type*) [Fintype O] [Fintype α]
    [DecidableEq α] (h : ℕ) (c₀ δ η : ℝ) : ℝ :=
  affineCubeMinorThreshold Unit O α h (cubeMinorVariableCount O α h) (cubeMinorDegree O h) c₀ δ η

theorem canonicalAffineCubeMinorThreshold_pos (O α : Type*) [Fintype O] [Nonempty O]
    [Fintype α] [DecidableEq α] {h : ℕ} (hh : 0 < h) {c₀ δ η : ℝ}
    (hc₀ : 0 < c₀) (hδ : 0 < δ) (hη : 0 < η) :
    0 < canonicalAffineCubeMinorThreshold O α h c₀ δ η :=
  affineCubeMinorThreshold_pos Unit O α h (boolean_minor_parameter_count_pos O α hh) _ hc₀ hδ hη

variable {D α : Type*} [Fintype D] [Fintype α] [decidableEqAlpha : DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]

noncomputable def jointAffineBooleanInverseBudget (h : D → ℕ) (C κ : D → ℝ) (δ : ℝ) : ℝ≥0 :=
  ∑ d, Real.toNNReal (δ⁻¹ * productMinorInverseBound (Fintype.card (O d)) (Fintype.card α)
    (h d) (C d) 1 (κ d))

omit decidableEqAlpha in
theorem jointAffineBooleanInverseBudget_le [DecidableEq α]
    (h : D → ℕ) (C κ : D → ℝ) (δ : ℝ) (d : D) :
    δ⁻¹ * productMinorInverseBound (Fintype.card (O d)) (Fintype.card α) (h d) (C d) 1 (κ d) ≤
      jointAffineBooleanInverseBudget (O := O) (α := α) h C κ δ := by
  classical
  apply (Real.le_coe_toNNReal _).trans
  exact_mod_cast Finset.single_le_sum (f := fun e => Real.toNNReal
    (δ⁻¹ * productMinorInverseBound (Fintype.card (O e)) (Fintype.card α) (h e) (C e) 1 (κ e)))
    (fun _ _ => zero_le) (Finset.mem_univ d)

noncomputable def jointAffineBooleanErrorBudget (h : D → ℕ) (C κ : D → ℝ) (A T : ℝ≥0)
    (r : ∀ d, B d × Fin (h d) → ℝ) (δ : ℝ) : ℝ :=
  let K := jointAffineBooleanInverseBudget (O := O) (α := α) h C κ δ
  let H := jointBooleanDerivativeBudget (B := B) (O := O) (α := α) h C
  1 + 2 * (K : ℝ) * jointBooleanWeightBudget (O := O) (α := α) h C A T r κ +
    (Fintype.card (JointBlockParameter B h α) : ℝ) * ((2 * (K : ℝ)) ^ 2 * ((H : ℝ) + 1))

theorem exists_canonical_joint_affine_good_mass
    [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]
    (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hc : ∀ d o, c₀ d ≤ |c d (block d o)|)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1) :
    ∃ sel : ∀ d, O d → Option α, ∀ (δ : ℝ) (η : D → ℝ), 0 < δ → (∀ d, 0 < η d) →
      ∀ (center width : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ)
        (hw : ∀ d z, width d z ≠ 0),
      (∀ d z, δ ≤ |width d z|) → (∀ d z, |center d z| + |width d z| ≤ 1) →
      1 - ∑ d, η d ≤ ∫ x, jointAffineBooleanGoodWeight c sets block
        (fun d => (⟨0, hh d⟩ : Fin (h d))) sel
        (fun d => (coordinateScaleEquiv (width d) (hw d)).toContinuousLinearEquiv.toContinuousLinearMap)
        center ψ (fun d _ => scalarCubeProductBoundaryRadius (B d × Fin (h d)) α (η d / 2))
        (fun d => canonicalAffineCubeMinorThreshold (O d) α (h d) (c₀ d) δ (η d)) x := by
  obtain ⟨sel, hs⟩ := exists_joint_affine_boolean_good_mass h hh c sets hsets hcard block hblock
    (fun d => cubeMinorVariableCount (O d) α (h d)) (fun d => booleanBlockParameterEquiv (O d) α (h d))
    (fun d => boolean_minor_parameter_count_pos (O d) α (hh d))
    (fun d => cubeMinorDegree (O d) (h d)) (fun _ => lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))
    (fun _ => le_max_right _ _) c₀ hc₀ hc ψ hψ hrange hzero hone
  refine ⟨sel, ?_⟩
  intro δ η hδ hη center width hw hwidth hbox
  exact hs δ η hδ hη center width hw
    (fun d z => hwidth d ((block d z.1, z.2.1, z.2.2)))
    (fun d z => hbox d ((block d z.1, z.2.1, z.2.2)))

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped ContDiff NNReal BigOperators

theorem jointAffineBooleanCutoff_loss {D α : Type*}
    [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
    {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    [∀ d, Fintype (O d)] [∀ d, DecidableEq (O d)] {h : D → ℕ}
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α) (block : ∀ d, O d → B d)
    (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α)
    (L : ∀ d, (BlockParameter (B d) (Fin (h d)) α → ℝ) →L[ℝ]
      (BlockParameter (B d) (Fin (h d)) α → ℝ))
    (b : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0)
    (r : ∀ d, B d × Fin (h d) → ℝ) (hr : ∀ d i, 0 < r d i)
    (κ : D → ℝ) (hκ : ∀ d, 0 < κ d) {η : ℝ}
    (hmass : 1-η ≤ ∫ x, jointAffineBooleanGoodWeight c sets block v sel L b ψ r κ x) :
    (∫ x, 1-jointAffineBooleanCutoff c sets block v sel L b ψ r κ x ∂jointBooleanSource h) ≤ η := by
  let : IsProbabilityMeasure (jointBooleanSource (B := B) (α := α) h) := jointBooleanSource_probability h
  have hs := jointAffineBooleanGoodWeight_spec c sets block v sel L b ψ r κ hψ hrange hzero hr hκ
  have hwi : Integrable (jointAffineBooleanGoodWeight c sets block v sel L b ψ r κ) :=
    hs.1.continuous.integrable_of_hasCompactSupport hs.2.1
  have hw0 : ∀ x, 0 ≤ jointAffineBooleanGoodWeight c sets block v sel L b ψ r κ x := hs.2.2.1
  have hχ : Measurable (jointAffineBooleanCutoff c sets block v sel L b ψ r κ) :=
    (jointAffineBooleanCutoff_contDiff c sets block v sel L b ψ r κ hψ).continuous.measurable
  have hχ01 : ∀ x, jointAffineBooleanCutoff c sets block v sel L b ψ r κ x ∈ Set.Icc (0 : ℝ) 1 :=
    jointAffineBooleanCutoff_range c sets block v sel L b ψ r κ hrange
  have hlaw : realDensityMeasure volume (jointAffineBooleanGoodWeight c sets block v sel L b ψ r κ) =
      realDensityMeasure (jointBooleanSource (B := B) (α := α) h) (jointAffineBooleanCutoff c sets block v sel L b ψ r κ) :=
    jointAffineBooleanGoodWeight_measure c sets block v sel L b ψ r κ hψ hrange hzero hr hκ
  exact cutoff_loss_of_density_mass (X := JointBlockParameter B h α → ℝ)
    (jointBooleanSource (B := B) (α := α) h) volume
    (jointAffineBooleanCutoff c sets block v sel L b ψ r κ) (jointAffineBooleanGoodWeight c sets block v sel L b ψ r κ)
    hχ hχ01 hwi hw0 hlaw hmass

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] {h : D → ℕ}

theorem jointAffineBoolean_regularization_error
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α) (block : ∀ d, O d → B d)
    (hblock : ∀ d, Function.Injective (block d))
    (v : ∀ d, Fin (h d)) (sel : ∀ d, O d → Option α) (hcard : ∀ d o, (sets d o).card ≤ h d)
    (L : ∀ d, (BlockParameter (B d) (Fin (h d)) α → ℝ) ≃L[ℝ]
      (BlockParameter (B d) (Fin (h d)) α → ℝ))
    (b : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ)
    (δ : D → ℝ) (hδ : ∀ d, 0 < δ d) (hδone : ∀ d, δ d ≤ 1)
    (hL : ∀ d, ‖(L d).toContinuousLinearMap‖ ≤ 1)
    (hLinv : ∀ d, δ d * ‖(L d).symm.toContinuousLinearMap‖ ≤ 1)
    (hbox : ∀ d x, (∀ z, |x z| ≤ 1) → ∀ z, |(b d + L d x) z| ≤ 1)
    (C : D → ℝ) (hC : ∀ d, 0 ≤ C d) (hc : ∀ d o, |c d (block d o)| ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (r : ∀ d, B d × Fin (h d) → ℝ) (hr : ∀ d i, 0 < r d i)
    (κ : D → ℝ) (hκ : ∀ d, 0 < κ d) (K H : ℝ≥0)
    (hK : ∀ d, (δ d)⁻¹ * productMinorInverseBound (Fintype.card (O d)) (Fintype.card α)
      (h d) (C d) 1 (κ d) ≤ K)
    (hH : ∀ d, productMinorDerivativeBound (Fintype.card (BlockParameter (B d) (Fin (h d)) α))
      (Fintype.card (O d)) (Fintype.card α) (h d) (C d) 1 ≤ H)
    {η : ℝ}
    (hmass : 1 - η ≤ ∫ x, jointAffineBooleanGoodWeight c sets block v sel
      (fun d => (L d).toContinuousLinearMap) b ψ r κ x)
    (ρ : ℝ≥0) (hρ : 0 < ρ) (φ : ((Σ d, O d) → ℝ) → ℝ)
    (hφ : Measurable φ) (hbound : ∀ x, ‖φ x‖ ≤ 1) :
    |(∫ x, regularizedImageDensity (jointBooleanSource h)
        (jointAffineBooleanSampler c sets L b) ρ x * φ x) -
      mappedTest (jointBooleanSource h) (jointAffineBooleanSampler c sets L b) φ| ≤
      2 * η + jointAffineBooleanTranslationBudget (O := O) (α := α) C A T r κ K H * ρ := by
  have htrans := jointAffineBoolean_translation_bound c sets block hblock v sel hcard L b δ
    hδ hδone hL hLinv hbox C hC hc ψ hψ hrange hzero A T hLip hTransition r hr κ hκ K H hK hH
  have hcut := jointAffineBooleanCutoff_loss c sets block v sel (fun d => (L d).toContinuousLinearMap)
    b ψ hψ hrange hzero r hr κ hκ hmass
  exact regularizedImageDensity_cutoff_error (jointBooleanSource h)
    (jointAffineBooleanCutoff c sets block v sel (fun d => (L d).toContinuousLinearMap) b ψ r κ)
    (jointAffineBooleanCutoff_contDiff _ _ _ _ _ _ _ _ _ _ hψ).continuous.measurable
    (jointAffineBooleanCutoff_range _ _ _ _ _ _ _ _ _ _ hrange)
    (jointAffineBooleanSampler c sets L b) (jointAffineBooleanSampler_contDiff c sets L b).continuous.measurable
    (jointAffineBooleanTranslationBudget (O := O) (α := α) C A T r κ K H) htrans hcut ρ hρ φ hφ hbound

end Erdos3

end

section

namespace Erdos3

 theorem affineCubeMinorThreshold_log_inv_relative (J O α : Type*) [Fintype J] [Fintype O]
    [Fintype α] [DecidableEq α] (h : ℕ) {N : ℕ} (hN : 0 < N) (d : ℕ)
    {c₀ δ η : ℝ} (hc₀ : 0 < c₀) (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η) :
    Real.log (affineCubeMinorThreshold J O α h N d c₀ δ η)⁻¹ ≤
      Real.log (affineCubeMinorThreshold J O α h N d c₀ 1 η)⁻¹ +
        (N * d : ℕ) * (N : ℝ) * Real.log δ⁻¹ := by
  have he := affineCubeMinorThreshold_log_inv_slice_bound J O α h hN d hc₀ hδ hδone hη
  have hb := affineCubeMinorThreshold_log_inv J O α h hN d hc₀ zero_lt_one hη
  simp only [inv_one, one_pow, mul_one] at hb
  rw [hb]
  calc
    _ ≤ _ := he
    _ = _ := by ring

 theorem canonicalAffineCubeMinorThreshold_log_inv_relative (O α : Type*) [Fintype O]
    [Nonempty O] [Fintype α] [DecidableEq α] {h : ℕ} (hh : 0 < h)
    {c₀ δ η : ℝ} (hc₀ : 0 < c₀) (hδ : 0 < δ) (hδone : δ ≤ 1) (hη : 0 < η) :
    Real.log (canonicalAffineCubeMinorThreshold O α h c₀ δ η)⁻¹ ≤
      Real.log (canonicalAffineCubeMinorThreshold O α h c₀ 1 η)⁻¹ +
        (cubeMinorVariableCount O α h * cubeMinorDegree O h : ℕ) *
          (cubeMinorVariableCount O α h : ℝ) * Real.log δ⁻¹ :=
  affineCubeMinorThreshold_log_inv_relative Unit O α h
    (boolean_minor_parameter_count_pos O α hh) (cubeMinorDegree O h) hc₀ hδ hδone hη

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped BigOperators ContDiff NNReal

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
  {B O : D → Type*} [∀ d, Fintype (B d)] [∀ d, Fintype (O d)]
  [∀ d, DecidableEq (B d)] [∀ d, DecidableEq (O d)] [∀ d, Nonempty (O d)]

theorem jointAffineBoolean_source_density_comparison
    (h : D → ℕ) (hh : ∀ d, 0 < h d)
    (c : ∀ d, B d → ℝ) (sets : ∀ d, O d → Finset α) (hsets : ∀ d, Function.Injective (sets d))
    (hcard : ∀ d o, (sets d o).card ≤ h d)
    (block : ∀ d, O d → B d) (hblock : ∀ d, Function.Injective (block d))
    (c₀ C : D → ℝ) (hc₀ : ∀ d, 0 < c₀ d) (hC : ∀ d, 0 ≤ C d)
    (hclow : ∀ d o, c₀ d ≤ |c d (block d o)|) (hcup : ∀ d o, |c d (block d o)| ≤ C d)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hrange : ∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hzero : ∀ t, |t| ≤ 1 → ψ t = 0) (hone : ∀ t, 2 ≤ |t| → ψ t = 1)
    (A T : ℝ≥0) (hLip : LipschitzWith A ψ) (hTransition : LipschitzWith T Real.smoothTransition)
    (δ : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1) (η : D → ℝ) (hη : ∀ d, 0 < η d)
    (center width : ∀ d, BlockParameter (B d) (Fin (h d)) α → ℝ)
    (hw : ∀ d z, width d z ≠ 0) (hwidth : ∀ d z, δ ≤ |width d z|)
    (hbox : ∀ d z, |center d z| + |width d z| ≤ 1)
    (ρ : ℝ≥0) (hρ : 0 < ρ) :
    let L := fun d => (coordinateScaleEquiv (width d) (hw d)).toContinuousLinearEquiv
    let slice := fun x : JointBlockParameter B h α → ℝ =>
      (fun s => center s.1 s.2) + sigmaAxisOperator (fun d => (L d).toContinuousLinearMap) x
    let U := jointAffineBooleanSampler c sets L center
    let f := regularizedImageDensity (jointBooleanSource h) U ρ
    let r := fun d (_ : B d × Fin (h d)) => scalarCubeProductBoundaryRadius (B d × Fin (h d)) α (η d / 2)
    let κ := fun d => canonicalAffineCubeMinorThreshold (O d) α (h d) (c₀ d) δ (η d)
    let K := jointAffineBooleanInverseBudget (O := O) (α := α) h C κ δ
    let H := jointBooleanDerivativeBudget (B := B) (O := O) (α := α) h C
    (∀ x, f x ∈ Set.Icc (0 : ℝ) (ρ⁻¹ ^ Fintype.card (Σ d, O d) : ℝ≥0)) ∧
    Integrable f ∧ (∫ x, f x) = 1 ∧ LipschitzWith (affineProductProfileLip (Σ d, O d) ρ) f ∧
    ∀ (V : (JointBlockParameter B h α → ℝ) → ((Σ d, O d) → ℝ)), ContDiff ℝ 2 V →
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 → (K : ℝ) * ε ≤ 1 / 2 →
    (∀ x, (∀ z, |x z| ≤ 1) →
      ‖V x - jointBooleanSampler h c sets x‖ ≤ ε ∧
      ‖fderiv ℝ V x - fderiv ℝ (jointBooleanSampler h c sets) x‖ ≤ ε ∧
      ‖fderiv ℝ (fderiv ℝ V) x - fderiv ℝ (fderiv ℝ (jointBooleanSampler h c sets)) x‖ ≤ ε) →
    ∀ φ : ((Σ d, O d) → ℝ) → ℝ, Measurable φ → (∀ y, ‖φ y‖ ≤ 1) →
      |(∫ y, f y * φ y) - mappedTest (jointBooleanSource h) (V ∘ slice) φ| ≤
        4 * (∑ d, η d) + jointAffineBooleanTranslationBudget (O := O) (α := α) C A T r κ K H * ρ +
          4 * (Fintype.card (Σ d, O d) : ℝ) *
            Real.sqrt (jointAffineBooleanErrorBudget (O := O) (α := α) h C κ A T r δ * ε) := by
  intro L slice U f r κ K H
  let : IsProbabilityMeasure (jointBooleanSource (B := B) (α := α) h) := jointBooleanSource_probability h
  have hUm : Measurable U := (jointAffineBooleanSampler_contDiff c sets L center).continuous.measurable
  have hp := regularizedImageDensity_probability (jointBooleanSource h) U hUm ρ hρ
  have hb := regularizedImageDensity_bounds (jointBooleanSource h) U hUm ρ hρ
  refine ⟨hb.1, hp.2.1, hp.2.2, hb.2, ?_⟩
  intro V hV ε hε hεone hsmall herr φ hφ hbound
  obtain ⟨sel, hs⟩ := exists_canonical_joint_affine_good_mass h hh c sets hsets hcard block hblock
    c₀ hc₀ hclow ψ hψ hrange hzero hone
  have hmass := hs δ η hδ hη center width hw hwidth hbox
  have hr (d) (i : B d × Fin (h d)) : 0 < r d i :=
    scalarCubeProductBoundaryRadius_pos _ _ (half_pos (hη d))
  have hκ (d) : 0 < κ d := canonicalAffineCubeMinorThreshold_pos (O d) α (hh d) (hc₀ d) hδ (hη d)
  have hL (d) : ‖(L d).toContinuousLinearMap‖ ≤ 1 :=
    coordinateScaleEquiv_norm_le (width d) (hw d) zero_le_one
      (fun z => (le_add_of_nonneg_left (abs_nonneg (center d z))).trans (hbox d z))
  have hLinv (d) : δ * ‖(L d).symm.toContinuousLinearMap‖ ≤ 1 :=
    coordinateScaleEquiv_scaled_inverse_norm_le (width d) (hw d) hδ (hwidth d)
  have hbx (d) (x : BlockParameter (B d) (Fin (h d)) α → ℝ) (hx : ∀ z, |x z| ≤ 1) :
      ∀ z, |(center d + L d x) z| ≤ 1 := coordinateScaleEquiv_affine_box _ _ _ (hbox d) x hx
  have hK := jointAffineBooleanInverseBudget_le (O := O) (α := α) h C κ δ
  have hH := jointBooleanDerivativeBudget_le (B := B) (O := O) (α := α) h C
  have hreg := jointAffineBoolean_regularization_error c sets block hblock
    (fun d => ⟨0, hh d⟩) sel hcard L center (fun _ => δ) (fun _ => hδ) (fun _ => hδone)
    hL hLinv hbx C hC hcup ψ hψ hrange hzero A T hLip hTransition r hr κ hκ K H hK hH
    hmass ρ hρ φ hφ hbound
  have hsmooth : ContDiff ℝ 2 (V ∘ slice) := hV.comp
    (contDiff_const.add (sigmaAxisOperator (fun d => (L d).toContinuousLinearMap)).contDiff)
  have he := jointAffineBoolean_c2_error_transport c sets L center hL hbx V hV herr
  have hcomp := jointAffineBoolean_good_weight_comparison c sets block hblock
    (fun d => ⟨0, hh d⟩) sel hcard L center (fun _ => δ) (fun _ => hδ) (fun _ => hδone)
    hL hLinv hbx C hC hcup ψ hψ hrange hzero A T hLip hTransition r hr κ hκ K H hK hH
    (V ∘ slice) hsmooth hε hεone hsmall hmass he φ hφ hbound
  calc
    _ ≤ |(∫ y, f y * φ y) - mappedTest (jointBooleanSource h) U φ| +
        |mappedTest (jointBooleanSource h) U φ - mappedTest (jointBooleanSource h) (V ∘ slice) φ| :=
      abs_sub_le _ _ _
    _ ≤ _ := by
      have ht := add_le_add hreg hcomp
      dsimp only [jointAffineBooleanErrorBudget]
      linarith only [ht]

end Erdos3

end

end OAI
