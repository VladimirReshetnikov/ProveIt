import Mathlib.Tactic
import OAI.Combinatorics.Progressions.Dynamics.LayerRemovalBudgets

namespace OAI

section

namespace Erdos3

noncomputable def modeRemovalTranslationConstant (d : ℕ) : ℝ :=
  4 * (3 : ℝ) ^ d * ((d : ℝ) * probabilityProfileLipschitz)

noncomputable def modeRemovalMeshConstant (d : ℕ) : ℝ :=
  (4 : ℝ) ^ d * ((d : ℝ) * probabilityProfileLipschitz)

theorem modeRemovalTranslationConstant_nonneg (d : ℕ) : 0 ≤ modeRemovalTranslationConstant d := by
  unfold modeRemovalTranslationConstant
  positivity

theorem modeRemovalMeshConstant_nonneg (d : ℕ) : 0 ≤ modeRemovalMeshConstant d := by
  unfold modeRemovalMeshConstant
  positivity

noncomputable def modeRemovalBeta (ε : ℝ) : ℝ := min (1 / 2) (ε / 2)

theorem modeRemovalBeta_pos {ε : ℝ} (hε : 0 < ε) : 0 < modeRemovalBeta ε := by
  exact lt_min (by norm_num) (by positivity)

theorem modeRemovalBeta_le_one (ε : ℝ) : modeRemovalBeta ε ≤ 1 :=
  (min_le_left _ _).trans (by norm_num)

noncomputable def modeRemovalRadius (d : ℕ) (ε : ℝ) : ℝ :=
  ε / (2 * (modeRemovalTranslationConstant d + 1))

theorem modeRemovalRadius_pos (d : ℕ) {ε : ℝ} (hε : 0 < ε) : 0 < modeRemovalRadius d ε := by
  have hc := modeRemovalTranslationConstant_nonneg d
  unfold modeRemovalRadius
  positivity

theorem modeRemovalError_bound (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    modeRemovalTranslationConstant d * modeRemovalRadius d ε + modeRemovalBeta ε ≤ ε := by
  have hc := modeRemovalTranslationConstant_nonneg d
  have hr := (modeRemovalRadius_pos d hε).le
  have hd : modeRemovalTranslationConstant d + 1 ≠ 0 := by positivity
  have he : (modeRemovalTranslationConstant d + 1) * modeRemovalRadius d ε = ε / 2 := by
    unfold modeRemovalRadius
    field_simp
  have hb : modeRemovalBeta ε ≤ ε / 2 := min_le_right _ _
  nlinarith

noncomputable def modeRemovalBias (m : ℕ) (ε : ℝ) : ℝ := modeRemovalBeta ε ^ (2 ^ m)

theorem modeRemovalBias_pos (m : ℕ) {ε : ℝ} (hε : 0 < ε) : 0 < modeRemovalBias m ε :=
  pow_pos (modeRemovalBeta_pos hε) _

theorem modeRemovalBias_le {m : ℕ} (i : Fin m) {ε : ℝ} (hε : 0 < ε) :
    modeRemovalBias m ε ≤ modeRemovalBeta ε ^ (2 ^ (i.val + 1)) := by
  apply pow_le_pow_of_le_one (modeRemovalBeta_pos hε).le (modeRemovalBeta_le_one ε)
  exact pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) (Nat.succ_le_of_lt i.isLt)

noncomputable def modeRemovalMesh (d : ℕ) : ℝ := 1 / (2 * (modeRemovalMeshConstant d + 1))

theorem modeRemovalMesh_pos (d : ℕ) : 0 < modeRemovalMesh d := by
  have hc := modeRemovalMeshConstant_nonneg d
  unfold modeRemovalMesh
  positivity

theorem modeRemovalMesh_le_one (d : ℕ) : modeRemovalMesh d ≤ 1 := by
  have hc := modeRemovalMeshConstant_nonneg d
  apply (div_le_iff₀ (by positivity : 0 < 2 * (modeRemovalMeshConstant d + 1))).mpr
  linarith

theorem modeRemovalMesh_small (d : ℕ) :
    modeRemovalMeshConstant d * modeRemovalMesh d ≤ 1 / 2 := by
  have hc := modeRemovalMeshConstant_nonneg d
  have hd : modeRemovalMeshConstant d + 1 ≠ 0 := by positivity
  have he : (modeRemovalMeshConstant d + 1) * modeRemovalMesh d = 1 / 2 := by
    unfold modeRemovalMesh
    field_simp
  nlinarith [modeRemovalMesh_pos d]

theorem modeRemovalMesh_of_width (d : ℕ) {V : ℝ} (hV : 0 < V)
    (hwidth : 1 / modeRemovalMesh d ≤ V) : 1 ≤ V ∧ 1 / V ≤ modeRemovalMesh d := by
  have hm := (div_le_iff₀ (modeRemovalMesh_pos d)).mp hwidth
  have hmul := mul_le_mul_of_nonneg_left (modeRemovalMesh_le_one d) hV.le
  constructor
  · nlinarith
  · apply (div_le_iff₀ hV).mpr
    nlinarith

end Erdos3

end

section

namespace Erdos3

noncomputable def modeRemovalShrink (m d : ℕ) (D ρ ε : ℝ) : ℝ :=
  1 + (m : ℝ) * D / (modeRemovalRadius d ε * ρ)

theorem modeRemovalShrink_one_le (m d : ℕ) {D ρ ε : ℝ}
    (hD : 0 ≤ D) (hρ : 0 < ρ) (hε : 0 < ε) : 1 ≤ modeRemovalShrink m d D ρ ε := by
  have hr := modeRemovalRadius_pos d hε
  unfold modeRemovalShrink
  exact le_add_of_nonneg_right (by positivity)

theorem modeRemovalShrink_move (m d : ℕ) {D ρ ε : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) :
    (m : ℝ) * D ≤ modeRemovalRadius d ε * ρ * modeRemovalShrink m d D ρ ε := by
  have hr := modeRemovalRadius_pos d hε
  have hd : modeRemovalRadius d ε * ρ ≠ 0 := ne_of_gt (mul_pos hr hρ)
  unfold modeRemovalShrink
  rw [mul_add, mul_one, mul_div_cancel₀ _ hd]
  linarith [mul_pos hr hρ]

noncomputable def modeRemovalSideThreshold (m d : ℕ) (D S ρ ε : ℝ) : ℝ :=
  S * modeRemovalShrink m d D ρ ε * (finiteLayerBiasBudget m (modeRemovalBias m ε) + 1) +
    1 / (ρ * modeRemovalMesh d) + 1

noncomputable def modeRemovalRankThreshold (m n d : ℕ) (C D S ρ ε : ℝ) : ℝ :=
  layerRemovalRankBudget m n C D (finiteLayerBiasBudget m (modeRemovalBias m ε))
    (2 * modeRemovalShrink m d D ρ ε) S

theorem modeRemovalSideThreshold_bounds (m d : ℕ) {D S ρ ε : ℝ}
    (hD : 0 ≤ D) (hS : 0 ≤ S) (hρ : 0 < ρ) (hε : 0 < ε) :
    0 < modeRemovalSideThreshold m d D S ρ ε ∧
    S * modeRemovalShrink m d D ρ ε * (finiteLayerBiasBudget m (modeRemovalBias m ε) + 1) ≤
      modeRemovalSideThreshold m d D S ρ ε ∧
    1 / modeRemovalMesh d ≤ ρ * modeRemovalSideThreshold m d D S ρ ε := by
  have hT := modeRemovalShrink_one_le m d hD hρ hε
  have hB := finiteLayerBiasBudget_one_le m (modeRemovalBias_pos m hε)
  have hδ := modeRemovalMesh_pos d
  have ha : 0 ≤ S * modeRemovalShrink m d D ρ ε *
      (finiteLayerBiasBudget m (modeRemovalBias m ε) + 1) := by positivity
  have hb : 0 < 1 / (ρ * modeRemovalMesh d) := by positivity
  have he : ρ * (1 / (ρ * modeRemovalMesh d)) = 1 / modeRemovalMesh d := by
    field_simp
  unfold modeRemovalSideThreshold
  refine ⟨by positivity, by linarith, ?_⟩
  nlinarith [mul_nonneg hρ.le ha]

end Erdos3

end

end OAI
