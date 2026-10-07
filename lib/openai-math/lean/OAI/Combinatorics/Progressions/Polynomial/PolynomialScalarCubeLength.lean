/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Dynamics.ScalarCubePrimitiveBudget
import OAI.Combinatorics.Progressions.Estimates.CoarseLocalizationError

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

namespace NormalizedScalarCubeSource

variable {I : Type*} [Fintype I] [DecidableEq I] (s : NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U ε W : ℝ}
    (h : ScalarCubePrimitiveBudget s A U) (hε : 0 < ε) (hε1 : ε ≤ 1) (hW : 1 ≤ W)
    (hlen : localizationLengthBudget U ε W ≤ s.length)

noncomputable def polynomialLocalizationData : ScalarCubeLocalizationData I := by
  have hU0 : 0 < U := by linarith [h.one_le]
  have hδ := localizationMesh_pos h.one_le hε
  have hbase : U ^ 2 ≤ (s.length : ℝ) :=
    (localizationLengthBudget_ge_square h.one_le hε hε1 hW).trans hlen
  have hgrid : 2 * scalarCubeGridBoundaryConstant I * s.modulusBound /
      volume.real (scalarCubeDomain I) ≤ s.length := by
    calc
      _ = (2 * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I)) * s.modulusBound := by ring
      _ ≤ U * U := mul_le_mul h.grid_le h.modulus_le (Nat.cast_nonneg _) hU0.le
      _ ≤ _ := by nlinarith
  have hδL : 2 * U * W ≤ localizationMesh U ε * s.length := by
    simpa only [localizationMesh_length h.one_le hε] using mul_le_mul_of_nonneg_left hlen hδ.le
  exact {
    length := s.length, modulusBound := s.modulusBound, length_pos := s.length_pos
    modulus := s.modulus, residue := s.residue, modulus_pos := s.modulus_pos
    modulus_le := s.modulus_le, size := s.size
    gridSmall := scalarCubeGrid_small_error_of_length I s.length_pos hgrid
    transitionBound := A, transition_lipschitz := hA
    radius := ⟨localizationRadius U ε, (localizationRadius_pos h.one_le hε).le⟩
    radius_pos := localizationRadius_pos h.one_le hε
    weight := s.weight, weightBound := s.weightBound, weightLipschitz := s.weightLipschitz
    weightBound_pos := s.weightBound_pos, weight_range := s.weight_range
    weight_lipschitz := s.weight_lipschitz, normalized := s.normalized
    mesh := localizationMesh U ε, mesh_pos := hδ
    mesh_le_one := localizationMesh_le_one h.one_le hε hε1
    meshLarge := by
      have hw := le_mul_of_one_le_right hU0.le hW
      nlinarith [h.modulus_le]
    margin := (mul_le_mul_of_nonneg_right h.dimension_le hδ.le).trans_lt
      (localizationMesh_margin h.one_le hε hε1) }

theorem polynomialLocalizationData_source :
    (s.polynomialLocalizationData A hA h hε hε1 hW hlen).source = s.source := rfl

theorem polynomialLocalizationData_cellLength :
    W ≤ ((s.polynomialLocalizationData A hA h hε hε1 hW hlen).cellLength : ℝ) := by
  let d := s.polynomialLocalizationData A hA h hε hε1 hW hlen
  have hM : (0 : ℝ) < s.modulusBound := by
    exact_mod_cast (s.modulus_pos none).trans_le (s.modulus_le none)
  have hδ := localizationMesh_pos h.one_le hε
  have hδL : 2 * U * W ≤ localizationMesh U ε * s.length := by
    simpa only [localizationMesh_length h.one_le hε] using mul_le_mul_of_nonneg_left hlen hδ.le
  apply le_trans _ d.cellLength_lower
  change W ≤ localizationMesh U ε * s.length / (2 * s.modulusBound)
  apply (le_div_iff₀ (by positivity)).mpr
  have hm := mul_le_mul_of_nonneg_right h.modulus_le (by linarith : 0 ≤ W)
  nlinarith

theorem polynomialLocalizationData_error {η : ℝ} (hη : 0 ≤ η) :
    (s.polynomialLocalizationData A hA h hε hε1 hW hlen).error η ≤ ε + U ^ 2 * η := by
  have hM : 0 < s.modulusBound := (s.modulus_pos none).trans_le (s.modulus_le none)
  have hC0 : 0 ≤ paddedResidueDensityCap I s.modulusBound := by
    have hc := scalarCubeResidueDensityCap_pos I s.modulusBound hM
    unfold paddedResidueDensityCap
    positivity
  have hG0 : 0 ≤ 2 * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I) := by
    have hg := scalarCubeGridBoundaryConstant_pos I
    have hv := scalarCubeDomain_volumeReal_pos I
    positivity
  have hH0 : 0 ≤ scalarCubeCutoffDerivativeNumerator I A := by
    unfold scalarCubeCutoffDerivativeNumerator
    positivity
  have he := polynomial_localization_error h.one_le s.weightBound.coe_nonneg hC0 hG0 hH0
    s.weightLipschitz.coe_nonneg (Nat.cast_nonneg s.modulusBound)
    h.weight_le h.density_le h.grid_le h.derivative_le h.weightLipschitz_le h.modulus_le
    (by exact_mod_cast s.length_pos) hη hε hε1 hW hlen
    (scalarCubeBoundaryConstant_pos I).le h.boundary_le
  let r : ℝ≥0 := ⟨localizationRadius U ε, (localizationRadius_pos h.one_le hε).le⟩
  have hr : (r : ℝ) = localizationRadius U ε := rfl
  have hq : (scalarCubeCutoffLipschitzConstant I A r : ℝ) =
      scalarCubeCutoffDerivativeNumerator I A / localizationRadius U ε :=
    scalarCubeCutoffLipschitzConstant_eq I A r
  change (s.weightBound : ℝ) * scalarCubeResidueCutoffBudget I A r s.length s.modulusBound +
    paddedResidueDensityCap I s.modulusBound *
      (((s.weightLipschitz : ℝ) + s.weightBound * scalarCubeCutoffLipschitzConstant I A r) *
        localizationMesh U ε + s.weightBound * η) ≤ _
  unfold scalarCubeResidueCutoffBudget
  rw [hq, hr]
  simpa only [mul_div_assoc] using he

end NormalizedScalarCubeSource

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

namespace NormalizedScalarCubeSource

theorem polynomialLocalizationData_lengthLoss {I : Type*} [Fintype I] [DecidableEq I]
    (s : NormalizedScalarCubeSource I) (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    {U ε W : ℝ} (h : ScalarCubePrimitiveBudget s A U) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hW : 1 ≤ W) (hlen : localizationLengthBudget U ε W ≤ s.length) :
    (s.polynomialLocalizationData A hA h hε hε1 hW hlen).lengthLoss ≤
      localizationLengthBudget U ε 1 := by
  change 2 * (s.modulusBound : ℝ) / localizationMesh U ε ≤ _
  calc
    _ ≤ 2 * U / localizationMesh U ε :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h.modulus_le (by norm_num))
        (localizationMesh_pos h.one_le hε).le
    _ = _ := by
      have hU : U ≠ 0 := ne_of_gt (by linarith [h.one_le])
      unfold localizationMesh localizationLengthBudget
      field_simp
      ring

end NormalizedScalarCubeSource

theorem polynomialScalarCube_inverse_product {J : Type*} [Fintype J]
    (I : J → Type*) [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
    (s : ∀ j, NormalizedScalarCubeSource (I j))
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U ε W : ℝ}
    (h : ∀ j, ScalarCubePrimitiveBudget (s j) A U) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hW : 1 ≤ W) (hlen : ∀ j, localizationLengthBudget U ε W ≤ (s j).length)
    {Q : ℝ} (hQ : 0 ≤ Q) :
    Q / (∏ j, (((s j).polynomialLocalizationData A hA (h j) hε hε1 hW (hlen j)).cellLength : ℝ)) ≤
      Q * (localizationLengthBudget U ε 1) ^ Fintype.card J / ∏ j, ((s j).length : ℝ) := by
  let d j := (s j).polynomialLocalizationData A hA (h j) hε hε1 hW (hlen j)
  have hp : (∏ j, (d j).lengthLoss) ≤ (localizationLengthBudget U ε 1) ^ Fintype.card J := by
    calc
      _ ≤ ∏ _j : J, localizationLengthBudget U ε 1 :=
        Finset.prod_le_prod₀ (fun j _ => (d j).lengthLoss_pos.le)
          (fun j _ => (s j).polynomialLocalizationData_lengthLoss A hA (h j) hε hε1 hW (hlen j))
      _ = _ := by simp only [Finset.prod_const, Finset.card_univ]
  exact (scalarCubeCell_inverse_product I d hQ).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp hQ) (by positivity))

end Erdos3

end

end OAI
