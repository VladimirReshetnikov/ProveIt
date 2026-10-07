import OAI.Combinatorics.Progressions.Estimates.PreparedEmptyLayerFiniteScheduleLocalDirectSource
import OAI.Combinatorics.Progressions.Linear.PreparedFiniteNestedSourceProjectionBudget
import OAI.Combinatorics.Progressions.Probability.PreparedGeometryConditionalExcess
import OAI.Combinatorics.Progressions.Sampling.AllocatedScalarEmptyLayerSampler
import OAI.Combinatorics.Progressions.Sampling.AllocatedZeroLayerDetectionFromEmptySampler

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m nX : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {Stage : Type} (degree : Stage → ℕ)
variable (selection : ∀ k, Fin (degree k + 1) ↪ G)
variable (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ)
variable (sourceU modelLog sliceLog α : Stage → ℝ) (Vtail : Fin m → ℝ≥0) (τ : ℝ)
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]

theorem preparedFiniteScheduleLocalCandidateDetection
    (Pchart Qstride : ℝ) (Pmaster : Stage → ℝ) (Plate : ℝ)
    (Pphysical : Stage → ℝ) (coarseTarget : ℝ) (pGain : Stage → ℝ)
    (hAvailable : ∀ k, PreparedScheduledDirectSourceAvailability
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection k) (stride := stride) (N := N)
      (Pdetect := Pdetect) (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
      (Vtail := Vtail) (τ := τ) (hb := hb) (o := o)
      Pchart Qstride (Pmaster k) Plate (pGain k) (Pphysical k) coarseTarget)
    (hαLower : ∀ k, Real.exp (-(2 * sourceU k + 4 * modelLog k + 7)) ≤ α k / 2)
    (hαHalfOne : ∀ k, α k / 2 ≤ 1)
    (hstride : ∀ i, 0 < stride i)
    (hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCbound : ∀ j, C j ≤ Real.exp Pchart)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) v‖ ≤ Cforward j * ‖v‖)
    (hForward : ∀ j, (Cforward j : ℝ) ≤ Real.exp Pchart)
    (hVtail : ∀ j, (Vtail j : ℝ) ≤ Real.exp Pchart)
    (hVactual : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Vtail j)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pchart)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Pchart)
    (hτ : 0 < τ) (hτInv : ∀ k, τ⁻¹ ≤ Real.exp (Pphysical k))
    (hτHalf : τ ≤ 1 / 2) (hτDim : (nX : ℝ) * τ ≤ 1 / 2)
    {ξ : ℝ} (hξ : 0 < ξ)
    (hξSmall : ∀ k, ξ ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) (selection k)
      (allocatedDetectedKernelCutoff (degree k) G (Fintype.card (LayerSamplerVariables G I n B))
        Pdetect (allocatedModelTestLog (sourceU k) (modelLog k))
        (allocatedModelTestLog (sourceU k) (modelLog k)) (α k / 2))
      (Pphysical k) coarseTarget)
    (hξLate : ξ⁻¹ ≤ Real.exp Plate)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (poly j))
    (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
    {Rrank : ℝ}
    (hsize : ∀ k i, Real.exp
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m (degree k))
        (degree k + 1) (Pmaster k) Plate).required ≤ (N i : ℝ))
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (hRank : ∀ k, Real.exp
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m (degree k))
        (degree k + 1) (Pmaster k) Plate).required ≤ Rrank)
    (hCells : cells.Nonempty)
    (hdimension : ∀ k, (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤
      Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k)))
    (A : AllocatedExternalCandidateSamplerFamily B U basis S hb o hR hσ N poly hmem τ ξ stride cells) :
    ∀ k center, (A center).NativeDetection (degree k) (sliceLog k)
      (Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k)))
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m (degree k))
        (degree k + 1) (Pmaster k) Plate).nativeBudget (α k) := by
  intro k
  have hDirect := hAvailable k (α k / 2) (hαLower k) (hαHalfOne k)
  have hconditional := preparedModularGeneralConditionalDetectionFreeTrimSharedWidth_of_direct
    (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
    (selection := selection k) (stride := stride) (N := N)
    (Pdetect := Pdetect) (u := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
    (Vtail := Vtail) (α := α k) (τ := τ) (hb := hb) (o := o)
    Pchart Qstride (Pmaster k) Plate (pGain k) (Pphysical k) coarseTarget hDirect
  have hα : 0 < α k := by
    have hhalf := (Real.exp_pos _).trans_le (hαLower k)
    linarith only [hhalf]
  obtain ⟨Ak, _hcenter, hdetect⟩ :=
    exists_allocatedExternalCandidateSamplerFamily_nativeDetection
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection k) (stride := stride) (N := N)
      (Pdetect := Pdetect) (u := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
      (Vtail := Vtail) (α := α k) (τ := τ) (hb := hb) (o := o)
      Pchart Qstride (Pmaster k) Plate (pGain k) (Pphysical k) coarseTarget hconditional
      hstride hstrideBound C hC hCbound hchart Cforward hforward hForward hVtail hVactual
      hprofile hcutoff hτ (hτInv k) hτHalf hτDim hξ (hξSmall k) hξLate
      cells poly hp hmem (hsize k) hrank (hRank k) hCells hα (hdimension k)
  have hsame : Ak = A := Subsingleton.elim _ _
  rw [hsame] at hdetect
  exact hdetect

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

theorem preparedEmptyLayerFiniteScheduleCandidateDetection
    {m nX : ℕ} {G : Type} [Fintype G] [DecidableEq G]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    [∀ j, IsEmpty (I j)] [∀ j, IsEmpty (J j)]
    {n : Fin m → ℕ} [∀ j, IsEmpty (Fin (n j))]
    (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (S : LayerSamplerScale (G := G) B U b R σ)
    {K : Type} (degree : K → ℕ) (selection : ∀ k, Fin (degree k + 1) ↪ G)
    (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ)
    (sourceU modelLog sliceLog α : K → ℝ) (τ ξ : ℝ)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (Pchart Qstride : ℝ) (Pmaster : K → ℝ) (Plate : ℝ)
    (Pphysical : K → ℝ) (coarseTarget : ℝ) (pGain : K → ℝ)
    (hAvailable : ∀ k, PreparedScheduledDirectSourceAvailability
      (B := B) (U := U) (basis := b) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection k) (stride := stride) (N := N) (Pdetect := Pdetect)
      (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
      (Vtail := fun _ => 1) (τ := τ) (hb := hb) (o := o)
      Pchart Qstride (Pmaster k) Plate (pGain k) (Pphysical k) coarseTarget)
    (hαLower : ∀ k, Real.exp (-(2 * sourceU k + 4 * modelLog k + 7)) ≤ α k / 2)
    (hαHalfOne : ∀ k, α k / 2 ≤ 1)
    (hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pchart)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Pchart)
    (hτInv : ∀ k, τ⁻¹ ≤ Real.exp (Pphysical k))
    (hτHalf : τ ≤ 1 / 2) (hτDim : (nX : ℝ) * τ ≤ 1 / 2)
    (hξSmall : ∀ k, ξ ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) (selection k)
      (allocatedDetectedKernelCutoff (degree k) G (Fintype.card (LayerSamplerVariables G I n B))
        Pdetect (allocatedModelTestLog (sourceU k) (modelLog k))
        (allocatedModelTestLog (sourceU k) (modelLog k)) (α k / 2))
      (Pphysical k) coarseTarget)
    (hξLate : ξ⁻¹ ≤ Real.exp Plate)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
    (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
    (hsize : ∀ k i, Real.exp
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m (degree k))
        (degree k + 1) (Pmaster k) Plate).required ≤ (N i : ℝ))
    (hdimension : ∀ k, (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤
      Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k)))
    (center : CoefficientTorus (K := LayerSamplerVariables G I n B) U)
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ
      N poly hmem τ ξ stride cells center) :
    ∀ k, A.NativeDetection (degree k) (sliceLog k)
      (Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k)))
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m (degree k))
        (degree k + 1) (Pmaster k) Plate).nativeBudget (α k) := by
  let : MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U) := borel _
  let : BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U) := ⟨rfl⟩
  have hCells : cells.Nonempty := by
    by_contra h
    have hz : cells = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    have hmass := A.smooth_mass_pos
    simp only [hz, selectedResidueSmoothWeight, Finset.notMem_empty, ↓reduceIte,
      tsum_zero, lt_self_iff_false] at hmass
  have hone : (1 : ℝ) ≤ Real.exp Pchart :=
    (show (1 : ℝ) ≤ normalizedSiteCutoffBound by
      exact_mod_cast normalizedSiteCutoffBound_one_le).trans hcutoff
  have hp (j) : DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (poly j) := by
    intro e he
    exact Subsingleton.elim _ _
  have hrank (j) (rank : ℝ) :
      HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) rank (U j) (poly j) := by
    intro a ha hw
    obtain ⟨w, hw⟩ := hw
    exact (hw (Finset.sum_eq_zero (fun i _ => isEmptyElim i))).elim
  have hchart (j) (v) :
      ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤
        (0 : ℝ) * ‖v‖ := by
    have hz : (normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v = 0 :=
      Subsingleton.elim _ _
    simp only [hz, norm_zero, zero_mul, le_refl]
  have hforward (j) (v) :
      ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤
        ((0 : ℝ≥0) : ℝ) * ‖v‖ := by
    have hz : v = 0 := Subsingleton.elim _ _
    simp only [hz, map_zero, norm_zero, mul_zero, le_refl]
  have hratio (j) :
      0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
        mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ (1 : ℝ≥0) := by
    rw [mixedDensityCovolumeRatio_eq_one_of_isEmpty]
    norm_num
  intro k
  have hDirect := hAvailable k (α k / 2) (hαLower k) (hαHalfOne k)
  have hconditional := preparedModularGeneralConditionalDetectionFreeTrimSharedWidth_of_direct
    (B := B) (U := U) (basis := b) (S := S) (hR := hR) (hσ := hσ)
    (selection := selection k) (stride := stride) (N := N)
    (Pdetect := Pdetect) (u := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
    (Vtail := fun _ => 1) (α := α k) (τ := τ) (hb := hb) (o := o)
    Pchart Qstride (Pmaster k) Plate (pGain k) (Pphysical k) coarseTarget hDirect
  have hα : 0 < α k := by
    have hhalf := (Real.exp_pos _).trans_le (hαLower k)
    linarith only [hhalf]
  obtain ⟨Ak, _, hdetect⟩ :=
    exists_allocatedExternalCandidateSamplerFamily_nativeDetection
      (B := B) (U := U) (basis := b) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection k) (stride := stride) (N := N)
      (Pdetect := Pdetect) (u := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
      (Vtail := fun _ => 1) (α := α k) (τ := τ) (hb := hb) (o := o)
      Pchart Qstride (Pmaster k) Plate (pGain k) (Pphysical k) coarseTarget hconditional
      A.stride_pos hstrideBound (fun _ => 0) (fun _ => le_refl 0)
      (fun _ => (Real.exp_pos _).le) hchart (fun _ => 0) hforward
      (fun _ => (Real.exp_pos _).le) (fun _ => hone) hratio
      hprofile hcutoff A.trim_pos (hτInv k) hτHalf hτDim A.narrow_pos (hξSmall k) hξLate
      cells poly hp hmem (hsize k) (fun j => hrank j _) (le_refl _) hCells hα (hdimension k)
  have hsame : Ak center = A := Subsingleton.elim _ _
  have hd : (Ak center).NativeDetection (degree k) (sliceLog k)
      (Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k)))
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m (degree k))
        (degree k + 1) (Pmaster k) Plate).nativeBudget (α k) := hdetect center
  rw [hsame] at hd
  exact @hd

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m nX : ℕ} {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {Stage : Type} (degree : Stage → ℕ)
variable (selection : ∀ k, Fin (degree k + 1) ↪ G)
variable (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ)
variable (sourceU modelLog sliceLog α : Stage → ℝ) (Vtail : Fin m → ℝ≥0) (τ : ℝ)
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]

theorem exists_preparedFiniteScheduleLocalCandidateFamily
    (kAnchor : Stage)
    (Pchart Qstride : ℝ) (Pmaster : Stage → ℝ) (Plate : ℝ)
    (Pphysical : Stage → ℝ) (coarseTarget : ℝ) (pGain : Stage → ℝ)
    (hAvailable : ∀ k, PreparedScheduledDirectSourceAvailability
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection k) (stride := stride) (N := N)
      (Pdetect := Pdetect) (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
      (Vtail := Vtail) (τ := τ) (hb := hb) (o := o)
      Pchart Qstride (Pmaster k) Plate (pGain k) (Pphysical k) coarseTarget)
    (hαLower : ∀ k, Real.exp (-(2 * sourceU k + 4 * modelLog k + 7)) ≤ α k / 2)
    (hαHalfOne : ∀ k, α k / 2 ≤ 1)
    (hstride : ∀ i, 0 < stride i)
    (hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCbound : ∀ j, C j ≤ Real.exp Pchart)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) v‖ ≤ Cforward j * ‖v‖)
    (hForward : ∀ j, (Cforward j : ℝ) ≤ Real.exp Pchart)
    (hVtail : ∀ j, (Vtail j : ℝ) ≤ Real.exp Pchart)
    (hVactual : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Vtail j)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pchart)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Pchart)
    (hτ : 0 < τ) (hτInv : ∀ k, τ⁻¹ ≤ Real.exp (Pphysical k))
    (hτHalf : τ ≤ 1 / 2) (hτDim : (nX : ℝ) * τ ≤ 1 / 2)
    {ξ : ℝ} (hξ : 0 < ξ)
    (hξSmall : ∀ k, ξ ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) (selection k)
      (allocatedDetectedKernelCutoff (degree k) G (Fintype.card (LayerSamplerVariables G I n B))
        Pdetect (allocatedModelTestLog (sourceU k) (modelLog k))
        (allocatedModelTestLog (sourceU k) (modelLog k)) (α k / 2))
      (Pphysical k) coarseTarget)
    (hξLate : ξ⁻¹ ≤ Real.exp Plate)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (poly j))
    (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
    {Rrank : ℝ}
    (hsize : ∀ k i, Real.exp
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m (degree k))
        (degree k + 1) (Pmaster k) Plate).required ≤ (N i : ℝ))
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (hRank : ∀ k, Real.exp
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m (degree k))
        (degree k + 1) (Pmaster k) Plate).required ≤ Rrank)
    (hCells : cells.Nonempty)
    (hdimension : ∀ k, (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤
      Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k)))
    : ∃ A : AllocatedExternalCandidateSamplerFamily B U basis S hb o hR hσ N poly hmem τ ξ stride cells,
    ∀ k center, (A center).NativeDetection (degree k) (sliceLog k)
      (Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k)))
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m (degree k))
        (degree k + 1) (Pmaster k) Plate).nativeBudget (α k) := by
  have hDirect := hAvailable kAnchor (α kAnchor / 2) (hαLower kAnchor) (hαHalfOne kAnchor)
  have hconditional := preparedModularGeneralConditionalDetectionFreeTrimSharedWidth_of_direct
    (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
    (selection := selection kAnchor) (stride := stride) (N := N)
    (Pdetect := Pdetect) (u := sourceU kAnchor) (pModel := modelLog kAnchor) (pSlice := sliceLog kAnchor)
    (Vtail := Vtail) (α := α kAnchor) (τ := τ) (hb := hb) (o := o)
    Pchart Qstride (Pmaster kAnchor) Plate (pGain kAnchor) (Pphysical kAnchor) coarseTarget hDirect
  have hα : 0 < α kAnchor := by
    have hhalf := (Real.exp_pos _).trans_le (hαLower kAnchor)
    linarith only [hhalf]
  obtain ⟨A, _hcenter, _hdetect⟩ :=
    exists_allocatedExternalCandidateSamplerFamily_nativeDetection
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection kAnchor) (stride := stride) (N := N)
      (Pdetect := Pdetect) (u := sourceU kAnchor) (pModel := modelLog kAnchor) (pSlice := sliceLog kAnchor)
      (Vtail := Vtail) (α := α kAnchor) (τ := τ) (hb := hb) (o := o)
      Pchart Qstride (Pmaster kAnchor) Plate (pGain kAnchor) (Pphysical kAnchor) coarseTarget hconditional
      hstride hstrideBound C hC hCbound hchart Cforward hforward hForward hVtail hVactual
      hprofile hcutoff hτ (hτInv kAnchor) hτHalf hτDim hξ (hξSmall kAnchor) hξLate
      cells poly hp hmem (hsize kAnchor) hrank (hRank kAnchor) hCells hα (hdimension kAnchor)
  refine ⟨A, ?_⟩
  exact preparedFiniteScheduleLocalCandidateDetection B U basis hR hσ S degree selection stride N
    Pdetect sourceU modelLog sliceLog α Vtail τ hb o
    Pchart Qstride Pmaster Plate Pphysical coarseTarget pGain hAvailable hαLower hαHalfOne
    hstride hstrideBound C hC hCbound hchart Cforward hforward hForward hVtail hVactual
    hprofile hcutoff hτ hτInv hτHalf hτDim hξ hξSmall hξLate
    cells poly hp hmem hsize hrank hRank hCells hdimension A

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m nX : ℕ}
noncomputable local instance fixedSourceFinDecidableEq : DecidableEq (Fin nX) := Classical.decEq _
variable {G : Type} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {Stage : Type} (degree : Stage → ℕ)
variable (selection : ∀ k, Fin (degree k + 1) ↪ G)
variable (stride N : Fin nX → ℕ) (Pdetect : Polynomial ℕ)
variable (sourceU modelLog sliceLog α : Stage → ℝ) (Vtail : Fin m → ℝ≥0) (τ : ℝ)
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]

theorem exists_preparedFiniteScheduleFixedCenterSource
    (kAnchor : Stage)
    (Pchart Qstride : ℝ) (Pmaster : Stage → ℝ) (Plate : ℝ)
    (Pphysical : Stage → ℝ) (coarseTarget : ℝ) (pGain : Stage → ℝ)
    (hAvailable : ∀ k, PreparedScheduledDirectSourceAvailability
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection k) (stride := stride) (N := N)
      (Pdetect := Pdetect) (sourceU := sourceU k) (pModel := modelLog k) (pSlice := sliceLog k)
      (Vtail := Vtail) (τ := τ) (hb := hb) (o := o)
      Pchart Qstride (Pmaster k) Plate (pGain k) (Pphysical k) coarseTarget)
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    {Pscale D target Pk Prho pRadius E : ℝ}
    (scalar : PreparedUniformDegreeDirectScalarBounds m (degree kAnchor) nX
      (Fintype.card (LayerSamplerVariables G I n B))
      (sampledSupportedSlicedDetectionConstant (degree kAnchor) Pdetect)
      Pchart Pscale D target Pk Prho Qstride (Pmaster kAnchor) Plate (pGain kAnchor)
      (Pphysical kAnchor) coarseTarget pRadius (sourceU kAnchor) (modelLog kAnchor) (sliceLog kAnchor))
    (geometryAt : PreparedUniformDegreeGeometryAt B U basis S (degree kAnchor)
      (sampledSupportedSlicedDetectionConstant (degree kAnchor) Pdetect) nX
      Pchart Pscale D target Pk Prho Qstride (allocatedModelTestLog (sourceU kAnchor) (modelLog kAnchor))
      pRadius (2 * sourceU kAnchor + 4 * modelLog kAnchor + 7) (pGain kAnchor))
    (hSLate : (S.value : ℝ) ≤ Real.exp Plate)
    (hαLower : ∀ k, Real.exp (-(2 * sourceU k + 4 * modelLog k + 7)) ≤ α k / 2)
    (hαHalfOne : ∀ k, α k / 2 ≤ 1)
    (hstride : ∀ i, 0 < stride i)
    (hstrideBound : ∀ i, (stride i : ℝ) ≤ Real.exp Qstride)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j) (hCbound : ∀ j, C j ≤ Real.exp Pchart)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤ C j * ‖v‖)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) v‖ ≤ Cforward j * ‖v‖)
    (hForward : ∀ j, (Cforward j : ℝ) ≤ Real.exp Pchart)
    (hVtail : ∀ j, (Vtail j : ℝ) ≤ Real.exp Pchart)
    (hVactual : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ Vtail j)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Pchart)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Pchart)
    (hτ : 0 < τ) (hτInv : ∀ k, τ⁻¹ ≤ Real.exp (Pphysical k))
    (hτHalf : τ ≤ 1 / 2) (hτDim : (nX : ℝ) * τ ≤ 1 / 2)
    {ξ : ℝ} (hξ : 0 < ξ)
    (hξSmall : ∀ k, ξ ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex B (layerSamplerDegree I n)) (selection k)
      (allocatedDetectedKernelCutoff (degree k) G (Fintype.card (LayerSamplerVariables G I n B))
        Pdetect (allocatedModelTestLog (sourceU k) (modelLog k))
        (allocatedModelTestLog (sourceU k) (modelLog k)) (α k / 2))
      (Pphysical k) coarseTarget)
    (hξLate : ξ⁻¹ ≤ Real.exp Plate)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
    (poly : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : Fin nX → ℕ) (j.val + 1) (poly j))
    (hmem : ∀ j ex, coefficients (poly j) ex ∈ U j)
    {Rrank : ℝ}
    (hsize : ∀ k i, Real.exp
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m (degree k))
        (degree k + 1) (Pmaster k) Plate).required ≤ (N i : ℝ))
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (hRank : ∀ k, Real.exp
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m (degree k))
        (degree k + 1) (Pmaster k) Plate).required ≤ Rrank)
    (hsizeConditional : ∀ i, Real.exp (preparedConditionalExcessRequired m Plate E) ≤ (N i : ℝ))
    (hRankConditional : Real.exp (preparedConditionalExcessRequired m Plate E) ≤ Rrank)
    (hCells : cells.Nonempty)
    (hdimension : ∀ k, (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤
      Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k)))
    : ∃ hmargin : ∀ i, 2 * spatialTrimMargin τ N i ≤ N i,
    ∃ A : AllocatedExternalCandidateSamplerFamily B U basis S hb o hR hσ N poly hmem τ ξ stride cells,
    (∀ k center, (A center).NativeDetection (degree k) (sliceLog k)
      (Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k)))
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants m (degree k))
        (degree k + 1) (Pmaster k) Plate).nativeBudget (α k)) ∧
    ∀ center : CoefficientTorus (K := LayerSamplerVariables G I n B) U,
      letI : Nonempty (A center).Site := (A center).site_nonempty
      (FiniteProbabilityWeights.uniformFinset (integerBox N) (A center).integerBox_nonempty).excessMass
        ((A center).law.siteLaw ((A center).physicalBox
          ((hξSmall kAnchor).trans (min_le_left _ _)) hmargin))
        (4 * ∏ j, earlyConstantDensityCap (Fintype.card (I j)) (n j) (R j) (Vtail j)) ≤
          6 * positiveProjectionAccuracy E := by
  have hDirect := hAvailable kAnchor (α kAnchor / 2) (hαLower kAnchor) (hαHalfOne kAnchor)
  have hconditional := preparedModularGeneralConditionalDetectionFreeTrimSharedWidth_of_direct
    (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
    (selection := selection kAnchor) (stride := stride) (N := N)
    (Pdetect := Pdetect) (u := sourceU kAnchor) (pModel := modelLog kAnchor) (pSlice := sliceLog kAnchor)
    (Vtail := Vtail) (α := α kAnchor) (τ := τ) (hb := hb) (o := o)
    Pchart Qstride (Pmaster kAnchor) Plate (pGain kAnchor) (Pphysical kAnchor) coarseTarget hDirect
  obtain ⟨_hN, _hbases, _hbox, _hmass, _hnormalizer, hmargin, _hcenter, _hweight, _hdetect⟩ :=
    hconditional hstride hstrideBound C hC hCbound hchart Cforward hforward hForward
      hVtail hVactual hprofile hcutoff hτ (hτInv kAnchor) hτHalf hτDim hξ (hξSmall kAnchor) hξLate
      cells poly hp hmem (hsize kAnchor) hrank (hRank kAnchor) hCells
  have hα : 0 < α kAnchor := by
    have hhalf := (Real.exp_pos _).trans_le (hαLower kAnchor)
    linarith only [hhalf]
  obtain ⟨A, _hcenter, _hdetect⟩ :=
    exists_allocatedExternalCandidateSamplerFamily_nativeDetection
      (B := B) (U := U) (basis := basis) (S := S) (hR := hR) (hσ := hσ)
      (selection := selection kAnchor) (stride := stride) (N := N)
      (Pdetect := Pdetect) (u := sourceU kAnchor) (pModel := modelLog kAnchor) (pSlice := sliceLog kAnchor)
      (Vtail := Vtail) (α := α kAnchor) (τ := τ) (hb := hb) (o := o)
      Pchart Qstride (Pmaster kAnchor) Plate (pGain kAnchor) (Pphysical kAnchor) coarseTarget hconditional
      hstride hstrideBound C hC hCbound hchart Cforward hforward hForward hVtail hVactual
      hprofile hcutoff hτ (hτInv kAnchor) hτHalf hτDim hξ (hξSmall kAnchor) hξLate
      cells poly hp hmem (hsize kAnchor) hrank (hRank kAnchor) hCells hα (hdimension kAnchor)
  refine ⟨hmargin, A, ?_, ?_⟩
  · have hdec : instDecidableEqFin nX = Classical.decEq (Fin nX) := Subsingleton.elim _ _
    have hdet := preparedFiniteScheduleLocalCandidateDetection B U basis hR hσ S degree selection stride N
      Pdetect sourceU modelLog sliceLog α Vtail τ hb o
      Pchart Qstride Pmaster Plate Pphysical coarseTarget pGain hAvailable hαLower hαHalfOne
      hstride hstrideBound C hC hCbound hchart Cforward hforward hForward hVtail hVactual
      hprofile hcutoff hτ hτInv hτHalf hτDim hξ hξSmall hξLate
      cells poly hp hmem hsize hrank hRank hCells hdimension A
    rw [hdec] at hdet
    exact hdet
  · exact A.prepared_conditional_excess μ ν scalar geometryAt hSLate
      Cforward Vtail hforward hForward hVactual hVtail C hC hCbound hchart hp
      hstrideBound (hτInv kAnchor) hτHalf hτDim
      ((hξSmall kAnchor).trans (min_le_left _ _)) hξLate
      hsizeConditional hrank hRankConditional hCells (A 0).integerBox_nonempty hmargin

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

namespace AllocatedExternalCandidateSampler
variable {s nX : ℕ}
    {I₀ J₀ : Fin 0 → Type} [∀ j, Fintype (I₀ j)] [∀ j, Fintype (J₀ j)]
    {n₀ : Fin 0 → ℕ} {B₀ : LayerSamplerAxis I₀ n₀ → Type} [∀ a, Fintype (B₀ a)]
    {U₀ : ∀ j, Submodule ℝ (J₀ j → ℝ)}
    {b₀ : ∀ j, Basis (Fin (n₀ j)) ℝ (euclideanSubspace (U₀ j))ᗮ}
    {R₀ σ₀ : Fin 0 → ℝ}
    {S₀ : LayerSamplerScale (G := Fin (scalarNativeDimension s)) B₀ U₀ b₀ R₀ σ₀}
    {hb₀ : ∀ j, span ℤ (Set.range (b₀ j)) = projectedIntegerLattice (euclideanSubspace (U₀ j))}
    {o₀ : ∀ j, OrthonormalBasis (I₀ j) ℝ (euclideanSubspace (U₀ j))}
    {hR₀ : ∀ j, 0 < R₀ j} {hσ₀ : ∀ j, 0 < σ₀ j}
    {N : Fin nX → ℕ} {poly₀ : ∀ j, VectorPolynomial (Fin nX) ℝ (J₀ j → ℝ)}
    {hmem₀ : ∀ j e, coefficients (poly₀ j) e ∈ U₀ j}
    {τ ξ₀ : ℝ}
    {center₀ : CoefficientTorus (K := LayerSamplerVariables (Fin (scalarNativeDimension s)) I₀ n₀ B₀) U₀}
    [∀ j, IsZLattice ℝ
      (latticeSection (standardEuclideanLattice (J₀ j)) (euclideanSubspace (U₀ j)))]

theorem nativeDetection_of_preparedScalarFiniteSchedule
    (A₀ : AllocatedExternalCandidateSampler B₀ U₀ b₀ S₀ hb₀ o₀ hR₀ hσ₀
      N poly₀ hmem₀ τ ξ₀ (fun _ : Fin nX => 1) {0} center₀)
    {K : Type} [Fintype K] (degree : K → ℕ) (hdegree : ∀ k, degree k ≤ s)
    (Pdetect : Polynomial ℕ) (Bstruct extraLate : ℝ)
    (sourceU modelLog sliceLog α : K → ℝ)
    (hB : 0 ≤ Bstruct) (hnum : (scalarNativeDimension s : ℝ) ≤ Bstruct)
    (hsourceU : ∀ k, 0 ≤ sourceU k) (hmodelLog : ∀ k, 0 ≤ modelLog k)
    (hsliceModel : ∀ k, sliceLog k ≤ modelLog k)
    (hcountModel : ∀ k, (scalarNativeDimension s : ℝ) ≤ Real.exp (modelLog k))
    (hαLower : ∀ k, Real.exp (-(2 * sourceU k + 4 * modelLog k + 7)) ≤ α k / 2)
    (hαHalfOne : ∀ k, α k / 2 ≤ 1)
    (hprofile : (probabilityProfileLipschitz : ℝ) ≤ Real.exp Bstruct)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp Bstruct)
    (hdimension : ∀ k, (scalarNativeDimension s : ℝ) ≤
      Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k))) :
    let q := max s 1
    let count := scalarNativeDimension s
    let Cdetect := fun k => sampledSupportedSlicedDetectionConstant (degree k) Pdetect
    let pRadius := allocatedCommonProductRadiusLog q Bstruct Bstruct
    let D := allocatedComparisonDimension q (count : ℝ)
    let pDetect := fun k => allocatedModelTestLog (sourceU k) (modelLog k)
    let aDetect := fun k => 2 * sourceU k + 4 * modelLog k + 7
    let detectionGain := fun k => slicedDetectionGainLog (degree k) (Cdetect k)
      count (pDetect k) (pDetect k) (aDetect k)
    let Pk := fun k => scalarKernelLogarithmicBudget (Fin (degree k + 1))
      (Fin (scalarNativeDimension s)) (detectionGain k + pDetect k + 4)
    let Pphysical := fun k => preparedFiniteScheduleLocalPhysical q nX count 0 (Pk k)
    let target := fun k => detectionGain k + 40 + coefficientErrorSpatialLog (Pphysical k)
    let E := fun k => target k + D * ((q * 2 ^ (q + 1) : ℕ) * Pk k) + 5
    let Prho := fun k => 2 * affineProfileInputEnvelope D
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E k) (pDetect k + 2) + 2
    let Ptail := fun k => affineProfileToleranceEnvelope q D (D * (D + 1) + D * D + D + 1)
      (canonicalSublevelCutoffLip : ℝ) (canonicalTransitionLip : ℝ) (E k) (pDetect k + 2)
    let Pscale := preparedUniformDegreeScaleLog (D + pRadius) Ptail 0
    let Tmod := fun k => ((q + 1 : ℕ) : ℝ) * Pk k + nX * 0
    let lengthLogs := fun k => allocatedAffineLengthLog q D Pscale (Prho k) (Pk k)
      (target k) (pDetect k + 2) (Tmod k)
    let Pmaster := fun k => preparedFiniteScheduleLocalMaster Bstruct D pRadius 0
      (Pphysical k) (sourceU k) (modelLog k) (Prho k) (target k) (detectionGain k)
    let coarseTarget := preparedFiniteScheduleDirectCoarse detectionGain 0
    let localLate := fun k => preparedUniformDegreeDirectLate (Pmaster k) Pscale
      (Pphysical k) coarseTarget extraLate
    let Plate := ∑ k, localLate k
    (∀ k, Real.exp (lengthLogs k) ≤ S₀.value) →
    Real.exp (((probabilityProfileLipschitz : ℝ) + 8) + (D + 4) + pRadius + Pscale) ≤ S₀.value →
    (S₀.value : ℝ) ≤ Real.exp extraLate →
    (∀ k i, Real.exp
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants q (degree k))
        (degree k + 1) (Pmaster k) Plate).required ≤ (N i : ℝ)) →
    (∀ k, τ⁻¹ ≤ Real.exp (Pphysical k)) →
    τ ≤ 1 / 2 → (nX : ℝ) * τ ≤ 1 / 2 →
    ∀ k, A₀.NativeDetection (degree k) (sliceLog k)
      (Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k)))
      (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants q (degree k))
        (degree k + 1) (Pmaster k) Plate).nativeBudget (α k) := by
  intro q count Cdetect pRadius D pDetect aDetect detectionGain Pk Pphysical target E
    Prho Ptail Pscale Tmod lengthLogs Pmaster coarseTarget localLate Plate
    hlength hwidth hSupper hsize hτInv hτHalf hτDim
  let BE := CanonicalEmptyLayerGeometry.B q
  let UE := CanonicalEmptyLayerGeometry.U q
  let bE := CanonicalEmptyLayerGeometry.b q
  let hbE := CanonicalEmptyLayerGeometry.hb q
  let oE := CanonicalEmptyLayerGeometry.o q
  let bWE := CanonicalEmptyLayerGeometry.bW q
  let selection := fun k => scalarNativeSelection (hdegree k)
  have hq : 0 < q := by dsimp only [q]; omega
  have hsq : s ≤ q := le_max_left _ _
  have hsource := exists_preparedEmptyLayerFiniteScheduleLocalDirectSource
    (G := Fin (scalarNativeDimension s)) BE UE bE (fun _ : Fin nX => 1) N Pdetect
    (fun _ => 1) τ (CanonicalEmptyLayerGeometry.Q q) hbE oE bWE
    degree selection hq hsq hdegree
    (by rw [Fintype.card_fin]; exact scalarNativeDimension_capacity (Nat.le_refl s))
    Bstruct 0 0 0 extraLate sourceU modelLog sliceLog hB
    (by simpa only [Fintype.card_fin] using hnum)
    hsourceU hmodelLog hsliceModel
    (fun k => by simpa only [Fintype.card_fin] using hcountModel k)
    (le_refl 0) (le_refl 0)
  simp only [emptyLayerVariables_card, Fintype.card_fin] at hsource
  obtain ⟨hR, σ, hσ, hpRadius, hRadius, hσone, hσexp, hσinv, hscales⟩ := hsource
  have hprofile8 : 8 * (probabilityProfileLipschitz : ℝ) ≤
      Real.exp ((probabilityProfileLipschitz : ℝ) + 8) := by
    have h1 : (probabilityProfileLipschitz : ℝ) ≤ Real.exp (probabilityProfileLipschitz : ℝ) :=
      le_trans (by linarith) (Real.add_one_le_exp _)
    have h8 : (8 : ℝ) ≤ Real.exp (8 : ℝ) :=
      le_trans (by norm_num) (Real.add_one_le_exp _)
    rw [Real.exp_add]
    calc
      _ = (probabilityProfileLipschitz : ℝ) * 8 := by ring
      _ ≤ _ := mul_le_mul h1 h8 (by norm_num) (Real.exp_pos _).le
  have hcount4 : ∀ j : Fin q, 4 * ((Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables (Fin (scalarNativeDimension s)) (CanonicalEmptyLayerGeometry.I q)
        (CanonicalEmptyLayerGeometry.n q) BE) (j.val + 1)) : ℝ) + 1) ≤ Real.exp (D + 4) := by
    intro j
    simpa only [Fintype.card_fin] using emptyLayerCoefficientCount_le_exp (G := Fin (scalarNativeDimension s)) BE j
  let S := emptyLayerSamplerScaleOfExp BE UE bE hR (fun _ => hσ)
    hprofile8 hcount4 (fun j => (hRadius j).2) (fun _ => hσinv)
    S₀.value S₀.positive hwidth
  have hvalue : S.value = S₀.value := rfl
  obtain ⟨scalarAll, geometryAll, availableAll⟩ :=
    hscales S (fun k => hlength k) hSupper
  let poly := CanonicalEmptyLayerGeometry.poly q (Fin nX)
  let hmem := CanonicalEmptyLayerGeometry.poly_mem q (Fin nX)
  let ξ := Real.exp (-Plate)
  let center : CoefficientTorus (K := LayerSamplerVariables (Fin (scalarNativeDimension s))
      (CanonicalEmptyLayerGeometry.I q) (CanonicalEmptyLayerGeometry.n q) BE) UE := 0
  let A : AllocatedExternalCandidateSampler BE UE bE S hbE oE hR (fun _ => hσ)
      N poly hmem τ ξ (fun _ : Fin nX => 1) {0} center :=
    allocatedExternalCandidateSampler_of_scalarReference_empty_layers τ ξ center
      A₀.size_pos A₀.trim_pos (Real.exp_pos _) A₀.bases_nonempty
      A₀.scalarAxesMass_pos_zero_layers
  have hξSmall (k) : ξ ≤ normalizedTupleNarrowWidth (Fin nX)
      (PrincipalTupleIndex BE (layerSamplerDegree (CanonicalEmptyLayerGeometry.I q)
        (CanonicalEmptyLayerGeometry.n q))) (selection k)
      (allocatedDetectedKernelCutoff (degree k) (Fin (scalarNativeDimension s)) count
        Pdetect (pDetect k) (pDetect k) (α k / 2)) (Pphysical k) coarseTarget := by
    have scalarK : PreparedUniformDegreeDirectScalarBounds q (degree k) nX
        (Fintype.card (LayerSamplerVariables (Fin (scalarNativeDimension s))
          (CanonicalEmptyLayerGeometry.I q) (CanonicalEmptyLayerGeometry.n q) BE))
        (Cdetect k) Bstruct Pscale D (target k) (Pk k) (Prho k) 0 (Pmaster k) Plate
        (detectionGain k) (Pphysical k) coarseTarget pRadius
        (sourceU k) (modelLog k) (sliceLog k) := by
      simpa only [emptyLayerVariables_card, Fintype.card_fin] using scalarAll k
    have h := preparedFiniteScheduleDirectWidth BE UE bE S (selection k) Pdetect
      (Cdetect k) rfl Bstruct Pscale D (target k) (Pk k) (Prho k) 0 (Pmaster k) Plate
      (detectionGain k) (Pphysical k) coarseTarget pRadius (sourceU k) (modelLog k)
      (sliceLog k) (α k / 2) scalarK (geometryAll k) (hαLower k)
    simpa only [emptyLayerVariables_card, Fintype.card_fin] using h
  have hξLate : ξ⁻¹ ≤ Real.exp Plate := by
    change (Real.exp (-Plate))⁻¹ ≤ Real.exp Plate
    rw [← Real.exp_neg, neg_neg]
  have hdetect := preparedEmptyLayerFiniteScheduleCandidateDetection
    BE UE bE hR (fun _ => hσ) S degree selection (fun _ : Fin nX => 1) N Pdetect
    sourceU modelLog sliceLog α τ ξ hbE oE Bstruct 0 Pmaster Plate Pphysical coarseTarget
    detectionGain availableAll hαLower hαHalfOne
    (fun _ => by simp only [Nat.cast_one, Real.exp_zero, le_refl])
    hprofile hcutoff hτInv hτHalf hτDim
    (fun k => by simpa only [emptyLayerVariables_card, Fintype.card_fin] using hξSmall k)
    hξLate {0} poly hmem hsize
    (fun k => by simpa only [emptyLayerVariables_card, Fintype.card_fin] using hdimension k)
    center A
  have hdec : instDecidableEqFin nX = Classical.decEq (Fin nX) := Subsingleton.elim _ _
  rw [hdec] at hdetect
  intro k
  rw [hdec]
  exact A₀.nativeDetection_of_emptyLayer_sampler A hvalue (degree k) (sliceLog k)
    (Pdetect.eval₂ (Nat.castRingHom ℝ) (allocatedModelTestLog (sourceU k) (modelLog k)))
    (preparedModularGeneralDetectorResources (preparedModularGeneralDetectorConstants q (degree k))
      (degree k + 1) (Pmaster k) Plate).nativeBudget (α k) (@hdetect k)

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI
