import OAI.Combinatorics.Progressions.Geometry.ScalarReferenceNativeDetectionCoordinateEquiv
import OAI.Combinatorics.Progressions.Probability.AllocatedEmptyLayerLaw

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    [∀ j, IsEmpty (I j)] [∀ j, IsEmpty (J j)]
    {n : Fin m → ℕ} [∀ j, IsEmpty (Fin (n j))]
    {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

namespace AllocatedExternalCandidateSampler
variable (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ
  N poly hm τ ξ (fun _ : X => 1) {0} center)

omit [∀ j, IsEmpty (J j)]
  [∀ j, IsZLattice ℝ
    (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in
include A in
theorem scalarWidths_pos_empty_layers :
    ∀ z : Option (LayerSamplerVariables G I n B) × X,
      0 < trimmedSpatialWidths ((Fintype.card G : ℝ) * S.value) τ N z := by
  simpa only [allocatedExternalCandidateWidths_empty_layers] using A.widths_pos

omit [∀ j, IsEmpty (J j)]
  [∀ j, IsZLattice ℝ
    (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in
include A in
theorem scalarMass_pos_empty_layers :
    0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0}
      (trimmedSpatialWidths (K := LayerSamplerVariables G I n B)
        ((Fintype.card G : ℝ) * S.value) τ N) z := by
  simpa only [allocatedExternalCandidateWidths_empty_layers] using A.smooth_mass_pos

theorem nativeDetection_iff_scalarReference_empty_layers
    (hW : ∀ z : Option (LayerSamplerVariables G I n B) × X,
      0 < trimmedSpatialWidths ((Fintype.card G : ℝ) * S.value) τ N z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0}
      (trimmedSpatialWidths (K := LayerSamplerVariables G I n B)
        ((Fintype.card G : ℝ) * S.value) τ N) z)
    (degree : ℕ) (pSlice pTest pNative α : ℝ) :
    A.NativeDetection degree pSlice pTest pNative α ↔
    ScalarReferenceNativeDetection (degree := degree) J N A.integerBox_nonempty poly
      S.value ((Fintype.card G : ℝ) * S.value) τ A.bases_nonempty
      hW hZ pSlice pTest pNative α := by
  unfold NativeDetection ScalarReferenceNativeDetection OrdinarySliceNativeDetection
  simp only [law_empty_layers]
  unfold physical Path Site sides
  generalize_proofs hbox hbase hpos hmass
  revert hW hZ hpos hmass
  rw [allocatedExternalCandidateSides_empty_layers_fun,
    allocatedExternalCandidateWidths_empty_layers]
  intros
  rfl

omit [∀ j, IsEmpty (I j)] [∀ j, IsEmpty (J j)] [∀ j, IsEmpty (Fin (n j))]
  [∀ j, IsZLattice ℝ
    (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in
include A in
theorem scalarAxesWidths_pos_empty_layers :
    ∀ z : Option G × X,
      0 < trimmedSpatialWidths ((Fintype.card G : ℝ) * S.value) τ N z :=
  trimmedSpatialWidths_pos (by positivity) A.trim_pos N A.size_pos

omit [∀ j, IsEmpty (J j)]
  [∀ j, IsZLattice ℝ
    (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in
include A in
theorem scalarAxesMass_pos_empty_layers :
    0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0}
      (trimmedSpatialWidths (K := G) ((Fintype.card G : ℝ) * S.value) τ N) z := by
  rw [selectedResidueSmoothMass_scalarCoordinateEquiv (emptyLayerVariablesEquiv B)
    ((Fintype.card G : ℝ) * S.value) τ N]
  exact A.scalarMass_pos_empty_layers

theorem nativeDetection_to_scalarAxes_empty_layers
    (degree : ℕ) (pSlice pTest pNative α : ℝ)
    (h : A.NativeDetection degree pSlice pTest pNative α) :
    ScalarReferenceNativeDetection (degree := degree) J N A.integerBox_nonempty poly
      S.value ((Fintype.card G : ℝ) * S.value) τ A.bases_nonempty
      A.scalarAxesWidths_pos_empty_layers A.scalarAxesMass_pos_empty_layers
      pSlice pTest pNative α := by
  have hlocal : ScalarReferenceNativeDetection (degree := degree) J N A.integerBox_nonempty poly
      S.value ((Fintype.card G : ℝ) * S.value) τ A.bases_nonempty
      A.scalarWidths_pos_empty_layers A.scalarMass_pos_empty_layers
      pSlice pTest pNative α := (A.nativeDetection_iff_scalarReference_empty_layers
    A.scalarWidths_pos_empty_layers A.scalarMass_pos_empty_layers
    degree pSlice pTest pNative α).mp h
  exact @ScalarReferenceNativeDetection.coordinateReturn m degree X G
    (LayerSamplerVariables G I n B) inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance J inferInstance
    N A.integerBox_nonempty poly
    (emptyLayerVariablesEquiv (G := G) B).symm S.value ((Fintype.card G : ℝ) * S.value) τ
    A.bases_nonempty A.scalarAxesWidths_pos_empty_layers A.scalarWidths_pos_empty_layers
    A.scalarAxesMass_pos_empty_layers A.scalarMass_pos_empty_layers pSlice pTest pNative α (@hlocal)

theorem nativeDetection_from_scalarAxes_empty_layers
    (degree : ℕ) (pSlice pTest pNative α : ℝ)
    (h : ScalarReferenceNativeDetection (degree := degree) J N A.integerBox_nonempty poly
      S.value ((Fintype.card G : ℝ) * S.value) τ A.bases_nonempty
      A.scalarAxesWidths_pos_empty_layers A.scalarAxesMass_pos_empty_layers
      pSlice pTest pNative α) :
    A.NativeDetection degree pSlice pTest pNative α := by
  apply (A.nativeDetection_iff_scalarReference_empty_layers
    A.scalarWidths_pos_empty_layers A.scalarMass_pos_empty_layers
    degree pSlice pTest pNative α).mpr
  exact @ScalarReferenceNativeDetection.coordinateReturn m degree X
    (LayerSamplerVariables G I n B) G inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance J inferInstance
    N A.integerBox_nonempty poly
    (emptyLayerVariablesEquiv (G := G) B) S.value ((Fintype.card G : ℝ) * S.value) τ
    A.bases_nonempty A.scalarWidths_pos_empty_layers A.scalarAxesWidths_pos_empty_layers
    A.scalarMass_pos_empty_layers A.scalarAxesMass_pos_empty_layers pSlice pTest pNative α (@h)

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel
open scoped Classical BigOperators NNReal TensorProduct

variable {G X : Type} [Fintype G] [Fintype X]
    {I J : Fin 0 → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin 0 → ℕ} {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin 0 → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

namespace AllocatedExternalCandidateSampler
variable (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ
  N poly hm τ ξ (fun _ : X => 1) {0} center)

omit [∀ j, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in
include A in
theorem scalarAxesMass_pos_zero_layers :
    0 < ∑' z, selectedResidueSmoothWeight (fun _ : X => 1) {0}
      (trimmedSpatialWidths (K := G) ((Fintype.card G : ℝ) * S.value) τ N) z := by
  let : ∀ j, IsEmpty (I j) := fun j => Fin.elim0 j
  let : ∀ j, IsEmpty (Fin (n j)) := fun j => Fin.elim0 j
  exact A.scalarAxesMass_pos_empty_layers

theorem nativeDetection_of_emptyTag_scalarReference
    {q : ℕ} (Jsource : Fin q → Type) [∀ j, Fintype (Jsource j)]
    [IsEmpty (Σ j, Jsource j)]
    (sourcePoly : ∀ j, VectorPolynomial X ℝ (Jsource j → ℝ))
    (degree : ℕ) (pSlice pTest pNative α : ℝ)
    (hsource : ScalarReferenceNativeDetection (degree := degree) Jsource N
      A.integerBox_nonempty sourcePoly S.value ((Fintype.card G : ℝ) * S.value) τ
      A.bases_nonempty A.scalarAxesWidths_pos_empty_layers A.scalarAxesMass_pos_zero_layers
      pSlice pTest pNative α) :
    A.NativeDetection degree pSlice pTest pNative α := by
  let : ∀ j, IsEmpty (I j) := fun j => Fin.elim0 j
  let : ∀ j, IsEmpty (J j) := fun j => Fin.elim0 j
  let : ∀ j, IsEmpty (Fin (n j)) := fun j => Fin.elim0 j
  have hscalar : ScalarReferenceNativeDetection (degree := degree) J N A.integerBox_nonempty poly
      S.value ((Fintype.card G : ℝ) * S.value) τ A.bases_nonempty
      A.scalarAxesWidths_pos_empty_layers A.scalarAxesMass_pos_empty_layers
      pSlice pTest pNative α :=
    @ScalarReferenceNativeDetection.retag_of_isEmpty q 0 degree X G
      inferInstance inferInstance inferInstance inferInstance
      Jsource inferInstance inferInstance J inferInstance N A.integerBox_nonempty
      sourcePoly poly S.value ((Fintype.card G : ℝ) * S.value) τ A.bases_nonempty
      A.scalarAxesWidths_pos_empty_layers A.scalarAxesMass_pos_zero_layers
      pSlice pTest pNative α (@hsource)
  apply (A.nativeDetection_iff_scalarReference_empty_layers
    A.scalarWidths_pos_empty_layers A.scalarMass_pos_empty_layers
    degree pSlice pTest pNative α).mpr
  exact @ScalarReferenceNativeDetection.coordinateReturn 0 degree X
    (LayerSamplerVariables G I n B) G inferInstance inferInstance
    inferInstance inferInstance inferInstance inferInstance J inferInstance
    N A.integerBox_nonempty poly
    (emptyLayerVariablesEquiv (G := G) B) S.value ((Fintype.card G : ℝ) * S.value) τ
    A.bases_nonempty A.scalarWidths_pos_empty_layers A.scalarAxesWidths_pos_empty_layers
    A.scalarMass_pos_empty_layers A.scalarAxesMass_pos_empty_layers pSlice pTest pNative α (@hscalar)

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI
