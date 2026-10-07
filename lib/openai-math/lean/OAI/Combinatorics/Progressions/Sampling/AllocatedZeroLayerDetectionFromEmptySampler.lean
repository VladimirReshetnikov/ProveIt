import OAI.Combinatorics.Progressions.Estimates.AllocatedZeroLayerDetectorReturn

namespace OAI

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

theorem nativeDetection_of_emptyLayer_sampler
    {q : ℕ} {I' J' : Fin q → Type}
    [∀ j, Fintype (I' j)] [∀ j, Fintype (J' j)]
    [∀ j, IsEmpty (I' j)] [∀ j, IsEmpty (J' j)]
    {n' : Fin q → ℕ} [∀ j, IsEmpty (Fin (n' j))]
    {B' : LayerSamplerAxis I' n' → Type} [∀ a, Fintype (B' a)]
    {U' : ∀ j, Submodule ℝ (J' j → ℝ)}
    {b' : ∀ j, Basis (Fin (n' j)) ℝ (euclideanSubspace (U' j))ᗮ}
    {R' σ' : Fin q → ℝ} {S' : LayerSamplerScale (G := G) B' U' b' R' σ'}
    {hb' : ∀ j, span ℤ (Set.range (b' j)) = projectedIntegerLattice (euclideanSubspace (U' j))}
    {o' : ∀ j, OrthonormalBasis (I' j) ℝ (euclideanSubspace (U' j))}
    {hR' : ∀ j, 0 < R' j} {hσ' : ∀ j, 0 < σ' j}
    {poly' : ∀ j, VectorPolynomial X ℝ (J' j → ℝ)}
    {hm' : ∀ j e, coefficients (poly' j) e ∈ U' j}
    {ξ' : ℝ} {center' : CoefficientTorus (K := LayerSamplerVariables G I' n' B') U'}
    [∀ j, IsZLattice ℝ
      (latticeSection (standardEuclideanLattice (J' j)) (euclideanSubspace (U' j)))]
    (Asource : AllocatedExternalCandidateSampler B' U' b' S' hb' o' hR' hσ'
      N poly' hm' τ ξ' (fun _ : X => 1) {0} center')
    (hvalue : S'.value = S.value)
    (degree : ℕ) (pSlice pTest pNative α : ℝ)
    (hsource : Asource.NativeDetection degree pSlice pTest pNative α) :
    A.NativeDetection degree pSlice pTest pNative α := by
  have hscalarSource : ScalarReferenceNativeDetection (degree := degree) J' N
      Asource.integerBox_nonempty poly' S'.value ((Fintype.card G : ℝ) * S'.value) τ
      Asource.bases_nonempty Asource.scalarAxesWidths_pos_empty_layers
      Asource.scalarAxesMass_pos_empty_layers pSlice pTest pNative α :=
    @nativeDetection_to_scalarAxes_empty_layers q G X inferInstance inferInstance
      I' J' inferInstance inferInstance inferInstance inferInstance n' inferInstance
      B' inferInstance U' b' R' σ' S' hb' o' hR' hσ' N poly' hm' τ ξ' center'
      inferInstance Asource degree pSlice pTest pNative α (@hsource)
  have heq :
      ScalarReferenceNativeDetection (degree := degree) J' N
        Asource.integerBox_nonempty poly' S'.value ((Fintype.card G : ℝ) * S'.value) τ
        Asource.bases_nonempty Asource.scalarAxesWidths_pos_empty_layers
        Asource.scalarAxesMass_pos_empty_layers pSlice pTest pNative α =
      ScalarReferenceNativeDetection (degree := degree) J' N
        A.integerBox_nonempty poly' S.value ((Fintype.card G : ℝ) * S.value) τ
        A.bases_nonempty A.scalarAxesWidths_pos_empty_layers A.scalarAxesMass_pos_zero_layers
        pSlice pTest pNative α := by
    simp only [hvalue]
  let : IsEmpty (Σ j, J' j) := ⟨fun x => isEmptyElim x.2⟩
  exact @nativeDetection_of_emptyTag_scalarReference G X inferInstance inferInstance
    I J inferInstance inferInstance n B inferInstance U b R σ S hb o hR hσ N poly hm
    τ ξ center inferInstance A q J' inferInstance inferInstance poly'
    degree pSlice pTest pNative α (@Eq.mp _ _ heq (@hscalarSource))

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI
