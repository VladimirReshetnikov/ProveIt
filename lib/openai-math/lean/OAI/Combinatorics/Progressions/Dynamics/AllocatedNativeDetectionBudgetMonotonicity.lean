import OAI.Combinatorics.Progressions.Estimates.AllocatedZeroLayerFixedCenterExcess

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped TensorProduct NNReal

theorem SampledSliceNativeDetection.mono_native
    {m : ℕ} {X Ω T : Type} [Fintype X] [DecidableEq X] [Fintype Ω] [Fintype T]
    {Tests : Ω → Type} {J : Fin m → Type} [∀ j, Fintype (J j)]
    {N : X → ℕ} {hbox : (integerBox N).Nonempty}
    {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {pathLaw : FiniteProbabilityWeights Ω} {physical : Ω → T → X → ℤ}
    {slices : ∀ z, Tests z → Finset T} {weight : ∀ z, Tests z → T → ℂ}
    {degree : ℕ} {pNative pNative' α : ℝ}
    (h : SampledSliceNativeDetection J N hbox poly pathLaw physical slices weight
      degree pNative α)
    (hpNative : pNative ≤ pNative') :
    SampledSliceNativeDetection J N hbox poly pathLaw physical slices weight
      degree pNative' α := by
  intro signal hsignal hsupp hlarge
  obtain ⟨W, g, ⟨model⟩, hcorr⟩ := h signal hsignal hsupp hlarge
  have hexp := Real.exp_le_exp.mpr hpNative
  have hLip : (⟨Real.exp pNative, Real.exp_nonneg _⟩ : ℝ≥0) ≤
      ⟨Real.exp pNative', Real.exp_nonneg _⟩ := hexp
  refine ⟨W.mono hexp hexp hLip, g, ⟨model.mono hpNative⟩, ?_⟩
  change Real.exp (-pNative') ≤
    ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).correlation
      (fun u => signal u.val) (fun u => star (W.eval N poly u.val) * g u)‖
  exact (Real.exp_le_exp.mpr (neg_le_neg hpNative)).trans hcorr

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X] [DecidableEq X]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

namespace AllocatedExternalCandidateSampler

variable {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

theorem NativeDetection.mono_native
    {degree : ℕ} {pSlice pTest pNative pNative' α : ℝ}
    (h : A.NativeDetection degree pSlice pTest pNative α)
    (hpNative : pNative ≤ pNative') :
    A.NativeDetection degree pSlice pTest pNative' α := by
  intro Tests _ Ldetect _ _ dims _ _ _ _ Ddetect Vdetect slices origin step length
    hstep hshape hdense hcomplex hnorm
  exact (h Ddetect Vdetect slices origin step length hstep hshape hdense hcomplex hnorm).mono_native
    hpNative

end AllocatedExternalCandidateSampler
end Erdos3.VectorPolynomial

end

end OAI
