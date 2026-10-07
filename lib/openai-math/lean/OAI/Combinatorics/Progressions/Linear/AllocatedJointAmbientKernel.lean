import OAI.Combinatorics.Progressions.Estimates.AllocatedAmbientLogBounds

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators NNReal

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
variable (f : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → ℝ → ℝ)

noncomputable def coefficientJointAmbientKernel (v : CoefficientAmbientIndex K J → ℝ) : ℝ :=
  ∏ s : CoefficientSlot K m,
    canonicalAmbientKernel (euclideanSubspace (U s.1)) (b s.1) (o s.1)
      (fun i => c s.1 i s.2) (fun i => w s.1 i s.2) (fun i => f s.1 i s.2)
      (fun i => v ⟨s,i⟩)

theorem coefficientJointAmbientKernel_support (v : CoefficientAmbientIndex K J → ℝ)
    (hv : coefficientJointAmbientKernel U b o c w f v ≠ 0) :
    ∀ i, |v i| < 1/2 := by
  rintro ⟨s,i⟩
  exact canonicalAmbientKernel_support _ _ _ _ _ _ _
    ((Finset.prod_ne_zero_iff.mp hv) s (Finset.mem_univ s)) i

theorem coefficientJointAmbientKernel_bounds {B L : ℝ≥0} (hB : 1 ≤ B)
    (hcap : ∀ (s : CoefficientSlot K m) x,
      0 ≤ canonicalAmbientKernel (euclideanSubspace (U s.1)) (b s.1) (o s.1)
        (fun i => c s.1 i s.2) (fun i => w s.1 i s.2) (fun i => f s.1 i s.2) x ∧
      canonicalAmbientKernel (euclideanSubspace (U s.1)) (b s.1) (o s.1)
        (fun i => c s.1 i s.2) (fun i => w s.1 i s.2) (fun i => f s.1 i s.2) x ≤ B)
    (hlip : ∀ s : CoefficientSlot K m, LipschitzWith L
      (canonicalAmbientKernel (euclideanSubspace (U s.1)) (b s.1) (o s.1)
        (fun i => c s.1 i s.2) (fun i => w s.1 i s.2) (fun i => f s.1 i s.2))) :
    (∀ x, 0 ≤ coefficientJointAmbientKernel U b o c w f x ∧
      coefficientJointAmbientKernel U b o c w f x ≤ (B : ℝ)^Fintype.card (CoefficientSlot K m)) ∧
    LipschitzWith (Fintype.card (CoefficientSlot K m) * L * B^Fintype.card (CoefficientSlot K m))
      (coefficientJointAmbientKernel U b o c w f) := by
  let H := fun (s : CoefficientSlot K m) (x : CoefficientAmbientIndex K J → ℝ) =>
    canonicalAmbientKernel (euclideanSubspace (U s.1)) (b s.1) (o s.1)
      (fun i => c s.1 i s.2) (fun i => w s.1 i s.2) (fun i => f s.1 i s.2)
      (fun i => x ⟨s,i⟩)
  have hL : ∀ s, LipschitzWith L (H s) := by
    intro s
    apply LipschitzWith.of_dist_le_mul
    intro x y
    refine ((hlip s).dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left ?_ L.coe_nonneg)
    apply (dist_pi_le_iff dist_nonneg).mpr
    intro i
    exact dist_le_pi_dist x y ⟨s,i⟩
  obtain ⟨hbnd, hprod⟩ := bounded_lipschitz_real_prod H hB hL
    (fun s x => by rw [abs_of_nonneg (hcap s _).1]; exact (hcap s _).2)
  refine ⟨?_, hprod⟩
  intro x
  have h0 : 0 ≤ coefficientJointAmbientKernel U b o c w f x :=
    Finset.prod_nonneg (fun s _ => (hcap s _).1)
  exact ⟨h0, (le_abs_self _).trans (hbnd x)⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule
open scoped BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

noncomputable def allocatedCoefficientJointAmbientKernel
    (x : CoefficientAmbientIndex (LayerSamplerVariables G I n B) J → ℝ) : ℝ :=
  coefficientJointAmbientKernel U b o (allocatedLayerCenters B U b S)
    (allocatedLayerWidths B U b S) (allocatedLayerIntegerInterpolation B U b S) x

include hC hV in
theorem allocatedAmbientKernelFactor_bounds (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (s : CoefficientSlot (LayerSamplerVariables G I n B) m) :
    (∀ x, 0 ≤ canonicalAmbientKernel (euclideanSubspace (U s.1)) (b s.1) (o s.1)
        (fun i => allocatedLayerCenters B U b S s.1 i s.2)
        (fun i => allocatedLayerWidths B U b S s.1 i s.2)
        (fun i => allocatedLayerIntegerInterpolation B U b S s.1 i s.2) x ∧
      canonicalAmbientKernel (euclideanSubspace (U s.1)) (b s.1) (o s.1)
        (fun i => allocatedLayerCenters B U b S s.1 i s.2)
        (fun i => allocatedLayerWidths B U b S s.1 i s.2)
        (fun i => allocatedLayerIntegerInterpolation B U b S s.1 i s.2) x ≤
          allocatedAmbientFactorCap (G := G) B R σ S.value V) ∧
    LipschitzWith (allocatedAmbientFactorLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V)
      (canonicalAmbientKernel (euclideanSubspace (U s.1)) (b s.1) (o s.1)
        (fun i => allocatedLayerCenters B U b S s.1 i s.2)
        (fun i => allocatedLayerWidths B U b S s.1 i s.2)
        (fun i => allocatedLayerIntegerInterpolation B U b S s.1 i s.2)) := by
  obtain ⟨hcap, hlip⟩ := allocatedLayerMixedInterpolation_bounds B U b S hR hσ s.1 s.2
  obtain ⟨ha, hl⟩ := canonicalAmbientKernel_bounds (euclideanSubspace (U s.1)) (b s.1) (o s.1)
    _ _ _ hcap hlip (hC s.1) (hV s.1)
  have hcaple : V s.1 * allocatedLayerMixedCap (G := G) B R σ S.value s.1 ≤
      allocatedAmbientFactorCap (G := G) B R σ S.value V := by
    apply le_trans (Finset.single_le_sum
      (f := fun j => V j * allocatedLayerMixedCap (G := G) B R σ S.value j)
      (fun _ _ => zero_le) (Finset.mem_univ s.1))
    exact le_add_of_nonneg_left (by norm_num)
  have hliple : allocatedAmbientLayerLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V s.1 ≤
      allocatedAmbientFactorLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V := by
    unfold allocatedAmbientFactorLip
    exact Finset.single_le_sum
      (f := fun j => allocatedAmbientLayerLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V j)
      (fun _ _ => zero_le) (Finset.mem_univ s.1)
  refine ⟨fun x => ⟨(ha x).1, (ha x).2.trans ?_⟩, hl.weaken hliple⟩
  exact_mod_cast hcaple

include hC hV in
theorem allocatedCoefficientJointAmbientKernel_bounds
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) :
    let A := allocatedAmbientFactorCap (G := G) B R σ S.value V
    let L := allocatedAmbientFactorLip (G := G) B R σ S.value (fun j => Fintype.card (J j)) C V
    let N := Fintype.card (CoefficientSlot (LayerSamplerVariables G I n B) m)
    (∀ x, 0 ≤ allocatedCoefficientJointAmbientKernel B U b S o x ∧
      allocatedCoefficientJointAmbientKernel B U b S o x ≤ (A : ℝ)^N) ∧
    LipschitzWith (N * L * A^N) (allocatedCoefficientJointAmbientKernel B U b S o) := by
  have h := allocatedAmbientKernelFactor_bounds B U b S o C V hC hV hR hσ
  exact coefficientJointAmbientKernel_bounds U b o _ _ _
    (allocatedAmbientFactorCap_one_le (G := G) B R σ S.value V)
    (fun s x => (h s).1 x) (fun s => (h s).2)

theorem allocatedCoefficientJointAmbientKernel_support
    (x : CoefficientAmbientIndex (LayerSamplerVariables G I n B) J → ℝ)
    (hx : allocatedCoefficientJointAmbientKernel B U b S o x ≠ 0) :
    ∀ i, |x i| < 1/2 := coefficientJointAmbientKernel_support U b o _ _ _ x hx

end Erdos3.VectorPolynomial

end

end OAI
