import OAI.Combinatorics.Progressions.Probability.AllocatedProfileErrorSampledMass

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory Module Submodule VectorPolynomial
open scoped BigOperators Classical NNReal

theorem exists_allocated_weighted_profile_error (m q : ℕ) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ {X : Type*} [Fintype X] [DecidableEq X]
    {Ksp : Type*} [Fintype Ksp]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (Fin q) × X) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := Fin q) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin q) U)] [BorelSpace (CoefficientTorus (K := Fin q) U)]
    (μ : Measure (CoefficientTorus (K := Fin q) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    (d : ℕ) [NeZero d]
    (stride : X → ℕ) (_hs : ∀ x, 0 < stride x)
    {R S₀ ρ ε : ℝ} (_hS : 0 ≤ S₀) (_hSP : S₀ ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ x, (stride x : ℝ) ≤ S₀)
    (N : X → ℝ) (_hsize : ∀ x, Real.exp ((P + K) ^ K) ≤ N x)
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) N R (U j) (p j))
    (_hR : Real.exp ((P + K) ^ K) ≤ R)
    (root : Ksp → ℤ) (D : Matrix (Fin q) Ksp ℤ) (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option Ksp) X stride))
    (W₀ : Option Ksp × X → ℝ) (_hW₀ : ∀ z, 0 < W₀ z)
    (_hZ₀ : 0 < ∑' z, selectedResidueSmoothWeight stride cells W₀ z)
    (H T : X → ℝ) (_hH : ∀ x, 0 < H x) (_hT : ∀ x, 0 < T x)
    {Wsp Lsp : ℝ} (_hLsp : 0 < Lsp) (_hsc : ∀ x, H x = (1 + Wsp) * T x)
    (_hrows : ∀ x i, (∑ k, |(physicalCubeCoefficient root D i k : ℝ)|) ≤ H x)
    (_hwidth : ∀ x, ρ * N x ≤ 20 * (stride x : ℝ) * H x)
    (_hprofile : ∀ x, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H x)
    (ψ : (X → (Unit ⊕ Fin q) → ℤ) → ℂ) {Cψ : ℝ} (_hCψ : 0 ≤ Cψ)
    (_hψ : ∀ w ∈ spatialWindow H 4, ‖ψ w‖ ≤ Cψ)
    (test : (X → (Unit ⊕ Fin q) → ℤ) → ℂ) (_htest : ∀ w, ‖test w‖ ≤ 1)
    {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R₀ σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R₀ σ)
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR₀ : ∀ j, 0 < R₀ j) (hσ : ∀ j, 0 < σ j)
    {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
    (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
      (allocatedPrincipalSides B U b S))
    (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
      (allocatedPrincipalSides B U b S))
    (rows : ∀ j : Fin m, BoundedBooleanJet (Fin q) (j.val + 1) → Finset α)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (period : ℕ) [NeZero period]
    (_hperiod : ∀ j, integerScalarLattice (BoundedBooleanJet (Fin q) (j.val + 1)) (period : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (modulus : ℕ)
    (residue : ∀ j : Fin m, Matrix (BoundedBooleanJet (Fin q) (j.val + 1))
      (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (Cm : ℝ≥0) (_hCm : 1 ≤ (Cm : ℝ))
    (_hmasks : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x rows j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U b S x rows j modulus (residue j) z ≤ Cm)
    (f g : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
      BoundedBooleanJet (Fin q) ((Sigma.fst (Subtype.val a)).val + 1)) → ℝ) → ℝ)
    {Cf Cg Kf Kg : ℝ≥0} (_hf : LipschitzWith Kf f) (_hg : LipschitzWith Kg g)
    (_hfb : ∀ z, |f z| ≤ Cf) (_hgb : ∀ z, |g z| ≤ Cg)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    {δ L : ℝ} (_hδ : 0 < δ) (_hL : 0 ≤ L)
    (_hamb : (Fintype.card (JetAmbientIndex (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) J) : ℝ) ≤ L)
    (_hδL : δ⁻¹ ≤ Real.exp L),
    let O := fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)
    let A := Real.toNNReal (coefficientDeckPeriodCap O Q period) * Cm ^ Fintype.card (LayerSamplerAxis I n)
    (allocatedProfileErrorLip B U b S (O := O) A Cf Cg Kf Kg C V : ℝ) ≤ Real.exp L →
    Real.exp ((2 * L + 2) ^ 4) ≤ Real.exp P →
    Real.exp (2 * L * (2 * L + 2) ^ 4) * allocatedProfileErrorCap B U b S (O := O) A Cf Cg V ≤ Real.exp P →
    Integrable (allocatedUnmaskedLongProfileDensity B U b S (fun v => |f v - g v|))
      (allocatedLongJetReference B U b S O) →
    ∀ M : ℝ,
    (A : ℝ) * (∫ z, allocatedUnmaskedLongProfileDensity B U b S (fun v => |f v - g v|) z
      ∂allocatedLongJetReference B U b S O) ≤ M →
    let covered := fun profile => allocatedCoveredProfileDensity B U b hR₀ hσ S x u v rows hb o bW d
      (fun j _ => standardLatticeClosedQuarterBox (J j))
      (allocatedLongProfileDensity B U b S x rows modulus residue profile)
    let error := fun y => |covered f y - covered g y|
    let volumeFactor := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin q) × X) *
      (((1 + Wsp) / Lsp) ^ q) ^ Fintype.card X
    let scale := ∏ x, ∏ i, physicalSpatialOutputScale (Fin q) (H x) (T x) Lsp i
    let window := spatialWindow H 4
    let reconstruct := fun a : cells => physicalResidueReconstruction root D base
      (boundedColumnResidueRepresentative stride a.val) stride
    (∑ t : cells × window,
      ‖(selectedResidueCellWeight stride cells W₀ t.1 : ℂ) * (ψ t.2.val / (scale : ℂ)) *
        test (reconstruct t.1 t.2.val)‖ *
          error (physicalCubeEuclideanSample U d p hm (reconstruct t.1 t.2.val))) ≤
      Cψ * (volumeFactor * (M + 2 * δ + ε)) := by
  obtain ⟨K, hK, hsample⟩ := exists_allocated_profile_error_sampled_mass m q
  refine ⟨K, hK, ?_⟩
  intro X _ _ Ksp _ J _ P hP hn hdim U _ _ _ μ _ _ ν _ _ p hp hm d _ stride hs R S₀ ρ ε
    hS hSP hρ hε hρP hεP hstride N hsize hrank hR root D base cells W₀ hW₀ hZ₀
    H T hH hT Wsp Lsp hLsp hsc hrows hwidth hprofile ψ Cψ hCψ hψ test htest
    G _ I _ n B _ b R₀ σ S o hR₀ hσ α _ x u v rows _ hb Q _ bW period _ hperiod
    modulus residue Cm hCm hmasks f g Cf Cg Kf Kg hf hg hfb hgb C V hC hV δ L hδ hL hamb hδL
    O A hLip hfreqP hcoeffP hi M hMass covered error volumeFactor scale window reconstruct
  let majorant := allocatedProfileErrorMajorant B U b S o hR₀ hσ x u v rows A f g d
  let p₀ := fun j => translate (fun x => (base x : ℝ)) (p j)
  have hp₀ (j) : DegreeLE (1 : X → ℕ) (j.val + 1) (p₀ j) :=
    degreeLE_translate (1 : X → ℕ) (fun _ => by norm_num) _ (p j) (hp j)
  have hm₀ (j e) : coefficients (p₀ j) e ∈ U j :=
    coefficients_translate_mem (U j) (fun x => (base x : ℝ)) (p j) (hm j) e
  have hrank₀ (j) : HasLayerSamplingRank (j.val + 1) N R (U j) (p₀ j) :=
    (hasLayerSamplingRank_translate_iff _ _ N R (U j) (p j) (hp j)).mpr (hrank j)
  let V₁ := referenceJetEnvelopeWidths (q := q) stride H
  have hV₁ := referenceJetEnvelopeWidths_pos (q := q) stride hs H hH
  have hg0 (y) : 0 ≤ majorant y :=
    ((allocatedProfileErrorTorusKernel_bounds B U b S o hR₀ hσ x u v rows A f g hf hg hfb hgb C V hC hV).1
      (coveredJetAmbientTorus U d y)).1
  have hscale : 0 < scale := Finset.prod_pos (fun x _ => Finset.prod_pos (fun i _ =>
    physicalSpatialOutputScale_pos (Fin q) (hH x) (hT x) hLsp i))
  have hmass (a : cells) :
      (∑ w ∈ window, majorant (physicalCubeEuclideanSample U d p hm (reconstruct a w))) ≤
        (volumeFactor * (M + 2 * δ + ε)) * scale := by
    let r := boundedColumnResidueRepresentative stride a.val
    let target := columnResiduePattern stride
      (standardPhysicalCubeFrame (physicalCubeRootDifferences root D 0 r))
    obtain ⟨hZ, hmean, _⟩ := hsample hP hn hdim U μ ν p₀ hp₀ hm₀ d stride hs
      hS hSP hρ hε hρP hεP hstride N hsize hrank₀ hR
      {target} (Finset.singleton_nonempty _) V₁ hV₁ (fun z => hwidth z.2)
      B b S o hR₀ hσ x u v rows hb bW A f g hf hg hfb hgb C V hC hV hδ hL hamb hδL
      hLip hfreqP hcoeffP hi M hMass
    let sampleTest := fun w => majorant (physicalCubeEuclideanSample U d p₀ hm₀ w)
    have hraw := physicalReconstruction_sum_le_sampled_mass stride hs root D a.val
      H hH hrows hprofile sampleTest (fun _ => hg0 _) hZ
    have hvol : ((3 / 2 : ℝ) ^ Fintype.card (Option (Fin q) × X) *
        (∏ i, residueProfileWidth stride V₁ i) /
        (smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin q) × X)) = volumeFactor * scale :=
      referenceJetEnvelope_anisotropic_volume stride hs H T hLsp.ne' hsc
    have hvol0 : 0 ≤ (3 / 2 : ℝ) ^ Fintype.card (Option (Fin q) × X) *
        (∏ i, residueProfileWidth stride V₁ i) /
        (smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin q) × X) := by
      exact div_nonneg (mul_nonneg (pow_nonneg (by norm_num) _)
        (Finset.prod_nonneg (fun i _ => (residueProfileWidth_pos stride V₁ hs hV₁ i).le)))
        (pow_pos smoothProbabilityProfile_pos_zero _).le
    have hfinal := hraw.trans (mul_le_mul_of_nonneg_left hmean hvol0)
    rw [hvol] at hfinal
    dsimp only [sampleTest, p₀] at hfinal
    simp_rw [physicalCubeEuclideanSample_translate U d p hm base,
      ← physicalResidueReconstruction_translate root D base] at hfinal
    change (∑ w ∈ window, majorant (physicalCubeEuclideanSample U d p hm (reconstruct a w))) ≤
      (volumeFactor * scale) * (M + 2 * δ + ε) at hfinal
    exact hfinal.trans_eq (by ring)
  have hdom (y) : error y ≤ majorant y :=
    allocatedProfileDifference_le_period_majorant B U b S o hR₀ hσ x u v rows hb bW d
      period hperiod modulus residue Cm hCm hmasks f g y
  calc
    _ ≤ ∑ t : cells × window,
        ‖(selectedResidueCellWeight stride cells W₀ t.1 : ℂ) * (ψ t.2.val / (scale : ℂ)) *
          test (reconstruct t.1 t.2.val)‖ *
            majorant (physicalCubeEuclideanSample U d p hm (reconstruct t.1 t.2.val)) :=
      Finset.sum_le_sum (fun t _ => mul_le_mul_of_nonneg_left (hdom _) (norm_nonneg _))
    _ ≤ _ := selectedResidue_coefficient_tail_of_window_mass stride cells W₀ hW₀ hZ₀ window ψ
      (fun a w => test (reconstruct a w))
      (fun a w => majorant (physicalCubeEuclideanSample U d p hm (reconstruct a w)))
      hscale hCψ hψ (fun a w => htest _) (fun a w => hg0 _) hmass

end Erdos3.BooleanCubeKernel

end

end OAI
