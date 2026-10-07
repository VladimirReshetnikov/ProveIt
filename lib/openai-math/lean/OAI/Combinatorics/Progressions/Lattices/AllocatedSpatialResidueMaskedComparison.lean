import OAI.Combinatorics.Progressions.Probability.AllocatedJointMaskedDensityComparison

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type} [Fintype G] {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

include hC hV in

theorem exists_allocated_spatial_residue_masked_comparison
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    (q : ℕ) (hq : 0 < q)
    {P δ : ℝ} (hP : 0 ≤ P) (hmP : (m : ℝ) ≤ P)
    (hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ) ≤ P)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (hn : ∀ j, (n j : ℝ) ≤ P)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (hLP : (S.value : ℝ) ≤ Real.exp P)
    (hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    (hqP : (q : ℝ) ≤ Real.exp P) (hδ : 0 < δ) (hδP : δ⁻¹ ≤ Real.exp P)
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
    (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
    [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    {X : Type} [Fintype X] [DecidableEq X]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (hm : ∀ j e, coefficients (poly j) e ∈ U j)
    {Ps ε ρ Rs Smax : ℝ} (hPs : 0 ≤ Ps) (hX : (Fintype.card X : ℝ) ≤ Ps)
    (hframe : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ Ps)
    (hqPs : (q : ℝ) ≤ Real.exp Ps)
    (hε : 0 < ε) (hρ : 0 < ρ) (hεPs : 1 / ε ≤ Real.exp Ps) (hρPs : 1 / ρ ≤ Real.exp Ps)
    (stride : X → ℕ) (hstride : ∀ x, 0 < stride x)
    (hSmax : 0 ≤ Smax) (hSmaxPs : Smax ≤ Real.exp Ps) (hstrideMax : ∀ x, ((stride x * q : ℕ) : ℝ) ≤ Smax)
    (H : X → ℝ)
    (hsize : ∀ x, Real.exp ((Ps + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ H x)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H Rs (U j) (poly j))
    (hRs : Real.exp ((Ps + allocatedMaskedTiltedConstant m) ^ allocatedMaskedTiltedConstant m) ≤ Rs)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
    (hcells : cells.Nonempty)
    (mask : ((Option (LayerSamplerVariables G I n B) × X) → ZMod q) →
      (CoefficientAmbientIndex (LayerSamplerVariables G I n B) J → ZMod q) → ℝ)
    (hmask : ∀ r z, mask r z ∈ Set.Icc (0 : ℝ) 1)
    (width : Option (LayerSamplerVariables G I n B) × X → ℝ) (hwidth : ∀ z, 0 < width z)
    (hwide : ∀ z, ρ * H z.2 ≤ width z)
    (hfreqPs : (4 * allocatedFourierLogBudget m P + 2)^4 ≤ Ps)
    (hmassPs : 4 * allocatedFourierLogBudget m P * (4 * allocatedFourierLogBudget m P + 2)^4 +
      allocatedFourierLogBudget m P ≤ Ps)
    (hsmallError : 2 * δ + ε ≤ 1 / 2) :
    let D := allocatedCoefficientDensity B U b hb o hR hσ S
    let Dc := fun x => D (quotientIntegerCover (coefficientIntegerLattice U) q x)
    let A := fun r => allocatedMaskedCoefficientDensity B U b o S q (mask r)
    let sample := fun z : Option (LayerSamplerVariables G I n B) × X → ℤ =>
      affineCoefficientCoverSample U poly hm q (fun k x => (z (k, x) : ℝ))
    let Dphysical := fun z : Option (LayerSamplerVariables G I n B) × X → ℤ => D (affineSampleCoefficientTorus U poly hm (fun k x => (z (k, x) : ℝ)))
    ∃ hD0 : ∀ z, 0 ≤ Dphysical z,
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z,
    ∃ hDpos : 0 < selectedResidueDensityMass stride cells width Dphysical,
      |selectedResidueDensityMass stride cells width Dphysical - 1| ≤ 2 * δ + ε ∧
      1 / 2 ≤ selectedResidueDensityMass stride cells width Dphysical ∧
      selectedResidueDensityMass stride cells width Dphysical ≤ 3 / 2 ∧
      ‖(∑' z, ((selectedResidueDensityPMF stride cells width hwidth hZ Dphysical hD0 hDpos z).toReal : ℂ) *
          dominatedDensityRatio Dc (A (fun v => (z v : ZMod q))) (sample z)) -
        ∑' z, ((selectedResidueSmoothPMF stride cells width hwidth hZ z).toReal : ℂ) *
          ((∫ x, A (fun v => (z v : ZMod q)) x ∂μ) : ℂ)‖ ≤ 12 * (2 * δ + ε) := by
  let (x : X) : NeZero (stride x) := ⟨(hstride x).ne'⟩
  let : NeZero q := ⟨hq.ne'⟩
  let refined := fun x => stride x * q
  let hdiv := fun x => dvd_mul_right (stride x) q
  let fine := selectedResidueRefinement stride refined hdiv cells
  let fmask := fun r => mask (refinedColumnExtraResidue stride q r)
  have hfine : fine.Nonempty := selectedResidueRefinement_nonempty stride refined hdiv cells hcells
  have hresult := exists_allocated_joint_masked_density_comparison B U b hb o S C V hC hV
    hR hσ hσ1 Cinv hCinv hchart hsmall q hq hP hmP hK hRP hσP hcount hI hn hJ hAP hLP
    hCP hVP hqP hδ hδP μ ν poly hp hm hPs hX hframe hqPs hε hρ hεPs hρPs
    refined (fun x => Nat.mul_pos (hstride x) hq) hSmax hSmaxPs hstrideMax H hsize hrank hRs
    fine hfine fmask (fun r => hmask _) width hwidth hwide hfreqPs hmassPs hsmallError
  dsimp only at hresult ⊢
  obtain ⟨hD0, hZref, hDref, hmassref, hlower, hupper, herror⟩ := hresult
  let Dphysical := fun z : Option (LayerSamplerVariables G I n B) × X → ℤ =>
    allocatedCoefficientDensity B U b hb o hR hσ S
      (affineSampleCoefficientTorus U poly hm (fun k x => (z (k,x) : ℝ)))
  have hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z := by
    rwa [selectedResidueSmoothMass_refinement] at hZref
  have hDpos : 0 < selectedResidueDensityMass stride cells width Dphysical := by
    rwa [selectedResidueDensityMass_refinement] at hDref
  have hpmf := selectedResidueSmoothPMF_refinement stride refined hdiv cells width hwidth hZ hZref
  have htilt := selectedResidueDensityPMF_refinement stride refined hdiv cells width hwidth
    hZ hZref Dphysical hD0 hDpos hDref
  have hmaskpattern (z : Option (LayerSamplerVariables G I n B) × X → ℤ) :
      fmask (columnResiduePattern refined z) = mask (fun v => (z v : ZMod q)) := by
    simp only [fmask, refinedColumnExtraResidue, refined, columnResidueReduction_pattern]
    rfl
  dsimp only [fine] at hmassref hlower hupper herror
  dsimp only [Dphysical] at htilt
  refine ⟨hD0, hZ, hDpos, ?_, ?_, ?_, ?_⟩
  · simpa only [selectedResidueDensityMass_refinement] using hmassref
  · simpa only [selectedResidueDensityMass_refinement] using hlower
  · simpa only [selectedResidueDensityMass_refinement] using hupper
  · simpa only [htilt, hpmf, hmaskpattern] using herror

end Erdos3.VectorPolynomial

end

end OAI
