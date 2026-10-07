import OAI.Combinatorics.Progressions.Lattices.AllocatedSpatialResidueMaskedComparison
import OAI.Combinatorics.Progressions.Lattices.SelectedResidueMaskedTest
import OAI.Combinatorics.Progressions.Probability.AllocatedMaskedCoefficientHaarLaw

namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type} [Fintype G] {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J E : Fin m → Type} [∀ j, Fintype (J j)] [∀ j, DecidableEq (J j)] [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

include hC hV in

theorem exists_allocated_spatial_chart_event_comparison
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    (q : ℕ) [NeZero q] (hq : 0 < q)
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
    (event : ((Option (LayerSamplerVariables G I n B) × X) → ZMod q) →
      CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → Prop)
    (width : Option (LayerSamplerVariables G I n B) × X → ℝ) (hwidth : ∀ z, 0 < width z)
    (hwide : ∀ z, ρ * H z.2 ≤ width z)
    (hfreqPs : (4 * allocatedFourierLogBudget m P + 2)^4 ≤ Ps)
    (hmassPs : 4 * allocatedFourierLogBudget m P * (4 * allocatedFourierLogBudget m P + 2)^4 +
      allocatedFourierLogBudget m P ≤ Ps)
    (hsmallError : 2 * δ + ε ≤ 1 / 2) :
    let Dphysical := fun z : Option (LayerSamplerVariables G I n B) × X → ℤ =>
      allocatedCoefficientDensity B U b hb o hR hσ S
        (affineSampleCoefficientTorus U poly hm (fun k x => (z (k, x) : ℝ)))
    let sample := fun z : Option (LayerSamplerVariables G I n B) × X → ℤ =>
      affineCoefficientCoverSample U poly hm q (fun k x => (z (k, x) : ℝ))
    ∃ hD0 : ∀ z, 0 ≤ Dphysical z,
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z,
    ∃ hDpos : 0 < selectedResidueDensityMass stride cells width Dphysical,
      |selectedResidueDensityMass stride cells width Dphysical - 1| ≤ 2 * δ + ε ∧
      1 / 2 ≤ selectedResidueDensityMass stride cells width Dphysical ∧
      selectedResidueDensityMass stride cells width Dphysical ≤ 3 / 2 ∧
      |(∑' z, (selectedResidueDensityPMF stride cells width hwidth hZ Dphysical hD0 hDpos z).toReal *
          (if coefficientDeckChartEvent U bW b hb o q (event (fun v => (z v : ZMod q))) (sample z) then 1 else 0)) -
        ∑' z, (selectedResidueSmoothPMF stride cells width hwidth hZ z).toReal *
          ∫ y, allocatedMaskedCoefficientDensity B U b o S q
            (coefficientDeckResidueMask U bW b hb q
              (fun a => if event (fun v => (z v : ZMod q)) a then 1 else 0)) y ∂μ| ≤
        12 * (2 * δ + ε) := by
  dsimp only
  let mask := fun r => coefficientDeckResidueMask U bW b hb q
    (fun a => if event r a then (1 : ℝ) else 0)
  have hmask : ∀ r z, mask r z ∈ Set.Icc (0 : ℝ) 1 := by
    intro r z
    simp only [mask, coefficientDeckResidueMask]
    split_ifs <;> constructor <;> norm_num
  obtain ⟨hD0, hZ, hDpos, hmass, hlower, hupper, he⟩ :=
    exists_allocated_spatial_residue_masked_comparison B U b hb o S C V hC hV
      hR hσ hσ1 Cinv hCinv hchart hsmall q hq hP hmP hK hRP hσP hcount hI hn hJ hAP hLP
      hCP hVP hqP hδ hδP μ ν poly hp hm hPs hX hframe hqPs hε hρ hεPs hρPs stride hstride
      hSmax hSmaxPs hstrideMax H hsize hrank hRs cells hcells mask hmask width hwidth hwide
      hfreqPs hmassPs hsmallError
  let D := allocatedCoefficientDensity B U b hb o hR hσ S
  let Dc := fun x => D (quotientIntegerCover (coefficientIntegerLattice U) q x)
  let A := fun r => allocatedMaskedCoefficientDensity B U b o S q (mask r)
  let sample := fun z : Option (LayerSamplerVariables G I n B) × X → ℤ =>
    affineCoefficientCoverSample U poly hm q (fun k x => (z (k,x) : ℝ))
  let Dphysical := fun z : Option (LayerSamplerVariables G I n B) × X → ℤ =>
    D (affineSampleCoefficientTorus U poly hm (fun k x => (z (k,x) : ℝ)))
  let ev := fun z => coefficientDeckChartEvent U bW b hb o q
    (event (fun v => (z v : ZMod q))) (sample z)
  have hdom (r) := allocatedMaskedCoefficientDensity_le_density B U b o S C V hC hV hb
    hR hσ hσ1 Cinv hCinv hchart hsmall q (mask r) (hmask r)
  have hmean := selectedResidueDensityPMF_mean_congr_density stride cells width hwidth hZ
    Dphysical hD0 hDpos (fun z => if ev z then (1 : ℂ) else 0)
    (fun z => dominatedDensityRatio Dc (A (fun v => (z v : ZMod q))) (sample z)) (by
      intro z
      have hd : Dc (sample z) = Dphysical z :=
        coefficientCover_density_sample U poly hm q hq D _
      rw [← hd, dominatedDensityRatio_mul Dc (A _) (fun x => (hdom _ x).1) (fun x => (hdom _ x).2)]
      have hid := allocatedMaskedCoefficientDensity_event B U bW b hb o S hR hσ hσ1
        Cinv hCinv hchart hsmall C V hC hV q (event (fun v => (z v : ZMod q))) (sample z)
      simpa only [Complex.ofReal_mul, apply_ite, Complex.ofReal_one, Complex.ofReal_zero]
        using congrArg Complex.ofReal hid)
  change ‖(∑' z, ((selectedResidueDensityPMF stride cells width hwidth hZ Dphysical hD0 hDpos z).toReal : ℂ) *
    dominatedDensityRatio Dc (A (fun v => (z v : ZMod q))) (sample z)) - _‖ ≤ _ at he
  rw [← hmean] at he
  simp only [mask] at he
  refine ⟨hD0, hZ, hDpos, hmass, hlower, hupper, ?_⟩
  have he' := he
  rw [show (∑' z, ((selectedResidueDensityPMF stride cells width hwidth hZ Dphysical hD0 hDpos z).toReal : ℂ) *
      (if ev z then (1 : ℂ) else 0)) =
      ((∑' z, (selectedResidueDensityPMF stride cells width hwidth hZ Dphysical hD0 hDpos z).toReal *
        (if ev z then (1 : ℝ) else 0) : ℝ) : ℂ) by
        simp only [Complex.ofReal_tsum, Complex.ofReal_mul, apply_ite, Complex.ofReal_one, Complex.ofReal_zero]] at he'
  simp only [integral_complex_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_tsum,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at he'
  exact he'

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type} [Fintype G] {I : Fin m → Type} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ a, Fintype (B a)]
variable {J E : Fin m → Type} [∀ j, Fintype (J j)] [∀ j, DecidableEq (J j)] [∀ j, Fintype (E j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (E j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)

variable (C V : Fin m → ℝ≥0)
variable (hC : ∀ j x, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) x‖ ≤ C j * ‖x‖)
variable (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
  mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)

include hC hV in

theorem exists_allocated_spatial_witness_comparison
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (hσ1 : ∀ j, σ j ≤ 1)
    (Cinv : Fin m → ℝ) (hCinv : ∀ j, 0 ≤ Cinv j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ Cinv j * ‖v‖)
    (hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1/4)
    (q : ℕ) [NeZero q] (hq : 0 < q)
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
    (event : ((Option (LayerSamplerVariables G I n B) × X) → ZMod q) →
      CoefficientChartResidues (LayerSamplerVariables G I n B) n E q → Prop)
    (width : Option (LayerSamplerVariables G I n B) × X → ℝ) (hwidth : ∀ z, 0 < width z)
    (hwide : ∀ z, ρ * H z.2 ≤ width z)
    (hfreqPs : (4 * allocatedFourierLogBudget m P + 2)^4 ≤ Ps)
    (hmassPs : 4 * allocatedFourierLogBudget m P * (4 * allocatedFourierLogBudget m P + 2)^4 +
      allocatedFourierLogBudget m P ≤ Ps)
    (hsmallError : 2 * δ + ε ≤ 1 / 2) :
    let Dphysical := fun z : Option (LayerSamplerVariables G I n B) × X → ℤ =>
      allocatedCoefficientDensity B U b hb o hR hσ S
        (affineSampleCoefficientTorus U poly hm (fun k x => (z (k, x) : ℝ)))
    let sample := fun z : Option (LayerSamplerVariables G I n B) × X → ℤ =>
      affineCoefficientCoverSample U poly hm q (fun k x => (z (k, x) : ℝ))
    ∃ hD0 : ∀ z, 0 ≤ Dphysical z,
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells width z,
    ∃ hDpos : 0 < selectedResidueDensityMass stride cells width Dphysical,
      |selectedResidueDensityMass stride cells width Dphysical - 1| ≤ 2 * δ + ε ∧
      1 / 2 ≤ selectedResidueDensityMass stride cells width Dphysical ∧
      selectedResidueDensityMass stride cells width Dphysical ≤ 3 / 2 ∧
      |(∑' z, (selectedResidueDensityPMF stride cells width hwidth hZ Dphysical hD0 hDpos z).toReal *
          (if coefficientDeckChartEvent U bW b hb o q (event (fun v => (z v : ZMod q))) (sample z) then 1 else 0)) -
        ∑' z, (selectedResidueSmoothPMF stride cells width hwidth hZ z).toReal *
          ∫ p : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n ×
              CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E q,
            (if event (fun v => (z v : ZMod q)) (coefficientSamplerChartResidues q p.1 p.2) then (1 : ℝ) else 0)
            ∂(allocatedCoefficientSource B U b hR hσ S).prod
              (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) E q)).toMeasure| ≤
        12 * (2 * δ + ε) := by
  dsimp only
  obtain ⟨hD0, hZ, hDpos, hmass, hlower, hupper, he⟩ :=
    exists_allocated_spatial_chart_event_comparison B U bW b hb o S C V hC hV
      hR hσ hσ1 Cinv hCinv hchart hsmall q hq hP hmP hK hRP hσP hcount hI hn hJ hAP hLP
      hCP hVP hqP hδ hδP μ ν poly hp hm hPs hX hframe hqPs hε hρ hεPs hρPs stride hstride
      hSmax hSmaxPs hstrideMax H hsize hrank hRs cells hcells event width hwidth hwide
      hfreqPs hmassPs hsmallError
  have hhaar (r) := allocatedMaskedCoefficientDensity_haar_integral B U bW b hb o S C V hC hV μ ν
    hR hσ hσ1 Cinv hCinv hchart hsmall q
    (fun a => if event r a then (1 : ℝ) else 0)
    (fun a => by split_ifs <;> constructor <;> norm_num)
  simp_rw [hhaar] at he
  exact ⟨hD0, hZ, hDpos, hmass, hlower, hupper, he⟩

end Erdos3.VectorPolynomial

end

end OAI
