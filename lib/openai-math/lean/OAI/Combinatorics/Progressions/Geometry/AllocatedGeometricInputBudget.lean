import OAI.Combinatorics.Progressions.Estimates.AllocatedFixedInitializedCover
import OAI.Combinatorics.Progressions.Estimates.AllocatedInitializedIdealCover

namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory

def allocatedUniformChartLog {A : Type*} [Semiring A] (p : A) : A := 20 * (p + 1) ^ 3

theorem allocatedUniformChartLog_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ allocatedUniformChartLog p := by unfold allocatedUniformChartLog; positivity

theorem exists_uniform_projected_chart {J : Type*} [Fintype J]
    (W : Submodule ℝ (EuclideanSpace ℝ J))
    [IsZLattice ℝ (latticeSection (standardEuclideanLattice J) W)]
    {p : ℝ} (hdim : (Fintype.card J : ℝ) ≤ p) :
    ∃ b : Basis (Fin (finrank ℝ Wᗮ)) ℝ Wᗮ,
      span ℤ (Set.range b) = projectedIntegerLattice W ∧
      (∀ z, ‖normalizedOrthogonalChart W b z‖ ≤ Real.exp (allocatedUniformChartLog p) * ‖z‖) ∧
      (∀ z, ‖(normalizedOrthogonalChart W b).symm z‖ ≤ Real.exp (allocatedUniformChartLog p) * ‖z‖) ∧
      0 ≤ mixedDensityCovolumeRatio W b ∧
      mixedDensityCovolumeRatio W b ≤ Real.exp (allocatedUniformChartLog p) := by
  have hn : finrank ℝ Wᗮ ≤ Fintype.card J := by
    simpa only [finrank_euclideanSpace] using Wᗮ.finrank_le
  have hnp : (finrank ℝ Wᗮ : ℝ) ≤ p := (Nat.cast_le.mpr hn).trans hdim
  have hlog : 20 * ((finrank ℝ Wᗮ : ℝ) + 1) ^ 3 ≤ allocatedUniformChartLog p := by
    unfold allocatedUniformChartLog
    gcongr
  have he := Real.exp_le_exp.mpr hlog
  obtain ⟨b, hb, _, hf, hi, _, hv⟩ := exists_quantitative_projected_chart W
  exact ⟨b, hb, fun z => (hf z).trans (mul_le_mul_of_nonneg_right he (norm_nonneg z)),
    fun z => (hi z).trans (mul_le_mul_of_nonneg_right he (norm_nonneg z)),
    (mixedDensityCovolumeRatio_pos W b).le, hv.trans he⟩

namespace VectorPolynomial

theorem exists_allocated_uniform_charts {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {p : ℝ} (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p) :
    ∃ b : ∀ j, Basis (Fin (finrank ℝ (euclideanSubspace (U j))ᗮ)) ℝ (euclideanSubspace (U j))ᗮ,
      (∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))) ∧
      (∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤
        Real.exp (allocatedUniformChartLog p) * ‖z‖) ∧
      (∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤
        Real.exp (allocatedUniformChartLog p) * ‖z‖) ∧
      (∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
        mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp (allocatedUniformChartLog p)) := by
  choose b hb hf hi hv0 hv using (fun j => exists_uniform_projected_chart (euclideanSubspace (U j)) (hJ j))
  exact ⟨b, hb, hf, hi, fun j => ⟨hv0 j, hv j⟩⟩

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

noncomputable def allocatedGeometryInput {A : Type*} [Semiring A]
    (m : ℕ) (p c s E : A) : A :=
  p + c + s + E + allocatedIdealCoverPrimitiveLog m p c

theorem allocatedGeometryInput_bounds (m : ℕ) {p c s E : ℝ}
    (hp : 0 ≤ p) (hc : 0 ≤ c) (hs : 0 ≤ s) (hE : 0 ≤ E) :
    let q := allocatedGeometryInput m p c s E
    0 ≤ q ∧ p ≤ q ∧ c ≤ q ∧ s ≤ q ∧ E ≤ q ∧ allocatedIdealCoverPrimitiveLog m p c ≤ q := by
  have hL := (allocatedIdealCoverPrimitiveRadius_bounds m hp hc).1
  dsimp only [allocatedGeometryInput]
  constructor
  · positivity
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem exists_allocatedGeometryInput_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ p : ℝ, 0 ≤ p → allocatedGeometryInput m p p p p ≤ (p + a) ^ a := by
  let poly : Polynomial ℕ := allocatedGeometryInput m Polynomial.X Polynomial.X Polynomial.X Polynomial.X
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro p hp
  simpa [poly, allocatedGeometryInput, allocatedIdealCoverPrimitiveLog, allocatedIdealCoverInputLog,
    allocatedSiteCoefficientLog, allocatedComparisonDimension, Polynomial.eval₂_pow] using hbound p hp

noncomputable def allocatedGeometrySourceInput {A : Type*} [Semiring A]
    (m : ℕ) (p c e E : A) : A :=
  allocatedGeometryInput m p c
    (allocatedSiteScaleLog m (allocatedGeometryInput m p c 0 E) e E) E

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq
attribute [local instance] ScalarSiteExpansion.termFinite

variable {m dim : ℕ} {G : Type uG} [Fintype G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {p c e E : ℝ}
local notation "radius" => allocatedIdealCoverPrimitiveRadius m p c
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

variable (M₀ : ℕ)
local notation "period" => kernelPeriodCandidate (m + 1)
local notation "P" => canonicalScalarSourceEnvelope m M₀
local notation "L" => scalarSourceTransitionBound

local notation "scaleInput" => allocatedGeometryInput m p c 0 E
local notation "scaleLog" => allocatedSiteScaleLog m scaleInput e E
local notation "inputParameter" => allocatedGeometrySourceInput m p c e E
local notation "sourceParameter" => siteSourceParameter m inputParameter
local notation "maskLog" => siteSourceMaskLog m inputParameter
local notation "δ" => allocatedSitePrimitiveTolerance m sourceParameter maskLog (allocatedIdealProfileLog m sourceParameter e) E
local notation "Λ" => allocatedSiteSpectrumLog m sourceParameter maskLog (allocatedIdealProfileLog m sourceParameter e) E
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "active" => allocatedActiveGrid B U b S
local notation "activeAxes" => {a : {a // grid a} // active a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "axisN" => allocatedGridNaturalScale B U b S

local notation "sitePeriods" => (fun a : activeAxes =>
  (allocatedPositiveSitePeriod B (Fin dim) U b hR S (Subtype.val a) : ℕ))

local notation "pointTolerance" => allocatedSitePointTolerance (G := G) B rowSets δ
local notation "torus" => (fun a : activeAxes => allocatedGridTorusFactor B (Fin dim) (ig (Subtype.val a)))
local notation "chartCap" => (NNReal.mk (Real.exp c) (Real.exp_nonneg c))
local notation "geometryQ" => Real.toNNReal (8 * (allocatedComparisonDimension m p + 1))
local notation "siteLip" => (NNReal.mk (Real.exp (1 + 6 * Λ + 12)) (Real.exp_nonneg _) + 4 : ℝ≥0)
local notation "coefficientCap" => (fun a : activeAxes =>
  allocatedGridPointCap B P (ig (Subtype.val a)) (rowSets (Sigma.fst (ig (Subtype.val a)))) *
    Real.exp (Fintype.card (Finset (Fin dim)) * (4 * Λ + 8) + Λ))

theorem exists_geometric_good_kernel_ideal_cover_family
    (hp : 0 ≤ p) (hc : 0 ≤ c) (he : 0 ≤ e) (hE : 0 ≤ E)
    (hdimSmall : dim ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn₁ : ∀ j, (n j : ℝ) ≤ p)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (hcutoff : (M₀ : ℝ) ≤ Real.exp p)
    (hScale : S = allocatedSiteScale (G := G) B U b hR hσ scaleInput e E)
    (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp p)
    (hRadius : ∀ j, R j = radius)
    (hforward : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ Real.exp c * ‖z‖)
    (hinverse : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Real.exp c * ‖z‖)
    (hvolume : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp c)
    (hσ1 : ∀ j, σ j ≤ 1)
    (hBlocks : ∀ j i, siteSpectrumBlockCount m ≤ Fintype.card (B ⟨j, Sum.inr i⟩)) :
    ∃ K : ℕ, 2 ≤ K ∧
      ∃ witnesses : (t : Fin M₀) → (r : AllocatedPositiveResidue (dim := dim) B U b S (period t)) →
        AllocatedResidueSiteWitness (dim := dim) B U b S (period t) r.val,
      (∀ t r, allocatedActiveSiteBounds B U b S rowSets P pointTolerance Λ sitePeriods (witnesses t r).expansion) ∧ ∀
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type uQ} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d]
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))],
    ∃ g : (t : Fin M₀) → (r : AllocatedPositiveResidue (dim := dim) B U b S (period t)) →
        (∀ a, ((witnesses t r).expansion a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ),
      (∀ t r k s, LipschitzWith (max (((Fintype.card activeAxes * siteLip) * geometryQ) *
        (Real.toNNReal (Real.exp sourceParameter) * ∑ j, chartCap * Fintype.card (J j)) * commonSitePeriod (witnesses t r).expansion k)
          (4 * commonSitePeriod (witnesses t r).expansion k)) (g t r k s) ∧ ∀ z, ‖g t r k s z‖ ≤ 1) ∧
      (∀ t r, (∑ k, ‖coverSiteCoefficient (witnesses t r).expansion k‖) ≤
        (2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * ∏ a, (coefficientCap) a) ∧
      (∀ t, allocatedResidueCoverCoefficientMass B U b S (period t) (witnesses t) ≤
        (2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * ∏ a, (coefficientCap) a) ∧
      ∀ (x : G → IntegerScalarCubeBox (Fin dim) S.value)
        (selection : Fin dim ↪ G) {κ : ℝ}
        (_hx : GoodScalarKernelTuple selection κ M₀ x),
      ∃ t : Fin M₀,
        (∀ root : G → ℤ, integerScalarLattice (Unit ⊕ Fin dim) (period t : ℤ) ≤
          pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
            (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)) ∧
        (∀ j, integerScalarLattice (rowTypes j) (period t : ℤ) ≤
          (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range) ∧
      ∀ (τ : ℝ≥0), 0 < τ → τ ≤ 1 → (τ : ℝ)⁻¹ ≤ Real.exp e → ∀
    {X : Type uX} [Fintype X] [DecidableEq X]
    {P₀ : ℝ} (_hP : 0 ≤ P₀) (_hn : (Fintype.card X : ℝ) ≤ P₀)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P₀)
    (_hbudget : allocatedSiteErrorFourierOutput m sourceParameter maskLog (allocatedIdealProfileLog m sourceParameter e) ≤ P₀)
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hmp : ∀ j e, coefficients (p j) e ∈ U j)
    (stride : X → ℕ) (_hs : ∀ x, 0 < stride x)
    {R₁ S₀ ρ : ℝ} (_hS : 0 ≤ S₀) (_hSP : S₀ ≤ Real.exp P₀) (_hρ : 0 < ρ)
    (_hρP : 1 / ρ ≤ Real.exp P₀)
    (_hstride : ∀ x, (stride x : ℝ) ≤ S₀)
    (H : X → ℝ) (_hsize : ∀ x, Real.exp ((P₀ + K) ^ K) ≤ H x)
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H R₁ (U j) (p j))
    (_hR : Real.exp ((P₀ + K) ^ K) ≤ R₁)
    (cells : Finset (ColumnResiduePattern (Option (Fin dim)) X stride)) (_hcells : cells.Nonempty)
    (W : Option (Fin dim) × X → ℝ) (hW : ∀ z, 0 < W z) (_hwidth : ∀ z, ρ * H z.2 ≤ W z),
    let f := allocatedPhysicalLongIdeal B U b hR S rowSets τ
    let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let error := fun z : Option (Fin dim) × X → ℤ =>
      law.complexMean (fun y₀ =>
        (allocatedWholeMaskedCoveredProfile (O := rowTypes) B U b hR hσ S x (rows) hb o bW d y₀ (period t) f
          (physicalCubeRowSample U d (rows) p hmp (standardPhysicalCubeOutput z)) : ℂ)) -
      (law.fiberLaw (principalResidueLabel (period t))).complexMean
        (allocatedSupportedIdealCoverValue B U b hR hσ S (period t) (witnesses t) hb o bW d (g t) τ x p hmp
          (standardPhysicalCubeOutput z))
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells W z,
      selectedResidueDensityMass stride cells W (fun z => ‖error z‖) ≤ Real.exp (-E) ∧
      ∀ φ : (Option (Fin dim) × X → ℤ) → ℂ, (∀ z, ‖φ z‖ ≤ 1) →
        ‖∑' z, ((selectedResidueSmoothPMF stride cells W hW hZ z).toReal : ℂ) *
          (error z * φ z)‖ ≤ Real.exp (-E) := by
  have hradius := allocatedIdealCoverPrimitiveRadius_bounds m hp hc
  obtain ⟨hq₀, hpq₀, _, _, _, hLq₀⟩ := allocatedGeometryInput_bounds m hp hc (le_refl 0) hE
  have hs₀ : 0 ≤ scaleLog := (allocatedSiteSourceLog_bounds m hq₀ he hE).1
  obtain ⟨hq, hpq, hcq, hsq, hEq, hLq⟩ := allocatedGeometryInput_bounds m hp hc hs₀ hE
  have hqSource := (siteSourceParameter_bounds m hq).2.1
  have hrowdim : Fintype.card (Fin dim) ≤ m + 1 := by
    simpa only [Fintype.card_fin] using hdimSmall
  have hRq₀ (j : Fin m) : (R j)⁻¹ ≤ Real.exp scaleInput := by
    rw [hRadius j]
    exact hradius.2.2.2.trans_le (Real.exp_le_exp.mpr hLq₀)
  have hS₁ : (S.value : ℝ) ≤ Real.exp scaleLog := by
    rw [hScale]
    exact allocatedSiteScale_upper (G := G) B U b hR hσ rows hrowdim
      (fun _ => Subtype.val_injective) hq₀ he hE (hvars.trans hpq₀)
      (fun j => (hI j).trans hpq₀) (fun j => (hn₁ j).trans hpq₀) hRq₀
      (fun j => (hσi j).trans (Real.exp_le_exp.mpr hpq₀))
  have hsize : (Fintype.card (Fin dim) + 1) * M₀ ^ (m + 1) ≤ S.value := by
    rw [hScale]
    exact allocatedSiteScale_period_window (G := G) B U b hR hσ hdimSmall hq₀ he hE
      (hcutoff.trans (Real.exp_le_exp.mpr hpq₀))
  have hdim := allocatedComparisonDimensions_of_primitive (G := G) B rows hrowdim
    (fun _ => Subtype.val_injective) hp hvars hI hn₁
  have hsmall := allocatedIdealCoverPrimitiveRadius_le (G := G) B rowSets hp hc hrowdim
    hvars hI hn₁ (fun _ => Real.exp c) (fun _ => (Real.exp_pos c).le) (fun _ => le_rfl)
  have hQsite (a : activeAxes) : 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (ig a.val).1 (ig a.val).2) : ℝ) + 1) ≤ geometryQ := by
    have hcount := allocatedIntegerBlock_card_le B rowSets hdim (ig a.val).1 (ig a.val).2
    have hD := hdim.nonneg
    rw [Real.coe_toNNReal _ (by positivity)]
    simpa only [layerIntegerPrincipalSlots_card] using (show
      8 * ((Fintype.card (B ⟨(ig a.val).1, Sum.inr (ig a.val).2⟩) : ℝ) + 1) ≤
        8 * (allocatedComparisonDimension m p + 1) by linarith)
  obtain ⟨K, hK, witnesses, hBounds, hgeometry⟩ := exists_initialized_good_kernel_ideal_cover_family
    (B := B) (U := U) (b := b) (hR := hR) (hσ := hσ) (S := S) (M₀ := M₀)
    (hsize := hsize) (p := inputParameter) hq he hE hdimSmall
    (hvars.trans hpq) (fun j => (hI j).trans hpq) (fun j => (hn₁ j).trans hpq)
    (fun j => (hJ j).trans hpq) (hcutoff.trans (Real.exp_le_exp.mpr hpq))
    (hS₁.trans (Real.exp_le_exp.mpr hsq)) hEq (fun j => (hRadius j).trans_le hradius.2.2.1) hBlocks
  refine ⟨K, hK, witnesses, hBounds, ?_⟩
  intro hb o Q _ bW d _ _
  have hRinv (j : Fin m) : (R j)⁻¹ ≤ Real.exp sourceParameter := by
    rw [hRadius j]
    exact hradius.2.2.2.trans_le (Real.exp_le_exp.mpr (hLq.trans hqSource))
  exact hgeometry hb o bW d (fun _ => chartCap) (fun _ => chartCap)
    hforward (fun j => ⟨(mixedDensityCovolumeRatio_pos _ _).le, hvolume j⟩)
    (fun _ => Real.exp_le_exp.mpr (hcq.trans hqSource))
    (fun _ => Real.exp_le_exp.mpr (hcq.trans hqSource)) hRinv hσ1 geometryQ hQsite
    (fun _ => Real.exp c) (fun _ => (Real.exp_pos c).le) hinverse (fun j => (hRadius j).trans_le (hsmall j))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype activeAmbientAxisDecidableEq
attribute [local instance] ScalarSiteExpansion.termFinite

variable {m dim : ℕ} {G : Type uG} [Fintype G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {p c e E : ℝ}
local notation "radius" => allocatedIdealCoverPrimitiveRadius m p c
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

variable (M₀ : ℕ)
local notation "period" => kernelPeriodCandidate (m + 1)
local notation "P" => canonicalScalarSourceEnvelope m M₀
local notation "L" => scalarSourceTransitionBound

local notation "scaleInput" => allocatedGeometryInput m p c 0 E
local notation "scaleLog" => allocatedSiteScaleLog m scaleInput e E
local notation "inputParameter" => allocatedGeometrySourceInput m p c e E
local notation "sourceParameter" => siteSourceParameter m inputParameter
local notation "maskLog" => siteSourceMaskLog m inputParameter
local notation "δ" => allocatedSitePrimitiveTolerance m sourceParameter maskLog (allocatedIdealProfileLog m sourceParameter e) E
local notation "Λ" => allocatedSiteSpectrumLog m sourceParameter maskLog (allocatedIdealProfileLog m sourceParameter e) E
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "active" => allocatedActiveGrid B U b S
local notation "activeAxes" => {a : {a // grid a} // active a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "axisN" => allocatedGridNaturalScale B U b S

local notation "sitePeriods" => (fun a : activeAxes =>
  (allocatedPositiveSitePeriod B (Fin dim) U b hR S (Subtype.val a) : ℕ))

local notation "pointTolerance" => allocatedSitePointTolerance (G := G) B rowSets δ
local notation "torus" => (fun a : activeAxes => allocatedGridTorusFactor B (Fin dim) (ig (Subtype.val a)))
local notation "chartCap" => (NNReal.mk (Real.exp c) (Real.exp_nonneg c))
local notation "geometryQ" => Real.toNNReal (8 * (allocatedComparisonDimension m p + 1))
local notation "siteLip" => (NNReal.mk (Real.exp (1 + 6 * Λ + 12)) (Real.exp_nonneg _) + 4 : ℝ≥0)
local notation "coefficientCap" => (fun a : activeAxes =>
  allocatedGridPointCap B P (ig (Subtype.val a)) (rowSets (Sigma.fst (ig (Subtype.val a)))) *
    Real.exp (Fintype.card (Finset (Fin dim)) * (4 * Λ + 8) + Λ))

variable {K : ℕ}
variable (hSampling : ∀ inst : ∀ j : Fin m,
    Fintype {s : Finset (Fin dim) // s ∈ boundedBooleanJetRows (Fin dim) (j.val + 1)},
  @AllocatedBooleanRowsSampling.{uX,uJ,uG,uI,uB,uQ} m dim K
    (fun j => {s : Finset (Fin dim) // s ∈ boundedBooleanJetRows (Fin dim) (j.val + 1)})
    inst (fun _ => Subtype.val))

include hSampling in
theorem geometric_good_kernel_ideal_cover_at_sampling
    (hp : 0 ≤ p) (hc : 0 ≤ c) (he : 0 ≤ e) (hE : 0 ≤ E)
    (hdimSmall : dim ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p) (hn₁ : ∀ j, (n j : ℝ) ≤ p)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p)
    (hcutoff : (M₀ : ℝ) ≤ Real.exp p)
    (hScale : S = allocatedSiteScale (G := G) B U b hR hσ scaleInput e E)
    (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp p)
    (hRadius : ∀ j, R j = radius)
    (hforward : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) z‖ ≤ Real.exp c * ‖z‖)
    (hinverse : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm z‖ ≤ Real.exp c * ‖z‖)
    (hvolume : ∀ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ Real.exp c)
    (hσ1 : ∀ j, σ j ≤ 1)
    (hBlocks : ∀ j i, siteSpectrumBlockCount m ≤ Fintype.card (B ⟨j, Sum.inr i⟩)) :
    ∃ witnesses : (t : Fin M₀) → (r : AllocatedPositiveResidue (dim := dim) B U b S (period t)) →
        AllocatedResidueSiteWitness (dim := dim) B U b S (period t) r.val,
      (∀ t r, allocatedActiveSiteBounds B U b S rowSets P pointTolerance Λ sitePeriods (witnesses t r).expansion) ∧ ∀
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type uQ} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d]
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))],
    ∃ g : (t : Fin M₀) → (r : AllocatedPositiveResidue (dim := dim) B U b S (period t)) →
        (∀ a, ((witnesses t r).expansion a).Term) → Finset (Fin dim) → (((Σ j, J j) → UnitAddCircle) → ℂ),
      (∀ t r k s, LipschitzWith (max (((Fintype.card activeAxes * siteLip) * geometryQ) *
        (Real.toNNReal (Real.exp sourceParameter) * ∑ j, chartCap * Fintype.card (J j)) * commonSitePeriod (witnesses t r).expansion k)
          (4 * commonSitePeriod (witnesses t r).expansion k)) (g t r k s) ∧ ∀ z, ‖g t r k s z‖ ≤ 1) ∧
      (∀ t r, (∑ k, ‖coverSiteCoefficient (witnesses t r).expansion k‖) ≤
        (2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * ∏ a, (coefficientCap) a) ∧
      (∀ t, allocatedResidueCoverCoefficientMass B U b S (period t) (witnesses t) ≤
        (2 : ℝ) ^ Fintype.card (Finset (Fin dim)) * ∏ a, (coefficientCap) a) ∧
      ∀ (x : G → IntegerScalarCubeBox (Fin dim) S.value)
        (selection : Fin dim ↪ G) {κ : ℝ}
        (_hx : GoodScalarKernelTuple selection κ M₀ x),
      ∃ t : Fin M₀,
        (∀ root : G → ℤ, integerScalarLattice (Unit ⊕ Fin dim) (period t : ℤ) ≤
          pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
            (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)) ∧
        (∀ j, integerScalarLattice (rowTypes j) (period t : ℤ) ≤
          (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range) ∧
      ∀ (τ : ℝ≥0), 0 < τ → τ ≤ 1 → (τ : ℝ)⁻¹ ≤ Real.exp e → ∀
    {X : Type uX} [Fintype X] [DecidableEq X]
    {P₀ : ℝ} (_hP : 0 ≤ P₀) (_hn : (Fintype.card X : ℝ) ≤ P₀)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P₀)
    (_hbudget : allocatedSiteErrorFourierOutput m sourceParameter maskLog (allocatedIdealProfileLog m sourceParameter e) ≤ P₀)
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hmp : ∀ j e, coefficients (p j) e ∈ U j)
    (stride : X → ℕ) (_hs : ∀ x, 0 < stride x)
    {R₁ S₀ ρ : ℝ} (_hS : 0 ≤ S₀) (_hSP : S₀ ≤ Real.exp P₀) (_hρ : 0 < ρ)
    (_hρP : 1 / ρ ≤ Real.exp P₀)
    (_hstride : ∀ x, (stride x : ℝ) ≤ S₀)
    (H : X → ℝ) (_hsize : ∀ x, Real.exp ((P₀ + K) ^ K) ≤ H x)
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H R₁ (U j) (p j))
    (_hR : Real.exp ((P₀ + K) ^ K) ≤ R₁)
    (cells : Finset (ColumnResiduePattern (Option (Fin dim)) X stride)) (_hcells : cells.Nonempty)
    (W : Option (Fin dim) × X → ℝ) (hW : ∀ z, 0 < W z) (_hwidth : ∀ z, ρ * H z.2 ≤ W z),
    let f := allocatedPhysicalLongIdeal B U b hR S rowSets τ
    let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let error := fun z : Option (Fin dim) × X → ℤ =>
      law.complexMean (fun y₀ =>
        (allocatedWholeMaskedCoveredProfile (O := rowTypes) B U b hR hσ S x (rows) hb o bW d y₀ (period t) f
          (physicalCubeRowSample U d (rows) p hmp (standardPhysicalCubeOutput z)) : ℂ)) -
      (law.fiberLaw (principalResidueLabel (period t))).complexMean
        (allocatedSupportedIdealCoverValue B U b hR hσ S (period t) (witnesses t) hb o bW d (g t) τ x p hmp
          (standardPhysicalCubeOutput z))
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells W z,
      selectedResidueDensityMass stride cells W (fun z => ‖error z‖) ≤ Real.exp (-E) ∧
      ∀ φ : (Option (Fin dim) × X → ℤ) → ℂ, (∀ z, ‖φ z‖ ≤ 1) →
        ‖∑' z, ((selectedResidueSmoothPMF stride cells W hW hZ z).toReal : ℂ) *
          (error z * φ z)‖ ≤ Real.exp (-E) := by
  have hradius := allocatedIdealCoverPrimitiveRadius_bounds m hp hc
  obtain ⟨hq₀, hpq₀, _, _, _, hLq₀⟩ := allocatedGeometryInput_bounds m hp hc (le_refl 0) hE
  have hs₀ : 0 ≤ scaleLog := (allocatedSiteSourceLog_bounds m hq₀ he hE).1
  obtain ⟨hq, hpq, hcq, hsq, hEq, hLq⟩ := allocatedGeometryInput_bounds m hp hc hs₀ hE
  have hqSource := (siteSourceParameter_bounds m hq).2.1
  have hrowdim : Fintype.card (Fin dim) ≤ m + 1 := by
    simpa only [Fintype.card_fin] using hdimSmall
  have hRq₀ (j : Fin m) : (R j)⁻¹ ≤ Real.exp scaleInput := by
    rw [hRadius j]
    exact hradius.2.2.2.trans_le (Real.exp_le_exp.mpr hLq₀)
  have hS₁ : (S.value : ℝ) ≤ Real.exp scaleLog := by
    rw [hScale]
    exact allocatedSiteScale_upper (G := G) B U b hR hσ rows hrowdim
      (fun _ => Subtype.val_injective) hq₀ he hE (hvars.trans hpq₀)
      (fun j => (hI j).trans hpq₀) (fun j => (hn₁ j).trans hpq₀) hRq₀
      (fun j => (hσi j).trans (Real.exp_le_exp.mpr hpq₀))
  have hsize : (Fintype.card (Fin dim) + 1) * M₀ ^ (m + 1) ≤ S.value := by
    rw [hScale]
    exact allocatedSiteScale_period_window (G := G) B U b hR hσ hdimSmall hq₀ he hE
      (hcutoff.trans (Real.exp_le_exp.mpr hpq₀))
  have hdim := allocatedComparisonDimensions_of_primitive (G := G) B rows hrowdim
    (fun _ => Subtype.val_injective) hp hvars hI hn₁
  have hsmall := allocatedIdealCoverPrimitiveRadius_le (G := G) B rowSets hp hc hrowdim
    hvars hI hn₁ (fun _ => Real.exp c) (fun _ => (Real.exp_pos c).le) (fun _ => le_rfl)
  have hQsite (a : activeAxes) : 8 * ((Finset.card (layerIntegerPrincipalSlots (G := G) B
      (ig a.val).1 (ig a.val).2) : ℝ) + 1) ≤ geometryQ := by
    have hcount := allocatedIntegerBlock_card_le B rowSets hdim (ig a.val).1 (ig a.val).2
    have hD := hdim.nonneg
    rw [Real.coe_toNNReal _ (by positivity)]
    simpa only [layerIntegerPrincipalSlots_card] using (show
      8 * ((Fintype.card (B ⟨(ig a.val).1, Sum.inr (ig a.val).2⟩) : ℝ) + 1) ≤
        8 * (allocatedComparisonDimension m p + 1) by linarith)
  obtain ⟨witnesses, hBounds, hgeometry⟩ := initialized_good_kernel_ideal_cover_at_sampling (hSampling := hSampling)
    (B := B) (U := U) (b := b) (hR := hR) (hσ := hσ) (S := S) (M₀ := M₀)
    (hsize := hsize) (p := inputParameter) hq he hE hdimSmall
    (hvars.trans hpq) (fun j => (hI j).trans hpq) (fun j => (hn₁ j).trans hpq)
    (fun j => (hJ j).trans hpq) (hcutoff.trans (Real.exp_le_exp.mpr hpq))
    (hS₁.trans (Real.exp_le_exp.mpr hsq)) hEq (fun j => (hRadius j).trans_le hradius.2.2.1) hBlocks
  refine ⟨witnesses, hBounds, ?_⟩
  intro hb o Q _ bW d _ _
  have hRinv (j : Fin m) : (R j)⁻¹ ≤ Real.exp sourceParameter := by
    rw [hRadius j]
    exact hradius.2.2.2.trans_le (Real.exp_le_exp.mpr (hLq.trans hqSource))
  exact hgeometry hb o bW d (fun _ => chartCap) (fun _ => chartCap)
    hforward (fun j => ⟨(mixedDensityCovolumeRatio_pos _ _).le, hvolume j⟩)
    (fun _ => Real.exp_le_exp.mpr (hcq.trans hqSource))
    (fun _ => Real.exp_le_exp.mpr (hcq.trans hqSource)) hRinv hσ1 geometryQ hQsite
    (fun _ => Real.exp c) (fun _ => (Real.exp_pos c).le) hinverse (fun j => (hRadius j).trans_le (hsmall j))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

noncomputable def allocatedGeometricSourceBudget {A : Type*} [Semiring A]
    (m : ℕ) (p c e E : A) : A :=
  let q := allocatedGeometrySourceInput m p c e E
  q + siteSourceParameter m q + siteSourceMaskLog m q

theorem allocatedGeometricSourceBudget_controls (m : ℕ) {p c e E : ℝ}
    (hp : 0 ≤ p) (hc : 0 ≤ c) (he : 0 ≤ e) (hE : 0 ≤ E) :
    let q := allocatedGeometrySourceInput m p c e E
    let B := allocatedGeometricSourceBudget m p c e E
    0 ≤ q ∧ q ≤ B ∧ siteSourceParameter m q ≤ B ∧ siteSourceMaskLog m q ≤ B := by
  have hscaleInput := (allocatedGeometryInput_bounds m hp hc (le_refl 0) hE).1
  have hscale := (allocatedSiteSourceLog_bounds m hscaleInput he hE).1
  have hq : 0 ≤ allocatedGeometrySourceInput m p c e E :=
    (allocatedGeometryInput_bounds m hp hc hscale hE).1
  have hparameter := (siteSourceParameter_bounds m hq).1
  have hmask := siteSourceMaskLog_nonneg m hq
  dsimp only [allocatedGeometricSourceBudget]
  exact ⟨hq, by linarith, by linarith, by linarith⟩

theorem map_allocatedGeometricSourceBudget {A B : Type*} [Semiring A] [Semiring B]
    (f : A →+* B) (m : ℕ) (p c e E : A) :
    f (allocatedGeometricSourceBudget m p c e E) =
      allocatedGeometricSourceBudget m (f p) (f c) (f e) (f E) := by
  simp [map_ofNat, allocatedGeometricSourceBudget, allocatedGeometrySourceInput, allocatedGeometryInput,
    allocatedIdealCoverPrimitiveLog, allocatedIdealCoverInputLog, allocatedSiteCoefficientLog,
    siteSourceParameter, siteSourceMaskLog, canonicalScalarSourceLog,
    allocatedSiteScaleLog, allocatedSiteScaleNumeric, allocatedSiteKernelMaskLog,
    allocatedComparisonDimension, allocatedIdealScaleLog, allocatedIdealScaleInput,
    allocatedPhysicalIdealLengthEnvelope, allocatedTestLengthEnvelope, allocatedJointLengthEnvelope,
    allocatedTestEnvelope, allocatedFrontEnvelope, allocatedAccuracyEnvelope, allocatedTupleEnvelope,
    allocatedKernelEnvelope, allocatedIdealMeshEnvelope, allocatedIdealGridEnvelope,
    allocatedIdealRadiusEnvelope, allocatedProxyLipEnvelope, allocatedIdealLipEnvelope,
    allocatedSupportEnvelope, allocatedDensityEnvelope, kernelOutputEnvelope,
    kernelGeometryEnvelope, kernelInverseEnvelope]

theorem exists_allocatedGeometricSourceBudget_bound (m : ℕ) :
    ∃ a : ℕ, 2 ≤ a ∧ ∀ p : ℝ, 0 ≤ p → allocatedGeometricSourceBudget m p p p p ≤ (p + a) ^ a := by
  let poly : Polynomial ℕ := allocatedGeometricSourceBudget m Polynomial.X Polynomial.X Polynomial.X Polynomial.X
  obtain ⟨a, ha, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨a, ha, ?_⟩
  intro p hp
  have heval : poly.eval₂ (Nat.castRingHom ℝ) p = allocatedGeometricSourceBudget m p p p p := by
    simpa only [poly, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X] using
      map_allocatedGeometricSourceBudget (Polynomial.eval₂RingHom (Nat.castRingHom ℝ) p)
        m Polynomial.X Polynomial.X Polynomial.X Polynomial.X
  exact heval ▸ hbound p hp

end Erdos3.VectorPolynomial

end

end OAI
