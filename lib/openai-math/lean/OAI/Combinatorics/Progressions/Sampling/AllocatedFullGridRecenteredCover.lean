import OAI.Combinatorics.Progressions.Estimates.AllocatedOriginalExponentialCover
import OAI.Combinatorics.Progressions.Sampling.AllocatedFullGridRefinedMixture

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (rowSets : Fin m → Finset (Finset α))
local notation "O" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))
variable {D : ℝ}
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
local notation "selected" => (fun _ : {a // allocatedGridAxis (I := I) U b S.value a} => True)
local notation "W" => allocatedFullGridSiteWindow B U b S rowSets D
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  (rowSets (Sigma.fst (Subtype.val a)) : Type uα)) → ℝ) → ℝ)
variable [NeZero q]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "laws" => allocatedSupportedGridJetPMF B U b hR hσ S x rows q (principalResidueLabel q y₀) hcell
local notation "density" => allocatedSupportedGridJetDensity B U b hR hσ S x rows q (principalResidueLabel q y₀) hcell
local notation "weight" => allocatedGridWindowWeight B U b S O selected W laws
local notation "χ" => allocatedChartGridMultiplier B U b S O hb o bW d weight
local notation "profile" => allocatedWholeMaskedGridlessProfile B U b S x y₀ rows hb o bW d q f
local notation "residue" => fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q

variable (CM Cf : ℝ≥0) (hCM : 1 ≤ (CM : ℝ)) (hfb : ∀ v, |f v| ≤ Cf)
variable (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x (fun j => (Subtype.val : rowSets j → Finset α)) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀) (fun j => (Subtype.val : rowSets j → Finset α)) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x (fun j => (Subtype.val : rowSets j → Finset α)) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀) (fun j => (Subtype.val : rowSets j → Finset α)) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ CM)

local notation "amplitude" => Real.toNNReal (coefficientDeckPeriodCap O Q q) *
  CM ^ Fintype.card (LayerSamplerAxis I n) * Cf

include hCM hfb hm in
theorem allocatedFullGridConditionalError_le_probability_majorant
    (hD : AllocatedComparisonDimensions (G := G) B α (fun j : Fin m => (rowSets j : Type uα)) D)
    (hσ1 : ∀ a : {a // grid a}, σ (allocatedGridIntegerAxis B U b S a).1 ≤ 1)
    (hrows : ∀ j t, t ∈ rowSets j → t.card ≤ j.val + 1)
    (hperiod : ∀ j, integerScalarLattice (O j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (e : {a // grid a} → ScalarSiteExpansion.{uα,uα} (Finset α))
    (hsupport : ∀ a i s r v, Real.exp (allocatedInactiveSupportLog D) ≤ |v| → (e a).factor i s r v = 0)
    {δ : ℝ} (hδ : 0 < δ)
    (he : ∀ z : AllocatedFrozenJetRows B U b S O,
      ‖(allocatedFullGridNaturalVolume B U b S rowSets : ℂ) *
        ((∏ a, (laws a (z a)).toReal : ℝ) : ℂ) -
        allocatedFullGridSiteApproximation B U b S rowSets e z‖ ≤ allocatedFullGridPointTolerance D δ)
    (C V : Fin m → ℝ≥0)
    (hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (y : EuclideanJetLayers U O) :
    ‖allocatedSelectedConditionalError B U b hR hσ S x (rows) hb o bW d q y₀ hcell
      selected f (allocatedFullGridSelectedApproximation B U b S rowSets e)
      (allocatedFullGridNaturalVolume B U b S rowSets) y‖ ≤
    allocatedProbabilityMajorant B U b S o
      (allocatedGridWindowPMF B U b S O selected W laws
        (fun a _ => allocatedFullGridSiteWindow_nonempty B U b S rowSets D a))
      (Real.toNNReal δ) amplitude d y := by
  have hpoint := allocatedFullGridSelected_error B U b hR hσ S rowSets q
    (principalResidueLabel q y₀) hcell x e he
  have hzero := allocatedFullGridSelected_zero B U b hR hσ S rowSets q
    (principalResidueLabel q y₀) hcell x e hD hσ1 hrows hsupport
  apply allocatedSelectedConditionalError_le_probability_majorant B U b hR hσ S x (rows)
    hb o bW d q y₀ hcell selected W f CM Cf hCM hfb hm hperiod
    (allocatedFullGridSelectedApproximation B U b S rowSets e)
    (allocatedFullGridNaturalVolume_pos B U b hR S rowSets)
    (allocatedFullGridPointTolerance_pos hδ).le hzero hpoint
    (fun a _ => allocatedFullGridSiteWindow_nonempty B U b S rowSets D a) (Real.toNNReal δ) _
    C V hC hV y
  simpa only [ite_true, Real.coe_toNNReal δ hδ.le] using
    allocatedFullGridSiteWindow_error_budget B U b hR S rowSets hD hδ

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type uG} [Fintype G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

variable (q : ℕ) [NeZero q]

variable {r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod q}
variable (w : AllocatedFullGridResidueWitness (dim := dim) B U b S q r)

def AllocatedFullGridResidueSampling (δ : ℝ) : Prop :=
  ∀ {K : ℕ}, AllocatedBooleanRowsSampling.{uX,uJ,uG,uI,uB,uQ} m dim K (rowTypes) (rows) → ∀
    (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type uQ} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d]
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

    (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset (Fin dim) // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)
    (CM Cf : ℝ≥0) (_hCM : 1 ≤ (CM : ℝ)) (_hfb : ∀ v, |f v| ≤ Cf)
    (_hmask : ∀ j z, 0 ≤ allocatedIntegerKernelMask (O := rowTypes) B U b S x
    (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix (O := rowTypes) B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) w.representative)
      (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) w.representative)) q) z ∧
  allocatedIntegerKernelMask (O := rowTypes) B U b S x
    (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix (O := rowTypes) B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) w.representative)
      (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) w.representative)) q) z ≤ CM)
    (_hperiod : ∀ j, integerScalarLattice (rowTypes j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    {X : Type uX} [Fintype X] [DecidableEq X]
    {P₀ : ℝ} (_hP : 0 ≤ P₀) (_hn : (Fintype.card X : ℝ) ≤ P₀)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P₀)
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
    {R₁ S₀ ρ ε : ℝ} (_hS : 0 ≤ S₀) (_hSP : S₀ ≤ Real.exp P₀) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P₀) (_hεP : 1 / ε ≤ Real.exp P₀)
    (_hstride : ∀ x, (stride x : ℝ) ≤ S₀)
    (H : X → ℝ) (_hsize : ∀ x, Real.exp ((P₀ + K) ^ K) ≤ H x)
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H R₁ (U j) (p j))
    (_hR : Real.exp ((P₀ + K) ^ K) ≤ R₁)
    (cells : Finset (ColumnResiduePattern (Option (Fin dim)) X stride)) (_hcells : cells.Nonempty)
    (W : Option (Fin dim) × X → ℝ) (_hW : ∀ z, 0 < W z) (_hwidth : ∀ z, ρ * H z.2 ≤ W z)
    {δFourier LFourier : ℝ} (_hδFourier : 0 < δFourier) (_hLFourier : 0 ≤ LFourier)
    (_hamb : (Fintype.card (JetAmbientIndex (rowTypes) J) : ℝ) ≤ LFourier)
    (_hδL : δFourier⁻¹ ≤ Real.exp LFourier),
    let A := Real.toNNReal (coefficientDeckPeriodCap (rowTypes) Q q) *
      CM ^ Fintype.card (LayerSamplerAxis I n) * Cf
    (allocatedErrorKernelLip B U b S (O := rowTypes) (Real.toNNReal δ) A C V : ℝ) ≤ Real.exp LFourier →
    Real.exp ((2 * LFourier + 2) ^ 4) ≤ Real.exp P₀ →
    Real.exp (2 * LFourier * (2 * LFourier + 2) ^ 4) *
      allocatedErrorKernelCap B U b S (O := rowTypes) (Real.toNNReal δ) A V ≤ Real.exp P₀ →
    let error := allocatedSelectedConditionalError (O := rowTypes) B U b hR hσ S x (rows)
      hb o bW d q w.representative w.positive (fun _ => True) f
      (allocatedFullGridSelectedApproximation B U b S rowSets w.expansion)
      (allocatedFullGridNaturalVolume B U b S rowSets)
    let mass := δ * A *
      (2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, (rowTypes) a.1)
    ∃ _hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells W z,
      selectedResidueDensityMass stride cells W
        (fun z => ‖error (physicalCubeRowSample (O := rowTypes) U d (rows) p hmp (standardPhysicalCubeOutput z))‖)
        ≤ mass + 2 * δFourier + ε

theorem allocatedFullGridResidueSampling_of_approximation {D δ : ℝ}
    (hD : AllocatedComparisonDimensions (G := G) B (Fin dim)
      (fun j : Fin m => (boundedBooleanJetRows (Fin dim) (j.val + 1) : Type)) D)
    (hσ1 : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a},
      σ (allocatedGridIntegerAxis B U b S a).1 ≤ 1)
    (hδ : 0 < δ)
    (hsupport : ∀ a i s r v, Real.exp (allocatedInactiveSupportLog D) ≤ |v| →
      (w.expansion a).factor i s r v = 0)
    (he : ∀ (x : G → IntegerScalarCubeBox (Fin dim) S.value)
        (z : AllocatedFrozenJetRows B U b S (rowTypes)),
      ‖(allocatedFullGridNaturalVolume B U b S rowSets : ℂ) *
        ((∏ a, (allocatedSupportedGridJetPMF B U b hR hσ S x (rows) q
          (principalResidueLabel q w.representative) w.positive a (z a)).toReal : ℝ) : ℂ) -
        allocatedFullGridSiteApproximation B U b S rowSets w.expansion z‖ ≤
          allocatedFullGridPointTolerance D δ) :
    AllocatedFullGridResidueSampling.{uG,uI,uB,uJ,uQ,uX} B U b hR hσ S q w δ := by
  unfold AllocatedFullGridResidueSampling
  intro K hSampling x hb o Q _ bW d _ _ f CM Cf hCM hfb hmask hperiod C V hC hV
    X _ _ P₀ hP₀ hn hdim _ _ _ μ _ _ ν _ _ p hp hmp stride hs R₁ S₀ ρ ε
    hS hSP hρ hε hρP hεP hstride H hsize₁ hrank hR₁ cells hcells W hW hwidth
    δFourier LFourier hδFourier hLFourier hamb hδL A hLip hfreqP hcoeffP error mass
  let laws := allocatedSupportedGridJetPMF (O := rowTypes) B U b hR hσ S x (rows)
    q (principalResidueLabel q w.representative) w.positive
  let aux := allocatedGridWindowPMF B U b S (rowTypes) (fun _ => True)
    (allocatedFullGridSiteWindow B U b S rowSets D) laws
    (fun a _ => allocatedFullGridSiteWindow_nonempty B U b S rowSets D a)
  have hrows (j : Fin m) (t : Finset (Fin dim)) (ht : t ∈ rowSets j) : t.card ≤ j.val + 1 :=
    (mem_boundedBooleanJetRows (j.val + 1) t).mp ht
  have hδcast : (Real.toNNReal δ : ℝ) = δ := Real.coe_toNNReal δ hδ.le
  have herror := allocatedFullGridConditionalError_le_probability_majorant B U b hR hσ S x rowSets
    hb o bW d q w.representative w.positive f CM Cf hCM hfb hmask hD hσ1 hrows hperiod
    w.expansion hsupport hδ (he x) C V hC hV
  dsimp only [AllocatedBooleanRowsSampling] at hSampling
  dsimp only at hLip hcoeffP hamb
  obtain ⟨hZ, hbound⟩ := @hSampling X _ _ J _ P₀ hP₀ hn hdim U _ _ _ μ _ _ ν _ _
    p hp hmp d _ stride hs R₁ S₀ ρ ε hS hSP hρ hε hρP hεP hstride H hsize₁ hrank hR₁
    cells hcells W hW hwidth G _ I _ n B _ b R σ S o aux _ hb Q _ bW
    (Real.toNNReal δ) A C V hC hV δFourier LFourier hδFourier hLFourier hamb hδL hLip hfreqP hcoeffP
  refine ⟨hZ, ?_⟩
  apply (selectedResidueDensityMass_mono stride cells W hW hZ
    (fun z => herror (physicalCubeRowSample (O := rowTypes) U d (rows) p hmp (standardPhysicalCubeOutput z)))).trans
  simpa only [hδcast] using hbound

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "ig" => allocatedGridIntegerAxis B U b S

theorem exists_allocated_full_grid_residue_sampling
    {D P p v δ E : ℝ}
    (hD : AllocatedComparisonDimensions (G := G) B (Fin dim) (fun j : Fin m => (rowSets j : Type)) D)
    (hα : Fintype.card (Fin dim) ≤ m + 1) (hP : 1 ≤ P) (hp : 0 ≤ p) (hv : 0 ≤ v)
    (hPp : P ≤ Real.exp p) (hq : 0 < q) (hqv : (q : ℝ) ≤ Real.exp v)
    (hδ : 0 < δ) (hE : 0 ≤ E) (hδE : δ⁻¹ ≤ Real.exp E)
    (hsize : (Fintype.card (Fin dim) + 1) * q ≤ S.value)
    (hgamma : ∀ a : gridAxes, principalProfileSize (R (ig a).1)
      (Finset.card (layerIntegerPrincipalSlots (G := G) B (ig a).1 (ig a).2)) ≤ 1)
    (hσ1 : ∀ a : gridAxes, σ (ig a).1 ≤ 1)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hcP : scalarCubePrimitiveEnvelope Empty L 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope (Fin dim) L 1 0 q ≤ P)
    (hrows : ∀ j t, t ∈ rowSets j → t.card ≤ j.val + 1)
    (hB : ∀ a : gridAxes, max
      (positiveModerateSpectrumBlockCount (ig a).1.val (rowSets (ig a).1).card
        ((layerTailDegree m + 2) * (rowSets (ig a).1).card))
      (uniformSpectrumBlockCount (ig a).1.val (rowSets (ig a).1).card
        (((ig a).1.val + 1) * (rowSets (ig a).1).card)) ≤
      Fintype.card (B ⟨(ig a).1, Sum.inr (ig a).2⟩)) :
    let O := allocatedMixedJointSiteLog m D p v (E + allocatedFullGridWindowLog D)
    ∃ W : (r : AllocatedPositiveResidue (dim := dim) B U b S q) →
        AllocatedFullGridResidueWitness (dim := dim) B U b S q r.val,
      (∀ r a, ((W r).expansion a).Bounds (Real.exp O) (Real.exp O) (Real.exp O)
        ⟨Real.exp O, Real.exp_nonneg _⟩ (Real.exp (allocatedInactiveSupportLog D))) ∧
      ∀ r, AllocatedFullGridResidueSampling.{uG,uI,uB,uJ,uQ,uX} B U b hR hσ S q (W r) δ := by
  obtain ⟨W, hW⟩ := exists_allocated_full_grid_residue_witnesses B U b hR hσ S q
    hD hα hP hp hv hPp hq hqv hδ hE hδE hsize hgamma hσ1 L hL hcP hsP hrows hB
  refine ⟨W, fun r => (hW r).1, ?_⟩
  intro r
  exact allocatedFullGridResidueSampling_of_approximation B U b hR hσ S q (W r)
    hD hσ1 hδ (fun a => ((hW r).1 a).support) (hW r).2

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type uG} [Fintype G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

variable (q : ℕ) [NeZero q]

variable (δ : ℝ)
variable (witnesses : (r : AllocatedPositiveResidue (dim := dim) B U b S q) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S q r.val)
variable (hWitness : ∀ r, AllocatedFullGridResidueSampling.{uG,uI,uB,uJ,uQ,uX}
  B U b hR hσ S q (witnesses r) δ)

include hWitness in
omit [NeZero q] in
theorem allocated_full_grid_reference_envelope_error :
  ∀ {K : ℕ}, AllocatedBooleanRowsSampling.{uX,uJ,uG,uI,uB,uQ} m dim K (rowTypes) (rows) → ∀
    (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type uQ} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d]
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

    (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset (Fin dim) // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)
    (CM Cf : ℝ≥0) (_hCM : 1 ≤ (CM : ℝ)) (_hfb : ∀ v, |f v| ≤ Cf)
    (_hmask : ∀ y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim)
      (allocatedPrincipalSides B U b S), ∀ j z, 0 ≤ allocatedIntegerKernelMask (O := rowTypes) B U b S x
    (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix (O := rowTypes) B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask (O := rowTypes) B U b S x
    (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix (O := rowTypes) B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ CM)
    (_hperiod : ∀ j, integerScalarLattice (rowTypes j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    {X : Type uX} [Fintype X] [DecidableEq X]
    {P₀ : ℝ} (_hP : 0 ≤ P₀) (_hn : (Fintype.card X : ℝ) ≤ P₀)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P₀)
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
    {R₁ S₀ ρ ε : ℝ} (_hS : 0 ≤ S₀) (_hSP : S₀ ≤ Real.exp P₀) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P₀) (_hεP : 1 / ε ≤ Real.exp P₀)
    (_hstride : ∀ x, (stride x : ℝ) ≤ S₀)
    (N : X → ℕ) (_hsize : ∀ x, Real.exp ((P₀ + K) ^ K) ≤ (N x : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) R₁ (U j) (p j))
    (_hR : Real.exp ((P₀ + K) ^ K) ≤ R₁)
    {δFourier LFourier : ℝ} (_hδFourier : 0 < δFourier) (_hLFourier : 0 ≤ LFourier)
    (_hamb : (Fintype.card (JetAmbientIndex (rowTypes) J) : ℝ) ≤ LFourier)
    (_hδL : δFourier⁻¹ ≤ Real.exp LFourier),
    let A := Real.toNNReal (coefficientDeckPeriodCap (rowTypes) Q q) *
      CM ^ Fintype.card (LayerSamplerAxis I n) * Cf
    (allocatedErrorKernelLip B U b S (O := rowTypes) (Real.toNNReal δ) A C V : ℝ) ≤ Real.exp LFourier →
    Real.exp ((2 * LFourier + 2) ^ 4) ≤ Real.exp P₀ →
    Real.exp (2 * LFourier * (2 * LFourier + 2) ^ 4) *
      allocatedErrorKernelCap B U b S (O := rowTypes) (Real.toNNReal δ) A V ≤ Real.exp P₀ →
    let mass := δ * A *
      (2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, (rowTypes) a.1)
    let envelope := referenceJetEnvelopeWidths (q := dim) stride (trimmedSpatialRootScale ρ N stride)
    ∀ (base : X → ℤ) (cell : ColumnResiduePattern (Option (Fin dim)) X stride)
      (r : AllocatedPositiveResidue (dim := dim) B U b S q),
    let error := allocatedSelectedConditionalError (O := rowTypes) B U b hR hσ S x (rows)
      hb o bW d q (witnesses r).representative (witnesses r).positive (fun _ => True) f
      (allocatedFullGridSelectedApproximation B U b S rowSets (witnesses r).expansion)
      (allocatedFullGridNaturalVolume B U b S rowSets)
    (0 < ∑' z, selectedResidueSmoothWeight stride {cell} envelope z) ∧
      selectedResidueDensityMass stride {cell} envelope
        (fun z => ‖error (physicalCubeRowSample (O := rowTypes) U d (rows) p hmp
          (translatePhysicalCube base (standardPhysicalCubeOutput z)))‖)
        ≤ mass + 2 * δFourier + ε := by
  intro K hSampling x hb o Q _ bW d _ _ f CM Cf hCM hfb hmask hperiod C V hC hV
    X _ _ P₀ hP₀ hn hdim _ _ _ μ _ _ ν _ _ p hp hmp stride hs R₁ S₀ ρ ε
    hS hSP hρ hε hρP hεP hstride N hsize₁ hrank hR₁
    δFourier LFourier hδFourier hLFourier hamb hδL A hLip hfreqP hcoeffP
    mass envelope base cell r error
  have hN (t : X) : (0 : ℝ) < N t := (Real.exp_pos _).trans_le (hsize₁ t)
  have hEnvelope (z : Option (Fin dim) × X) : 0 < envelope z := by
    change 0 < referenceJetEnvelopeWidths stride (trimmedSpatialRootScale ρ N stride) z
    rw [referenceJetEnvelopeWidths_trimmed stride N hs ρ z]
    exact mul_pos (mul_pos (by norm_num) hρ) (hN z.2)
  have hWidth (z : Option (Fin dim) × X) : ρ * (N z.2 : ℝ) ≤ envelope z := by
    change ρ * (N z.2 : ℝ) ≤ referenceJetEnvelopeWidths stride (trimmedSpatialRootScale ρ N stride) z
    rw [referenceJetEnvelopeWidths_trimmed stride N hs ρ z]
    nlinarith [mul_pos hρ (hN z.2)]
  have hp' (j : Fin m) : DegreeLE (1 : X → ℕ) (j.val + 1)
      (translate (fun t => (base t : ℝ)) (p j)) :=
    degreeLE_translate (1 : X → ℕ) (fun _ => by norm_num) _ _ (hp j)
  have hrank' (j : Fin m) : HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) R₁
      (U j) (translate (fun t => (base t : ℝ)) (p j)) :=
    (hasLayerSamplingRank_translate_iff _ _ _ _ _ _ (hp j)).mpr (hrank j)
  have hc := @hWitness r
  dsimp only [AllocatedFullGridResidueSampling] at hc
  obtain ⟨hZ, hbound⟩ := @hc K hSampling x hb o Q _ bW d _ _ f CM Cf hCM hfb
    (hmask (witnesses r).representative) hperiod C V hC hV
    X _ _ P₀ hP₀ hn hdim _ _ _ μ _ _ ν _ _
    (fun j => translate (fun t => (base t : ℝ)) (p j)) hp'
    (fun j => coefficients_translate_mem (U j) (fun t => (base t : ℝ)) (p j) (hmp j))
    stride hs R₁ S₀ ρ ε hS hSP hρ hε hρP hεP hstride (fun t => (N t : ℝ))
    hsize₁ hrank' hR₁ {cell} (Finset.singleton_nonempty cell) envelope hEnvelope hWidth
    δFourier LFourier hδFourier hLFourier hamb hδL hLip hfreqP hcoeffP
  refine ⟨hZ, ?_⟩
  refine (le_of_eq ?_).trans hbound
  apply congrArg (selectedResidueDensityMass stride {cell} envelope)
  funext z
  exact congrArg (fun v => ‖error v‖)
    (physicalCubeRowSample_translate U d (rows) p hmp base (standardPhysicalCubeOutput z)).symm

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type uG} [Fintype G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

variable (q : ℕ) [NeZero q]

variable (δ : ℝ)
variable (witnesses : (r : AllocatedPositiveResidue (dim := dim) B U b S q) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S q r.val)
variable (hWitness : ∀ r, AllocatedFullGridResidueSampling.{uG,uI,uB,uJ,uQ,uX}
  B U b hR hσ S q (witnesses r) δ)

include hWitness in
theorem allocated_full_grid_sampled_error :
  ∀ {K : ℕ}, AllocatedBooleanRowsSampling.{uX,uJ,uG,uI,uB,uQ} m dim K (rowTypes) (rows) → ∀
    (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type uQ} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d]
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

    (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset (Fin dim) // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)
    (CM Cf : ℝ≥0) (_hCM : 1 ≤ (CM : ℝ)) (_hfb : ∀ v, |f v| ≤ Cf)
    (_hmask : ∀ y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim)
      (allocatedPrincipalSides B U b S), ∀ j z, 0 ≤ allocatedIntegerKernelMask (O := rowTypes) B U b S x
    (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix (O := rowTypes) B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask (O := rowTypes) B U b S x
    (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix (O := rowTypes) B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ CM)
    (_hperiod : ∀ j, integerScalarLattice (rowTypes j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    {X : Type uX} [Fintype X] [DecidableEq X]
    {P₀ : ℝ} (_hP : 0 ≤ P₀) (_hn : (Fintype.card X : ℝ) ≤ P₀)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P₀)
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
    {R₁ S₀ ρ ε : ℝ} (_hS : 0 ≤ S₀) (_hSP : S₀ ≤ Real.exp P₀) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P₀) (_hεP : 1 / ε ≤ Real.exp P₀)
    (_hstride : ∀ x, (stride x : ℝ) ≤ S₀)
    (H : X → ℝ) (_hsize : ∀ x, Real.exp ((P₀ + K) ^ K) ≤ H x)
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H R₁ (U j) (p j))
    (_hR : Real.exp ((P₀ + K) ^ K) ≤ R₁)
    (cells : Finset (ColumnResiduePattern (Option (Fin dim)) X stride)) (_hcells : cells.Nonempty)
    (W : Option (Fin dim) × X → ℝ) (hW : ∀ z, 0 < W z) (_hwidth : ∀ z, ρ * H z.2 ≤ W z)
    {δFourier LFourier : ℝ} (_hδFourier : 0 < δFourier) (_hLFourier : 0 ≤ LFourier)
    (_hamb : (Fintype.card (JetAmbientIndex (rowTypes) J) : ℝ) ≤ LFourier)
    (_hδL : δFourier⁻¹ ≤ Real.exp LFourier),
    let A := Real.toNNReal (coefficientDeckPeriodCap (rowTypes) Q q) *
      CM ^ Fintype.card (LayerSamplerAxis I n) * Cf
    (allocatedErrorKernelLip B U b S (O := rowTypes) (Real.toNNReal δ) A C V : ℝ) ≤ Real.exp LFourier →
    Real.exp ((2 * LFourier + 2) ^ 4) ≤ Real.exp P₀ →
    Real.exp (2 * LFourier * (2 * LFourier + 2) ^ 4) *
      allocatedErrorKernelCap B U b S (O := rowTypes) (Real.toNNReal δ) A V ≤ Real.exp P₀ →
    let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let target := allocatedSupportedFullGridResidueProfile B U b hR hσ S q x hb o bW d f witnesses
    let error := fun y : EuclideanJetLayers U (rowTypes) =>
      law.complexMean (fun y₀ =>
        (allocatedWholeMaskedCoveredProfile (O := rowTypes) B U b hR hσ S x (rows) hb o bW d y₀ q f y : ℂ)) -
      (law.fiberLaw (principalResidueLabel q)).complexMean (fun r => target r y)
    let mass := δ * A *
      (2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, (rowTypes) a.1)
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells W z,
      selectedResidueDensityMass stride cells W
        (fun z => ‖error (physicalCubeRowSample (O := rowTypes) U d (rows) p hmp (standardPhysicalCubeOutput z))‖)
        ≤ mass + 2 * δFourier + ε ∧
      ∀ φ : (Option (Fin dim) × X → ℤ) → ℂ, (∀ z, ‖φ z‖ ≤ 1) →
        ‖∑' z, ((selectedResidueSmoothPMF stride cells W hW hZ z).toReal : ℂ) *
          (error (physicalCubeRowSample (O := rowTypes) U d (rows) p hmp (standardPhysicalCubeOutput z)) * φ z)‖
          ≤ mass + 2 * δFourier + ε := by
  intro K hSampling x hb o Q _ bW d _ _ f CM Cf hCM hfb hmask hperiod C V hC hV
    X _ _ P₀ hP₀ hn hdim _ _ _ μ _ _ ν _ _ p hp hmp stride hs R₁ S₀ ρ ε
    hS hSP hρ hε hρP hεP hstride H hsize₁ hrank hR₁ cells hcells W hW hwidth
    δFourier LFourier hδFourier hLFourier hamb hδL A hLip hfreqP hcoeffP law target error mass
  let sample := fun z : Option (Fin dim) × X → ℤ =>
    physicalCubeRowSample (O := rowTypes) U d (rows) p hmp (standardPhysicalCubeOutput z)
  let source := fun (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim)
      (allocatedPrincipalSides B U b S)) (z : Option (Fin dim) × X → ℤ) =>
    (allocatedWholeMaskedCoveredProfile (O := rowTypes) B U b hR hσ S x (rows) hb o bW d y₀ q f (sample z) : ℂ)
  let targetSample := fun r (z : Option (Fin dim) × X → ℤ) => target r (sample z)
  have hlocal (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod q)
      (hr : 0 < law.mass (Finset.univ.filter (fun y => principalResidueLabel q y = r))) :
      ∃ _hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells W z,
        selectedResidueDensityMass stride cells W
          (fun z => ‖(law.condition _ hr).complexMean (fun y => source y z) - targetSample r z‖)
          ≤ mass + 2 * δFourier + ε := by
    let rr : AllocatedPositiveResidue (dim := dim) B U b S q := ⟨r, hr⟩
    have hc := @hWitness rr
    dsimp only [AllocatedFullGridResidueSampling] at hc
    obtain ⟨hZ, hbound⟩ := @hc K hSampling x hb o Q _ bW d _ _ f CM Cf hCM hfb
      (hmask (witnesses rr).representative) hperiod C V hC hV
      X _ _ P₀ hP₀ hn hdim _ _ _ μ _ _ ν _ _ p hp hmp stride hs R₁ S₀ ρ ε
      hS hSP hρ hε hρP hεP hstride H hsize₁ hrank hR₁ cells hcells W hW hwidth
      δFourier LFourier hδFourier hLFourier hamb hδL hLip hfreqP hcoeffP
    refine ⟨hZ, ?_⟩
    have hid := allocatedSupportedFullGridResidueProfile_error B U b hR hσ S q x hb o bW d f witnesses rr
    have hfun :
        (fun z => ‖(law.condition _ hr).complexMean (fun y => source y z) - targetSample r z‖) =
        (fun z => ‖allocatedSelectedConditionalError (O := rowTypes) B U b hR hσ S x (rows)
          hb o bW d q (witnesses rr).representative (witnesses rr).positive
          (fun _ => True) f
          (allocatedFullGridSelectedApproximation B U b S rowSets (witnesses rr).expansion)
          (allocatedFullGridNaturalVolume B U b S rowSets) (sample z)‖) := by
      funext z
      exact congrArg norm (congrFun hid (sample z))
    rw [hfun]
    exact hbound
  obtain ⟨r₀, hr₀⟩ := (law.fiberLaw (principalResidueLabel q)).exists_weight_pos
  rw [law.fiberLaw_weight_eq_mass] at hr₀
  obtain ⟨hZ, _⟩ := hlocal r₀ hr₀
  have heach r hr := (hlocal r hr).choose_spec
  refine ⟨hZ, ?_, ?_⟩
  · exact selectedResidue_supported_fiber_error_uniform law (principalResidueLabel q)
      stride cells W hW hZ source targetSample heach
  · intro φ hφ
    have h := selectedResidue_supported_fiber_test_error law (principalResidueLabel q)
      stride cells W hW hZ source targetSample (fun _ => mass + 2 * δFourier + ε) heach φ hφ
    simpa only [FiniteProbabilityWeights.mean_const] using h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type uG} [Fintype G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

variable (q : ℕ) [NeZero q]

variable (δ : ℝ)
variable (witnesses : (r : AllocatedPositiveResidue (dim := dim) B U b S q) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S q r.val)
variable (hWitness : ∀ r, AllocatedFullGridResidueSampling.{uG,uI,uB,uJ,uQ,uX}
  B U b hR hσ S q (witnesses r) δ)

include hWitness in
theorem allocated_full_grid_reconstructed_comparison :
  ∀ {K : ℕ}, AllocatedBooleanRowsSampling.{uX,uJ,uG,uI,uB,uQ} m dim K (rowTypes) (rows) → ∀
    (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type uQ} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d]
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

    (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset (Fin dim) // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)
    (CM Cf : ℝ≥0) (_hCM : 1 ≤ (CM : ℝ)) (_hfb : ∀ v, |f v| ≤ Cf)
    (_hmask : ∀ y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim)
      (allocatedPrincipalSides B U b S), ∀ j z, 0 ≤ allocatedIntegerKernelMask (O := rowTypes) B U b S x
    (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix (O := rowTypes) B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask (O := rowTypes) B U b S x
    (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix (O := rowTypes) B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ CM)
    (modulus : ℕ) (_hdiv : modulus ∣ q)
    (_hperiod : ∀ j, integerScalarLattice (rowTypes j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    {X : Type uX} [Fintype X] [DecidableEq X]
    {P₀ : ℝ} (_hP : 0 ≤ P₀) (_hn : (Fintype.card X : ℝ) ≤ P₀)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P₀)
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
    {R₁ S₀ ρ ε : ℝ} (_hS : 0 ≤ S₀) (_hSP : S₀ ≤ Real.exp P₀) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P₀) (_hεP : 1 / ε ≤ Real.exp P₀)
    (_hstride : ∀ x, (stride x : ℝ) ≤ S₀)
    (N : X → ℕ) (_hsize : ∀ x, Real.exp ((P₀ + K) ^ K) ≤ (N x : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) R₁ (U j) (p j))
    (_hR : Real.exp ((P₀ + K) ^ K) ≤ R₁)
    {δFourier LFourier : ℝ} (_hδFourier : 0 < δFourier) (_hLFourier : 0 ≤ LFourier)
    (_hamb : (Fintype.card (JetAmbientIndex (rowTypes) J) : ℝ) ≤ LFourier)
    (_hδL : δFourier⁻¹ ≤ Real.exp LFourier),
    let A := Real.toNNReal (coefficientDeckPeriodCap (rowTypes) Q q) *
      CM ^ Fintype.card (LayerSamplerAxis I n) * Cf
    (allocatedErrorKernelLip B U b S (O := rowTypes) (Real.toNNReal δ) A C V : ℝ) ≤ Real.exp LFourier →
    Real.exp ((2 * LFourier + 2) ^ 4) ≤ Real.exp P₀ →
    Real.exp (2 * LFourier * (2 * LFourier + 2) ^ 4) *
      allocatedErrorKernelCap B U b S (O := rowTypes) (Real.toNNReal δ) A V ≤ Real.exp P₀ →
    let mass := δ * A *
      (2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, (rowTypes) a.1)
    ∀ (W : ℝ), 0 ≤ W →
    let H := trimmedSpatialRootScale ρ N stride
    let T := trimmedSpatialSlopeScale W ρ N stride
    let outputVolume := ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim) (H t) (T t) S.value i
    let point := physicalCubeRowSample (O := rowTypes) U d (rows) p hmp
    let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let target := allocatedSupportedFullGridResidueProfile B U b hR hσ S q x hb o bW d f witnesses
    ∀ (reference : (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod q) →
        PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
      (base : X → ℤ)
      (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
      (V₀ : Option (LayerSamplerVariables G I n B) × X → ℝ),
    (∀ z, 0 < V₀ z) → (0 < ∑' z, selectedResidueSmoothWeight stride cells V₀ z) →
    (∀ t, Fintype.card (Option (LayerSamplerVariables G I n B)) *
      allocatedPhysicalEntryBudget B U b S (fun _ => 0) ≤ H t) →
    (∀ t, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H t) →
    ∀ (weight : (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod q) →
        cells → (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) (Cweight Z : ℝ),
    0 ≤ Cweight → 0 < Z →
    (∀ r a v, v ∈ spatialWindow H 4 → ‖weight r a v‖ ≤ Cweight / outputVolume) →
    let reconstruct := fun r (a : cells) => physicalResidueReconstruction
      (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (reference r))
      (allocatedPhysicalCubeDirections B U b S x (reference r)) base
      (boundedColumnResidueRepresentative stride a.val) stride
    let factor := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / (S.value : ℝ)) ^ dim) ^ Fintype.card X
    ‖(law.complexMean (fun y => ∑ a : cells, (selectedResidueCellWeight stride cells V₀ a : ℂ) *
        ∑ v ∈ spatialWindow H 4, weight (principalResidueLabel q y) a v *
          (allocatedWholeMaskedCoveredProfile (O := rowTypes) B U b hR hσ S x (rows)
            hb o bW d y modulus f (point (reconstruct (principalResidueLabel q y) a v)) : ℂ)) -
      (law.fiberLaw (principalResidueLabel q)).complexMean (fun r =>
        ∑ a : cells, (selectedResidueCellWeight stride cells V₀ a : ℂ) *
          ∑ v ∈ spatialWindow H 4, weight r a v * target r (point (reconstruct r a v)))) / (Z : ℂ)‖ ≤
      (Cweight * factor * (mass + 2 * δFourier + ε)) / Z := by
  intro K hSampling x hb o Q _ bW d _ _ f CM Cf hCM hfb hmask modulus hdiv hperiod C V hC hV
    X _ _ P₀ hP₀ hn hdim _ _ _ μ _ _ ν _ _ p hp hmp stride hs R₁ S₀ ρ ε
    hS hSP hρ hε hρP hεP hstride N hsize₁ hrank hR₁
    δFourier LFourier hδFourier hLFourier hamb hδL A hLip hfreqP hcoeffP
    mass W hW H T outputVolume point law target reference base cells V₀ hV₀ hZ₀
    hrows hscale weight Cweight Z hCweight hZ hweight reconstruct factor
  have hperiod' (j : Fin m) : integerScalarLattice (rowTypes j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range :=
    (integerScalarLattice_nat_refinement (rowTypes j) hdiv).trans (hperiod j)
  have hEnvelope := allocated_full_grid_reference_envelope_error B U b hR hσ S q δ witnesses
    hWitness hSampling x hb o bW d f CM Cf hCM hfb hmask hperiod' C V hC hV
    hP₀ hn hdim μ ν p hp hmp stride hs hS hSP hρ hε hρP hεP hstride N hsize₁ hrank hR₁
    hδFourier hLFourier hamb hδL hLip hfreqP hcoeffP
  have hN (t : X) : 0 < N t := Nat.cast_pos.mp ((Real.exp_pos _).trans_le (hsize₁ t))
  have hscales (t : X) : 0 < H t ∧ 0 < T t := trimmedSpatial_scales_pos hW hρ N stride t (hN t) (hs t)
  have houtput : 0 < outputVolume := Finset.prod_pos (fun t _ => Finset.prod_pos (fun i _ =>
    physicalSpatialOutputScale_pos (Fin dim) (hscales t).1 (hscales t).2
      (Nat.cast_pos.mpr S.positive) i))
  have hbound := allocatedFullGridRefinedCover_selected_reconstruction_error
    B U b hR hσ S x hb o bW d modulus q hdiv hperiod f witnesses reference
    stride hs base cells V₀ hV₀ hZ₀ H (fun t => (hscales t).1) T
    (Nat.cast_pos.mpr S.positive).ne' (trimmedSpatial_scale_ratio hW N stride) houtput
    hrows hscale point weight hCweight hZ hweight (fun _ => mass + 2 * δFourier + ε)
    (fun a r => hEnvelope base _ r)
  simpa only [FiniteProbabilityWeights.mean_const] using hbound

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type uG} [Fintype G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

variable (q : ℕ) [NeZero q]

variable (δ : ℝ)
variable (witnesses : (r : AllocatedPositiveResidue (dim := dim) B U b S q) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S q r.val)
variable (hWitness : ∀ r, AllocatedFullGridResidueSampling.{uG,uI,uB,uJ,uQ,uX}
  B U b hR hσ S q (witnesses r) δ)

include hWitness in
theorem allocated_full_grid_reconstructed_primitive_comparison
    {p₁ w v E : ℝ} (hp₁ : 0 ≤ p₁) (hw : 0 ≤ w) (hv : 0 ≤ v) (hE : 0 ≤ E)
    (hdimSmall : dim ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p₁)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p₁) (hn₁ : ∀ j, (n j : ℝ) ≤ p₁)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p₁)
    (M₀ : ℕ) (hqM : q ≤ M₀ ^ (m + 1)) (hM₀ : (M₀ : ℝ) ≤ Real.exp p₁)
    (hS₁ : (S.value : ℝ) ≤ Real.exp p₁)
    (hδ : δ ≤ allocatedSitePrimitiveTolerance m p₁ w v E) (hEbudget : E + 4 ≤ p₁) :
  ∀ {K : ℕ}, AllocatedBooleanRowsSampling.{uX,uJ,uG,uI,uB,uQ} m dim K (rowTypes) (rows) → ∀
    (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type uQ} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d]
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

    (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset (Fin dim) // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)
    (CM Cf : ℝ≥0) (_hCM : 1 ≤ (CM : ℝ)) (_hfb : ∀ v, |f v| ≤ Cf)
    (_hCMexp : (CM : ℝ) ≤ Real.exp w) (_hCfexp : (Cf : ℝ) ≤ Real.exp v)
    (_hmask : ∀ y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim)
      (allocatedPrincipalSides B U b S), ∀ j z, 0 ≤ allocatedIntegerKernelMask (O := rowTypes) B U b S x
    (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix (O := rowTypes) B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask (O := rowTypes) B U b S x
    (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix (O := rowTypes) B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ CM)
    (modulus : ℕ) (_hdiv : modulus ∣ q)
    (_hperiod : ∀ j, integerScalarLattice (rowTypes j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hCexp : ∀ j, (C j : ℝ) ≤ Real.exp p₁) (_hVexp : ∀ j, (V j : ℝ) ≤ Real.exp p₁)
    {X : Type uX} [Fintype X] [DecidableEq X]
    {P₀ : ℝ} (_hP : 0 ≤ P₀) (_hn : (Fintype.card X : ℝ) ≤ P₀)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P₀)
    (_hbudget : allocatedSiteErrorFourierOutput m p₁ w v ≤ P₀)
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
    (N : X → ℕ) (_hsize : ∀ x, Real.exp ((P₀ + K) ^ K) ≤ (N x : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) R₁ (U j) (p j))
    (_hR : Real.exp ((P₀ + K) ^ K) ≤ R₁),
    ∀ (W : ℝ), 0 ≤ W →
    let H := trimmedSpatialRootScale ρ N stride
    let T := trimmedSpatialSlopeScale W ρ N stride
    let outputVolume := ∏ t, ∏ i, physicalSpatialOutputScale (Fin dim) (H t) (T t) S.value i
    let point := physicalCubeRowSample (O := rowTypes) U d (rows) p hmp
    let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let target := allocatedSupportedFullGridResidueProfile B U b hR hσ S q x hb o bW d f witnesses
    ∀ (reference : (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod q) →
        PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
      (base : X → ℤ)
      (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
      (V₀ : Option (LayerSamplerVariables G I n B) × X → ℝ),
    (∀ z, 0 < V₀ z) → (0 < ∑' z, selectedResidueSmoothWeight stride cells V₀ z) →
    (∀ t, Fintype.card (Option (LayerSamplerVariables G I n B)) *
      allocatedPhysicalEntryBudget B U b S (fun _ => 0) ≤ H t) →
    (∀ t, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H t) →
    ∀ (weight : (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod q) →
        cells → (X → (Unit ⊕ Fin dim) → ℤ) → ℂ) (Cweight Z : ℝ),
    0 ≤ Cweight → 0 < Z →
    (∀ r a v, v ∈ spatialWindow H 4 → ‖weight r a v‖ ≤ Cweight / outputVolume) →
    let reconstruct := fun r (a : cells) => physicalResidueReconstruction
      (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (reference r))
      (allocatedPhysicalCubeDirections B U b S x (reference r)) base
      (boundedColumnResidueRepresentative stride a.val) stride
    let factor := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / (S.value : ℝ)) ^ dim) ^ Fintype.card X
    ‖(law.complexMean (fun y => ∑ a : cells, (selectedResidueCellWeight stride cells V₀ a : ℂ) *
        ∑ v ∈ spatialWindow H 4, weight (principalResidueLabel q y) a v *
          (allocatedWholeMaskedCoveredProfile (O := rowTypes) B U b hR hσ S x (rows)
            hb o bW d y modulus f (point (reconstruct (principalResidueLabel q y) a v)) : ℂ)) -
      (law.fiberLaw (principalResidueLabel q)).complexMean (fun r =>
        ∑ a : cells, (selectedResidueCellWeight stride cells V₀ a : ℂ) *
          ∑ v ∈ spatialWindow H 4, weight r a v * target r (point (reconstruct r a v)))) / (Z : ℂ)‖ ≤
      (Cweight * factor * Real.exp (-E)) / Z := by
  intro K hSampling x hb o Q _ bW d _ _ f CM Cf hCM hfb hCMexp hCfexp hmask modulus hdiv hperiod C V hC hV
    hCexp hVexp X _ _ P₀ hP₀ hn hdim hbudget _ _ _ μ _ _ ν _ _ p hp hmp stride hs R₁ S₀ ρ
    hS hSP hρ hρP hstride N hsize₁ hrank hR₁ W hW H T outputVolume point law target
    reference base cells V₀ hV₀ hZ₀ hrows hscale weight Cweight Z hCweight hZ hweight reconstruct factor
  have hδnn : Real.toNNReal δ ≤ 1 := Real.toNNReal_le_one.mpr
    (hδ.trans (allocatedSitePrimitiveTolerance_le_one m hp₁ hw hv hE))
  have hrowdim : Fintype.card (Fin dim) ≤ m + 1 := by
    simpa only [Fintype.card_fin] using hdimSmall
  have hshare : (physicalIdealErrorShare E 1)⁻¹ ≤ Real.exp p₁ := by
    rw [physicalIdealErrorShare_inv]
    exact Real.exp_le_exp.mpr (by linarith)
  obtain ⟨hLF, hpP, hamb, hδL, hLip, hfreq, hcoeff⟩ :=
    allocatedSiteErrorPrimitive_fourier_budget B U b S (rows) hrowdim
      (fun _ => Subtype.val_injective) hb bW M₀ q hqM (Real.toNNReal δ) CM Cf C V
      hp₁ hw hv hvars hI hn₁ hJ hδnn hM₀ hS₁ hCexp hVexp hCMexp hCfexp hshare
  have heP := Real.exp_le_exp.mpr hbudget
  have hεP : 1 / physicalIdealErrorShare E 1 ≤ Real.exp P₀ := by
    simpa only [one_div] using hshare.trans (Real.exp_le_exp.mpr (hpP.trans hbudget))
  have hprevious := allocated_full_grid_reconstructed_comparison B U b hR hσ S q δ witnesses
    hWitness (K := K) hSampling
  have hbound := @hprevious x hb o Q _ bW d _ _ f CM Cf hCM hfb hmask modulus hdiv hperiod C V hC hV
    X _ _ P₀ hP₀ hn hdim _ _ _ μ _ _ ν _ _ p hp hmp stride hs R₁ S₀ ρ (physicalIdealErrorShare E 1)
    hS hSP hρ (physicalIdealErrorShare_pos E 1) hρP hεP hstride N hsize₁ hrank hR₁
    (physicalIdealErrorShare E 1) (allocatedSiteErrorFourierInput m p₁ w v)
    (physicalIdealErrorShare_pos E 1) hLF hamb hδL hLip (hfreq.trans heP) (hcoeff.trans heP)
    W hW reference base cells V₀ hV₀ hZ₀ hrows hscale weight Cweight Z hCweight hZ hweight
  have hmass := allocatedSiteSpatial_primitive_error_budget B U b (rows) hrowdim
    (fun _ => Subtype.val_injective) hb bW M₀ q hqM CM Cf C hp₁ hw hvars hI hn₁ hJ
    hM₀ hCexp hCMexp hCfexp hδ (le_refl (physicalIdealErrorShare E 1))
    (le_refl (physicalIdealErrorShare E 1))
  have hfactor : 0 ≤ factor := mul_nonneg
    (pow_nonneg (div_nonneg (by norm_num) smoothProbabilityProfile_pos_zero.le) _)
    (pow_nonneg (pow_nonneg (div_nonneg (by linarith) (Nat.cast_nonneg S.value)) _) _)
  exact hbound.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmass (mul_nonneg hCweight hfactor)) hZ.le)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

universe uG uI uB uJ uQ uX

attribute [local instance 2000] fullBooleanRowSetFintype

variable {m dim : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type uB)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin dim) (Fin.val j + 1))
local notation "rowTypes" => (fun j : Fin m => (rowSets j : Type))
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset (Fin dim)))

variable {X : Type uX} [Fintype X] [DecidableEq X]
variable (stride : X → ℕ) (hs : ∀ t, 0 < stride t) (modulus : ℕ) [NeZero modulus]
variable [NeZero (residueRefinedPeriod modulus stride)]
local notation "refined" => residueRefinedPeriod modulus stride

variable (δ : ℝ)
variable (witnesses : (r : AllocatedPositiveResidue (dim := dim) B U b S (residueRefinedPeriod modulus stride)) →
  AllocatedFullGridResidueWitness (dim := dim) B U b S (residueRefinedPeriod modulus stride) r.val)
variable (hWitness : ∀ r, AllocatedFullGridResidueSampling.{uG,uI,uB,uJ,uQ,uX}
  B U b hR hσ S (residueRefinedPeriod modulus stride) (witnesses r) δ)

include hWitness hs in
theorem allocated_full_grid_recentered_primitive_comparison
    {p₁ w v E : ℝ} (hp₁ : 0 ≤ p₁) (hw : 0 ≤ w) (hv : 0 ≤ v) (hE : 0 ≤ E)
    (hdimSmall : dim ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p₁)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p₁) (hn₁ : ∀ j, (n j : ℝ) ≤ p₁)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p₁)
    (M₀ : ℕ) (hqM : refined ≤ M₀ ^ (m + 1)) (hM₀ : (M₀ : ℝ) ≤ Real.exp p₁)
    (hS₁ : (S.value : ℝ) ≤ Real.exp p₁)
    (hδ : δ ≤ allocatedSitePrimitiveTolerance m p₁ w v E) (hEbudget : E + 4 ≤ p₁) :
  ∀ {K : ℕ}, AllocatedBooleanRowsSampling.{uX,uJ,uG,uI,uB,uQ} m dim K (rowTypes) (rows) → ∀
    (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    {Q : Fin m → Type uQ} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d]
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

    (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset (Fin dim) // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)
    (CM Cf : ℝ≥0) (_hCM : 1 ≤ (CM : ℝ)) (_hfb : ∀ v, |f v| ≤ Cf)
    (_hCMexp : (CM : ℝ) ≤ Real.exp w) (_hCfexp : (Cf : ℝ) ≤ Real.exp v)
    (_hmask : ∀ y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim)
      (allocatedPrincipalSides B U b S), ∀ j z, 0 ≤ allocatedIntegerKernelMask (O := rowTypes) B U b S x
    (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j refined
    (integerResidueMatrix (allocatedNonkernelJetMatrix (O := rowTypes) B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) refined) z ∧
  allocatedIntegerKernelMask (O := rowTypes) B U b S x
    (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j refined
    (integerResidueMatrix (allocatedNonkernelJetMatrix (O := rowTypes) B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset (Fin dim))) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) refined) z ≤ CM)
    (_hperiod : ∀ j, integerScalarLattice (rowTypes j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (C V : Fin m → ℝ≥0)
    (_hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ≤ V j)
    (_hCexp : ∀ j, (C j : ℝ) ≤ Real.exp p₁) (_hVexp : ∀ j, (V j : ℝ) ≤ Real.exp p₁)
    {P₀ : ℝ} (_hP : 0 ≤ P₀) (_hn : (Fintype.card X : ℝ) ≤ P₀)
    (_hdim : (Fintype.card (Option (Fin dim) × X) : ℝ) ≤ P₀)
    (_hbudget : allocatedSiteErrorFourierOutput m p₁ w v ≤ P₀)
    [CompactSpace (CoefficientTorus (K := Fin dim) U)]
    [MeasurableSpace (CoefficientTorus (K := Fin dim) U)] [BorelSpace (CoefficientTorus (K := Fin dim) U)]
    (μ : Measure (CoefficientTorus (K := Fin dim) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hmp : ∀ j e, coefficients (p j) e ∈ U j)
    {R₁ S₀ ρ : ℝ} (_hS : 0 ≤ S₀) (_hSP : S₀ ≤ Real.exp P₀) (_hρ : 0 < ρ)
    (_hρP : 1 / ρ ≤ Real.exp P₀)
    (_hstride : ∀ x, (stride x : ℝ) ≤ S₀)
    (N : X → ℕ) (_hsize : ∀ x, Real.exp ((P₀ + K) ^ K) ≤ (N x : ℝ))
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun t => (N t : ℝ)) R₁ (U j) (p j))
    (_hR : Real.exp ((P₀ + K) ^ K) ≤ R₁),
    ∀ (W : ℝ) (hW : 0 ≤ W),
    let H := trimmedSpatialRootScale ρ N stride
    let point := physicalCubeRowSample (O := rowTypes) U d (rows) p hmp
    let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let target := allocatedSupportedFullGridResidueProfile B U b hR hσ S refined x hb o bW d f witnesses
    let reference := allocatedSupportedWholeReference (dim := dim) B U b S refined
    ∀ (base : X → ℤ)
      (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))
      (ξ : ℝ), 0 < ξ →
    let V₀ := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W ρ ξ N
    (0 < ∑' z, selectedResidueSmoothWeight stride cells V₀ z) →
    (∀ t, Fintype.card (Option (LayerSamplerVariables G I n B)) *
      allocatedPhysicalEntryBudget B U b S (fun _ => 0) ≤ H t) →
    (∀ t, 8 * (probabilityProfileLipschitz : ℝ) ≤ 20 * H t) →
    ∀ (M : ℕ) (hM : 0 < M) (selection : Fin dim ↪ G)
      (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
      (mesh : ℝ), 0 < mesh →
    (allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W) →
    (integerScalarLattice (Unit ⊕ Fin dim) (modulus : ℤ) ≤
      pivotFullImage
        (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ)) (scalarCubeDifferenceMatrix x) selection)) →
    ∀ (test : (X → (Unit ⊕ Fin dim) → ℤ) → ℂ), (∀ v, ‖test v‖ ≤ 1) →
    ∀ (Z : ℝ), 0 < Z →
    let profile := fun y z => (allocatedWholeMaskedCoveredProfile (O := rowTypes)
      B U b hR hσ S x (rows) hb o bW d y modulus f z : ℂ)
    let reconstruct := allocatedWholeResidueReconstruction B U b S X modulus stride reference x base
    let weight := allocatedRecenteredResidueWeight (τ := ρ) B U b S X modulus stride reference x hM selection hx
      N hW mesh base cells test
    let cap := ((modulus : ℝ) ^ Fintype.card (Unit ⊕ Fin dim) *
      anisotropicSpatialDensityCap selection (1 / (M : ℝ))) ^ Fintype.card X
    let factor := (30 / smoothProbabilityProfile 0) ^ Fintype.card (Option (Fin dim) × X) *
      (((1 + W) / (S.value : ℝ)) ^ dim) ^ Fintype.card X
    ‖(law.complexMean (allocatedRecenteredProfileTerm (τ := ρ) (ξ := ξ)
        B U b S X modulus stride reference x hM selection hx N hW mesh base cells point test profile) -
      (law.fiberLaw (principalResidueLabel refined)).complexMean (fun r =>
        ∑ a : cells, (selectedResidueCellWeight stride cells V₀ a : ℂ) *
          ∑ v ∈ spatialWindow H 4, weight r a v * target r (point (reconstruct r a.val v)))) / (Z : ℂ)‖ ≤
      (cap * factor * Real.exp (-E)) / Z := by
  intro K hSampling x hb o Q _ bW d _ _ f CM Cf hCM hfb hCMexp hCfexp hmask hperiod C V hC hV
    hCexp hVexp P₀ hP₀ hn hdim hbudget _ _ _ μ _ _ ν _ _ p hp hmp R₁ S₀ ρ
    hS hSP hρ hρP hstride N hsize₁ hrank hR₁ W hW H point law target reference
    base cells ξ hξ V₀ hZ₀ hrows hscale M hM selection hx mesh hmesh hroot hspatial test htest Z hZ
    profile reconstruct weight cap factor
  have hN (t : X) : 0 < N t := Nat.cast_pos.mp ((Real.exp_pos _).trans_le (hsize₁ t))
  have hV₀ : ∀ z, 0 < V₀ z := narrowTrimmedSpatialWidths_pos hW hρ hξ N hN
  have hcap : 0 ≤ cap := pow_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg modulus) _)
    (anisotropicSpatialDensityCap_nonneg selection (one_div_nonneg.mpr (Nat.cast_nonneg M)))) _
  have hweight := allocatedRecenteredResidueWeight_norm_le B U b S X modulus stride reference x
    hM selection hx N hW mesh base cells test hs hN hρ hroot hmesh hspatial htest
  have hprevious := allocated_full_grid_reconstructed_primitive_comparison B U b hR hσ S refined δ witnesses
    hWitness hp₁ hw hv hE hdimSmall hvars hI hn₁ hJ M₀ hqM hM₀ hS₁ hδ hEbudget (K := K) hSampling
  have hbound := @hprevious x hb o Q _ bW d _ _ f CM Cf hCM hfb hCMexp hCfexp hmask
    modulus ⟨∏ t, stride t, rfl⟩ hperiod C V hC hV hCexp hVexp
    X _ _ P₀ hP₀ hn hdim hbudget _ _ _ μ _ _ ν _ _ p hp hmp stride hs R₁ S₀ ρ
    hS hSP hρ hρP hstride N hsize₁ hrank hR₁ W hW reference base cells V₀ hV₀ hZ₀ hrows hscale
    weight cap Z hcap hZ hweight
  have hsource : law.complexMean
      (allocatedRecenteredProfileTerm (τ := ρ) (ξ := ξ)
        B U b S X modulus stride reference x hM selection hx N hW mesh base cells point test profile) =
      law.complexMean (fun y => ∑ a : cells, (selectedResidueCellWeight stride cells V₀ a : ℂ) *
        ∑ v ∈ spatialWindow H 4, weight (principalResidueLabel refined y) a v *
          profile y (point (reconstruct (principalResidueLabel refined y) a.val v))) := by
    apply law.complexMean_congr_support
    intro y hy
    exact allocatedRecenteredProfileTerm_residue_weight B U b S X modulus stride reference x
      hM selection hx N hW mesh base cells point test profile y
      (allocatedSupportedWholeReference_label B U b S refined y hy)
  rw [hsource]
  exact hbound

end Erdos3.VectorPolynomial

end

end OAI
