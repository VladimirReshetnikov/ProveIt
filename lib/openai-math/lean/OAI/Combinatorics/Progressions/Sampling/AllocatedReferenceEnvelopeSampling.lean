import OAI.Combinatorics.Progressions.Lattices.AllocatedResidueSitePrimitiveAverage

namespace OAI

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
  AllocatedResidueSiteWitness (dim := dim) B U b S q r.val)
variable (hWitness : ∀ r, AllocatedResidueSiteSampling.{uG,uI,uB,uJ,uQ,uX}
  B U b hR hσ S q (witnesses r) δ)

include hWitness in
omit [NeZero q] in
theorem allocated_residue_site_reference_envelope_error :
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
      hb o bW d q (witnesses r).representative (witnesses r).positive (allocatedActiveGrid B U b S) f
      (allocatedActiveSiteApproximation B U b S rowSets (witnesses r).expansion)
      (allocatedActiveNaturalVolume B U b S rowSets)
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
  dsimp only [AllocatedResidueSiteSampling] at hc
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

end OAI
