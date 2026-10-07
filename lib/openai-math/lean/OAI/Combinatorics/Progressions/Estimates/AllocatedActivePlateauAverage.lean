import OAI.Combinatorics.Progressions.Estimates.AllocatedJointWindowIntegral
import OAI.Combinatorics.Progressions.Estimates.AllocatedPeriodicAmbientSiteExpansion

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
variable (selected : {a // allocatedGridAxis (I := I) U b S.value a} → Prop) [DecidablePred selected]
variable (W : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a}, Finset (CoefficientJetAxisRow O a.val))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  O (Sigma.fst (Subtype.val a))) → ℝ) → ℝ)
variable (hf : Measurable f) {T C Cf : ℝ}
variable (hT : 0 ≤ T) (hs : ∀ v, T < ‖v‖ → f v = 0)
variable (hC : 1 ≤ C) (hCf : 0 ≤ Cf) (hfb : ∀ v, |f v| ≤ Cf)

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "laws" => allocatedSupportedGridJetPMF B U b hR hσ S x rows q (principalResidueLabel q y₀) hcell
local notation "density" => allocatedSupportedGridJetDensity B U b hR hσ S x rows q (principalResidueLabel q y₀) hcell
local notation "weight" => allocatedGridWindowWeight B U b S O selected W laws
local notation "χ" => allocatedChartGridMultiplier B U b S O hb o bW d weight
local notation "profile" => allocatedWholeMaskedGridlessProfile B U b S x y₀ rows hb o bW d q f
local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))
local notation "massBound" => (∏ a : {a // allocatedGridAxis (I := I) U b S.value a},
  ite (selected a) (Nat.cast (Finset.card (W a)) : ℝ) 1) *
  ((C ^ Fintype.card (LayerSamplerAxis I n) * Cf) *
    (2 * T + 1) ^ Fintype.card (Σ a : LayerSamplerAxis I n, O (Sigma.fst a)))
local notation "residue" => fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q

variable (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x rows j q (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
    (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀) rows j
    (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x rows j q (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
    (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀) rows j
    (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ C)

local notation "longBound" => (C ^ Fintype.card (LayerSamplerAxis I n) * Cf) *
  (2 * T + 1) ^ Fintype.card (Σ a : LayerSamplerAxis I n, O (Sigma.fst a))

noncomputable def allocatedSelectedConditionalError (g : ((a : {a : {a // grid a} // selected a}) →
  CoefficientJetAxisRow O (Subtype.val (Subtype.val a))) → ℂ) (N : ℝ)
    (z : EuclideanJetLayers U O) : ℂ :=
  ((FiniteProbabilityWeights.condition
    (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S))
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)) hcell).mean
      (fun y => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y q f z) : ℂ) -
    allocatedComplexGridMultiplier B U b S O hb o bW d
      (allocatedSelectedGridExtension B U b hR hσ S x rows q (principalResidueLabel q y₀) hcell selected g N) z *
        (profile z : ℂ)

include hf hT hs hC hCf hfb hm in
theorem allocatedSelectedConditionalError_bound
    (hperiod : ∀ j, integerScalarLattice (O j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (g : ((a : {a : {a // grid a} // selected a}) →
  CoefficientJetAxisRow O (Subtype.val (Subtype.val a))) → ℂ) {N ε V : ℝ} (hN : 0 < N) (hε : 0 ≤ ε)
    (hzero : ∀ z : ((a : {a : {a // grid a} // selected a}) →
  CoefficientJetAxisRow O (Subtype.val (Subtype.val a))), (∃ a, z a ∉ W a.val) →
      (∏ a, (laws a.val (z a)).toReal) = 0 ∧ g z = 0)
    (he : ∀ z : ((a : {a : {a // grid a} // selected a}) →
  CoefficientJetAxisRow O (Subtype.val (Subtype.val a))), ‖(N : ℂ) * ((∏ a, (laws a.val (z a)).toReal : ℝ) : ℂ) - g z‖ ≤ ε)
    (hcard : (∏ a : {a // grid a}, if selected a then ((W a).card : ℝ) else 1) ≤ V * N) :
    Integrable (allocatedSelectedConditionalError B U b hR hσ S x rows hb o bW d q y₀ hcell selected f g N) haar ∧
      (∫ z, ‖allocatedSelectedConditionalError B U b hR hσ S x rows hb o bW d q y₀ hcell selected f g N z‖ ∂haar) ≤
        (ε * V) * longBound := by
  have herror := allocatedSelectedGridExtension_error B U b hR hσ S x rows q
    (principalResidueLabel q y₀) hcell selected W g hN hzero he
  have hmeas := allocatedSelectedGridExtension_measurable B U b hR hσ S x rows q
    (principalResidueLabel q y₀) hcell selected g N
  have h := allocatedConditionalProfile_haar_error B U b hR hσ S x rows hb o bW d ν q y₀ hcell
    selected W f hf hT hs hC hCf hfb hm hperiod _ hmeas (div_nonneg hε hN.le) herror
  refine ⟨h.1, h.2.trans ?_⟩
  apply selectedWindow_volume_cancel hN hε _ hcard
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  positivity

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
local notation "O" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))

variable (x : G → IntegerScalarCubeBox α S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "active" => allocatedActiveGrid B U b S
local notation "activeAxes" => {a : {a // grid a} // active a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "axisN" => allocatedGridNaturalScale B U b S
local notation "volumeN" => allocatedActiveNaturalVolume B U b S rowSets
local notation "rowFamily" => (fun a : (Σ j : Fin m, Fin (n j)) => rowSets (Sigma.fst a))
local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))

variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)
variable (hf : Measurable f) {T C Cf : ℝ}
variable (hT : 0 ≤ T) (hs : ∀ v, T < ‖v‖ → f v = 0)
variable (hC : 1 ≤ C) (hCf : 0 ≤ Cf) (hfb : ∀ v, |f v| ≤ Cf)
variable (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x
    (fun j => (Subtype.val : rowSets j → Finset α)) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset α)) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x
    (fun j => (Subtype.val : rowSets j → Finset α)) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset α)) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ C)
variable (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)
variable (P δ : ℝ)
variable (M : {a : {a // allocatedGridAxis (I := I) U b S.value a} // allocatedActiveGrid B U b S a} → ℕ)
variable [∀ a, NeZero (M a)]

local notation "pointTolerance" => allocatedGridL1PointTolerance (G := G) B (rowFamily) δ
local notation "accuracy" => allocatedGridFamilyAccuracy B (rowFamily) P pointTolerance
local notation "approximation" => allocatedActivePlateauProduct B U b hR hσ S rowSets q
  (principalResidueLabel q y₀) hq hsize P accuracy M
local notation "difference" => allocatedSelectedConditionalError B U b hR hσ S x (rows) hb o bW d q y₀ hcell
  active f approximation volumeN
local notation "longBound" => (C ^ Fintype.card (LayerSamplerAxis I n) * Cf) *
  (2 * T + 1) ^ Fintype.card (Σ a : LayerSamplerAxis I n, O (Sigma.fst a))

include hf hT hs hC hCf hfb hm in
theorem allocatedActivePlateau_haar_error
    (hperiod : ∀ j, integerScalarLattice (O j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (hP : 1 ≤ P) (hδ : 0 < δ)
    (hgamma : ∀ a : activeAxes, principalProfileSize (R (ig a.val).1)
      (Finset.card (layerIntegerPrincipalSlots (G := G) B (ig a.val).1 (ig a.val).2)) ≤ S.value)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hcP : scalarCubePrimitiveEnvelope Empty L 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α L 1 0 q ≤ P)
    (hM : ∀ a, M a = allocatedGridTorusFactor B α (ig a.val) * axisN a.val)
    (hrows : ∀ j t, t ∈ rowSets j → t.card ≤ j.val + 1)
    (hB : ∀ a : activeAxes, positiveModerateSpectrumBlockCount (ig a.val).1.val
      (rowSets (ig a.val).1).card ((layerTailDegree m + 2) * (rowSets (ig a.val).1).card) ≤
        Fintype.card (B ⟨(ig a.val).1, Sum.inr (ig a.val).2⟩)) :
    Integrable difference haar ∧ (∫ z, ‖difference z‖ ∂haar) ≤ δ * longBound := by
  have ht := allocatedGridL1PointTolerance_spec (G := G) B (rowFamily) δ hδ
  have he := allocatedActivePlateauProduct_error B U b hR hσ S rowSets x q
    (principalResidueLabel q y₀) hcell hq hsize P M pointTolerance hP ht.1
    hgamma L hL hcP hsP hM hrows hB
  have hz := allocatedActivePlateauProduct_zero B U b hR hσ S rowSets x q
    (principalResidueLabel q y₀) hcell hq hsize P accuracy M hrows
  have h := allocatedSelectedConditionalError_bound B U b hR hσ S x (rows) hb o bW d ν q y₀ hcell
    active (allocatedGridNaturalWindow B U b S rowSets) f hf hT hs hC hCf hfb hm hperiod
    approximation (allocatedActiveNaturalVolume_pos B U b hR S rowSets) ht.1.le hz he
    (allocatedActiveWindow_volume B U b hR S rowSets)
  refine ⟨h.1, h.2.trans (mul_le_mul_of_nonneg_right ht.2 ?_)⟩
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  positivity

end Erdos3.VectorPolynomial

end

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
variable (rowSets : Fin m → Finset (Finset α))
local notation "O" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))

variable (x : G → IntegerScalarCubeBox α S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable (q : ℕ)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "active" => allocatedActiveGrid B U b S
local notation "activeAxes" => {a : {a // grid a} // active a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "axisN" => allocatedGridNaturalScale B U b S
local notation "volumeN" => allocatedActiveNaturalVolume B U b S rowSets
local notation "rowFamily" => (fun a : (Σ j : Fin m, Fin (n j)) => rowSets (Sigma.fst a))
local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))

variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)
variable (hf : Measurable f) {T C Cf : ℝ}
variable (hT : 0 ≤ T) (hs : ∀ v, T < ‖v‖ → f v = 0)
variable (hC : 1 ≤ C) (hCf : 0 ≤ Cf) (hfb : ∀ v, |f v| ≤ Cf)
variable (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x
    (fun j => (Subtype.val : rowSets j → Finset α)) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset α)) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x
    (fun j => (Subtype.val : rowSets j → Finset α)) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset α)) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ C)
variable (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)
variable (P δ Λ : ℝ)
variable (M : {a : {a // allocatedGridAxis (I := I) U b S.value a} // allocatedActiveGrid B U b S a} → ℕ)
variable [∀ a, NeZero (M a)]

local notation "pointTolerance" => allocatedSitePointTolerance (G := G) B rowSets δ
local notation "trueCap" => allocatedGridFamilyCap B (rowFamily) P + 1
local notation "halfAccuracy" => uniformProductAccuracy (Fintype.card (Σ j : Fin m, Fin (n j))) trueCap pointTolerance / 2
local notation "torus" => (fun a : activeAxes => allocatedGridTorusFactor B α (ig (Subtype.val a)))
local notation "cap" => (fun a : activeAxes => allocatedGridPointCap B P (ig (Subtype.val a)) (rowSets (Sigma.fst (ig (Subtype.val a)))))
local notation "siteH" => (fun a : activeAxes =>
  allocatedNaturalSiteRadius (G := G) B (Sigma.fst (ig (Subtype.val a))) (Sigma.snd (ig (Subtype.val a))) (rowSets (Sigma.fst (ig (Subtype.val a)))) + 1 / 4)
local notation "bias" => (fun a : activeAxes => positiveModerateRetainedBias (Fin.val (Sigma.fst (ig (Subtype.val a))))
  (Finset.card (rowSets (Sigma.fst (ig (Subtype.val a))))) ((layerTailDegree m + 2) * Finset.card (rowSets (Sigma.fst (ig (Subtype.val a)))))
  P ((torus) a : ℝ) ((2 * ((torus) a : ℝ)) ^ Finset.card (rowSets (Sigma.fst (ig (Subtype.val a))))) halfAccuracy)
local notation "freq" => (fun a : activeAxes => Real.toNNReal (positiveRetainedFrequencyBound
  (Fin.val (Sigma.fst (ig (Subtype.val a)))) (Finset.card (rowSets (Sigma.fst (ig (Subtype.val a))))) P ((torus) a : ℝ) ((bias) a)))
local notation "approximation" => allocatedActiveSiteApproximation B U b S rowSets
local notation "difference" => (fun e => allocatedSelectedConditionalError B U b hR hσ S x (rows) hb o bW d q y₀ hcell
  active f (approximation e) volumeN)
local notation "longBound" => (C ^ Fintype.card (LayerSamplerAxis I n) * Cf) *
  (2 * T + 1) ^ Fintype.card (Σ a : LayerSamplerAxis I n, O (Sigma.fst a))

include hf hT hs hC hCf hfb hm hq hsize in
theorem exists_allocated_active_site_haar_error
    (hperiod : ∀ j, integerScalarLattice (O j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (hP : 1 ≤ P) (hδ : 0 < δ) (hΛ : 0 ≤ Λ)
    (hgamma : ∀ a : activeAxes, principalProfileSize (R (ig a.val).1)
      (Finset.card (layerIntegerPrincipalSlots (G := G) B (ig a.val).1 (ig a.val).2)) ≤ S.value)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hcP : scalarCubePrimitiveEnvelope Empty L 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α L 1 0 q ≤ P)
    (hM : ∀ a, M a = (torus) a * axisN a.val)
    (hrows : ∀ j t, t ∈ rowSets j → t.card ≤ j.val + 1)
    (hB : ∀ a : activeAxes, positiveModerateSpectrumBlockCount (ig a.val).1.val
      (rowSets (ig a.val).1).card ((layerTailDegree m + 2) * (rowSets (ig a.val).1).card) ≤
        Fintype.card (B ⟨(ig a.val).1, Sum.inr (ig a.val).2⟩))
    (hHΛ : ∀ a, (siteH) a ≤ Real.exp Λ)
    (hδΛ : ∀ a, (halfAccuracy / ((cap) a + 1))⁻¹ ≤ Real.exp Λ)
    (hLΛ : ∀ a, ((CircleFourier.characterLipConstant * ((rowSets (ig a.val).1).card * (freq) a) + 4) *
      (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp Λ) :
    ∃ e : activeAxes → ScalarSiteExpansion.{uα,uα} (Finset α),
      allocatedActiveSiteBounds B U b S rowSets P pointTolerance Λ M e ∧
      Integrable (difference e) haar ∧ (∫ z, ‖difference e z‖ ∂haar) ≤ δ * longBound := by
  have ht := allocatedSitePointTolerance_spec (G := G) B rowSets hδ
  obtain ⟨e, hbE, he⟩ := exists_allocated_joint_site_expansion B U b hR hσ S q
    (principalResidueLabel q y₀) hcell (rowFamily) (fun a : activeAxes => ig a.val) P pointTolerance Λ M
    hP ht.1 hΛ ((allocatedGridIntegerAxis_injective B U b S).comp Subtype.val_injective)
    (fun a => allocatedGridIntegerAxis_grid B U b S a.val) (fun a => a.property)
    hgamma hq hsize L hL hcP hsP hM (fun a => hrows (ig a.val).1) hB hHΛ hδΛ hLΛ
  have hpoint := allocatedActiveSiteApproximation_error B U b hR hσ S rowSets q
    (principalResidueLabel q y₀) hcell e he x
  have hzero (z : (a : activeAxes) → CoefficientJetAxisRow (O) a.val.val)
      (hz : ∃ a, z a ∉ allocatedGridSiteWindow B rowSets U b S a.val) :=
    And.intro
      (allocatedActiveGridMass_zero_off_site_window B U b hR hσ S rowSets x q
        (principalResidueLabel q y₀) hcell hq hsize hrows z hz)
      (allocatedActiveSiteApproximation_zero B U b hR S rowSets e hrows
        (fun a => (hbE a).support) z hz)
  have h := allocatedSelectedConditionalError_bound B U b hR hσ S x (rows) hb o bW d ν q y₀ hcell
    active (allocatedGridSiteWindow B rowSets U b S) f hf hT hs hC hCf hfb hm hperiod
    (approximation e) (allocatedActiveNaturalVolume_pos B U b hR S rowSets) ht.1.le hzero hpoint
    (allocatedActiveSiteWindow_volume B rowSets U b S hR)
  refine ⟨e, hbE, h.1, h.2.trans (mul_le_mul_of_nonneg_right ht.2 ?_)⟩
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  positivity

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
local notation "O" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))
variable (x : G → IntegerScalarCubeBox α S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (q : ℕ)

local notation "active" => allocatedActiveGrid B U b S
local notation "rowFamily" => (fun a : (Σ j : Fin m, Fin (n j)) => rowSets (Sigma.fst a))

noncomputable def allocatedActivePlateauProfile
    (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
    (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
    (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
      {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)
    (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value) (P δ : ℝ)
    (M : {a : {a // allocatedGridAxis (I := I) U b S.value a} // allocatedActiveGrid B U b S a} → ℕ)
    [∀ a, NeZero (M a)] (z : EuclideanJetLayers U O) : ℂ :=
  allocatedComplexGridMultiplier B U b S O hb o bW d
    (allocatedSelectedGridExtension B U b hR hσ S x rows q (principalResidueLabel q y₀) hcell active
      (allocatedActivePlateauProduct B U b hR hσ S rowSets q (principalResidueLabel q y₀) hq hsize P
        (allocatedGridFamilyAccuracy B rowFamily P (allocatedGridL1PointTolerance (G := G) B rowFamily δ)) M)
      (allocatedActiveNaturalVolume B U b S rowSets)) z *
    (allocatedWholeMaskedGridlessProfile B U b S x y₀ rows hb o bW d q f z : ℂ)

variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)
variable (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value) (P δ : ℝ)
variable (M : {a : {a // allocatedGridAxis (I := I) U b S.value a} // allocatedActiveGrid B U b S a} → ℕ)
variable [∀ a, NeZero (M a)]

theorem allocatedActivePlateauProfile_measurable (hf : Measurable f) :
    Measurable (allocatedActivePlateauProfile B U b hR hσ S rowSets x hb o bW d q y₀ hcell f hq hsize P δ M) := by
  unfold allocatedActivePlateauProfile
  apply Measurable.mul
  · apply allocatedComplexGridMultiplier_measurable
    exact allocatedSelectedGridExtension_measurable B U b hR hσ S x rows q
      (principalResidueLabel q y₀) hcell active _ _
  · exact (allocatedWholeMaskedGridlessProfile_measurable B U b S x y₀ rows hb o bW d q f hf).complex_ofReal

theorem allocatedActivePlateauProfile_error :
    (fun z => ((FiniteProbabilityWeights.condition
      (principalTupleWeights (α := α) B (layerSamplerDegree I n)
        (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S))
      (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)) hcell).mean
        (fun y => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y q f z) : ℂ) -
      allocatedActivePlateauProfile B U b hR hσ S rowSets x hb o bW d q y₀ hcell f hq hsize P δ M z) =
    allocatedSelectedConditionalError B U b hR hσ S x rows hb o bW d q y₀ hcell active f
      (allocatedActivePlateauProduct B U b hR hσ S rowSets q (principalResidueLabel q y₀) hq hsize P
        (allocatedGridFamilyAccuracy B rowFamily P (allocatedGridL1PointTolerance (G := G) B rowFamily δ)) M)
      (allocatedActiveNaturalVolume B U b S rowSets) := rfl

end Erdos3.VectorPolynomial

end

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
variable (rowSets : Fin m → Finset (Finset α))
local notation "O" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))
variable (x : G → IntegerScalarCubeBox α S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (q : ℕ)

local notation "active" => allocatedActiveGrid B U b S
local notation "rowFamily" => (fun a : (Σ j : Fin m, Fin (n j)) => rowSets (Sigma.fst a))

noncomputable def allocatedActiveSiteProfile
    (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
    (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
    (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
      {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)
    (e : {a : {a // allocatedGridAxis (I := I) U b S.value a} // allocatedActiveGrid B U b S a} →
      ScalarSiteExpansion.{uα,uα} (Finset α)) (z : EuclideanJetLayers U O) : ℂ :=
  allocatedComplexGridMultiplier B U b S O hb o bW d
    (allocatedSelectedGridExtension B U b hR hσ S x rows q (principalResidueLabel q y₀) hcell active
      (allocatedActiveSiteApproximation B U b S rowSets e)
      (allocatedActiveNaturalVolume B U b S rowSets)) z *
    (allocatedWholeMaskedGridlessProfile B U b S x y₀ rows hb o bW d q f z : ℂ)

variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)))
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)
variable (e : {a : {a // allocatedGridAxis (I := I) U b S.value a} // allocatedActiveGrid B U b S a} →
  ScalarSiteExpansion.{uα,uα} (Finset α))

theorem allocatedActiveSiteProfile_measurable (hf : Measurable f) :
    Measurable (allocatedActiveSiteProfile B U b hR hσ S rowSets x hb o bW d q y₀ hcell f e) := by
  unfold allocatedActiveSiteProfile
  apply Measurable.mul
  · apply allocatedComplexGridMultiplier_measurable
    exact allocatedSelectedGridExtension_measurable B U b hR hσ S x rows q
      (principalResidueLabel q y₀) hcell active _ _
  · exact (allocatedWholeMaskedGridlessProfile_measurable B U b S x y₀ rows hb o bW d q f hf).complex_ofReal

theorem allocatedActiveSiteProfile_error :
    (fun z => ((FiniteProbabilityWeights.condition
      (principalTupleWeights (α := α) B (layerSamplerDegree I n)
        (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S))
      (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)) hcell).mean
        (fun y => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y q f z) : ℂ) -
      allocatedActiveSiteProfile B U b hR hσ S rowSets x hb o bW d q y₀ hcell f e z) =
    allocatedSelectedConditionalError B U b hR hσ S x rows hb o bW d q y₀ hcell active f
      (allocatedActiveSiteApproximation B U b S rowSets e)
      (allocatedActiveNaturalVolume B U b S rowSets) := rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))
local notation "O" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowSets j → Finset α))

variable (x : G → IntegerScalarCubeBox α S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable (q : ℕ) [NeZero q]
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "active" => allocatedActiveGrid B U b S
local notation "activeAxes" => {a : {a // grid a} // active a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "axisN" => allocatedGridNaturalScale B U b S
local notation "volumeN" => allocatedActiveNaturalVolume B U b S rowSets
local notation "rowFamily" => (fun a : (Σ j : Fin m, Fin (n j)) => rowSets (Sigma.fst a))
local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))

variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset α // t ∈ rowSets (Sigma.fst (Subtype.val a))}) → ℝ) → ℝ)
variable (hf : Measurable f) {T C Cf : ℝ}
variable (hT : 0 ≤ T) (hs : ∀ v, T < ‖v‖ → f v = 0)
variable (hC : 1 ≤ C) (hCf : 0 ≤ Cf) (hfb : ∀ v, |f v| ≤ Cf)
variable (hm : ∀ y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α
  (allocatedPrincipalSides B U b S), ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x
    (fun j => (Subtype.val : rowSets j → Finset α)) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset α)) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x
    (fun j => (Subtype.val : rowSets j → Finset α)) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : rowSets j → Finset α)) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ C)
variable (hq : 0 < q) (hsize : (Fintype.card α + 1) * q ≤ S.value)
variable (P δ : ℝ)
variable (M : {a : {a // allocatedGridAxis (I := I) U b S.value a} // allocatedActiveGrid B U b S a} → ℕ)
variable [∀ a, NeZero (M a)]

local notation "pointTolerance" => allocatedGridL1PointTolerance (G := G) B (rowFamily) δ
local notation "accuracy" => allocatedGridFamilyAccuracy B (rowFamily) P pointTolerance
local notation "longBound" => (C ^ Fintype.card (LayerSamplerAxis I n) * Cf) *
  (2 * T + 1) ^ Fintype.card (Σ a : LayerSamplerAxis I n, O (Sigma.fst a))

local notation "tuples" => principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
local notation "labelType" => (PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)

include hf hT hs hC hCf hfb hm in
theorem exists_allocatedActivePlateau_residue_approximation
    (hperiod : ∀ j, integerScalarLattice (O j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (hP : 1 ≤ P) (hδ : 0 < δ)
    (hgamma : ∀ a : activeAxes, principalProfileSize (R (ig a.val).1)
      (Finset.card (layerIntegerPrincipalSlots (G := G) B (ig a.val).1 (ig a.val).2)) ≤ S.value)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hcP : scalarCubePrimitiveEnvelope Empty L 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α L 1 0 q ≤ P)
    (hM : ∀ a, M a = allocatedGridTorusFactor B α (ig a.val) * axisN a.val)
    (hrows : ∀ j t, t ∈ rowSets j → t.card ≤ j.val + 1)
    (hB : ∀ a : activeAxes, positiveModerateSpectrumBlockCount (ig a.val).1.val
      (rowSets (ig a.val).1).card ((layerTailDegree m + 2) * (rowSets (ig a.val).1).card) ≤
        Fintype.card (B ⟨(ig a.val).1, Sum.inr (ig a.val).2⟩)) :
    ∃ A : labelType → EuclideanJetLayers U O → ℂ,
      (∀ r, Measurable (A r)) ∧
      (∀ r, 0 < (tuples).mass (Finset.univ.filter (fun y => principalResidueLabel q y = r)) →
        ∃ y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S),
        ∃ hy₀ : 0 < (tuples).mass
          (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)),
          principalResidueLabel q y₀ = r ∧ A r =
            allocatedActivePlateauProfile B U b hR hσ S rowSets x hb o bW d q y₀ hy₀ f hq hsize P δ M) ∧
      Integrable (fun z => ((tuples).mean (fun y =>
        allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y q f z) : ℂ) -
        ((tuples).fiberLaw (principalResidueLabel q)).complexMean (fun r => A r z)) haar ∧
      (∫ z, ‖((tuples).mean (fun y =>
        allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y q f z) : ℂ) -
        ((tuples).fiberLaw (principalResidueLabel q)).complexMean (fun r => A r z)‖ ∂haar) ≤ δ * longBound := by
  let p := principalTupleWeights (α := α) B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
  let Spec (r : labelType) (A : EuclideanJetLayers U O → ℂ) : Prop :=
    ∃ y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S),
    ∃ hy₀ : 0 < p.mass
      (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q y₀)),
      principalResidueLabel q y₀ = r ∧ A =
        allocatedActivePlateauProfile B U b hR hσ S rowSets x hb o bW d q y₀ hy₀ f hq hsize P δ M
  have hlocal (r : labelType) (hr : 0 < p.mass (Finset.univ.filter (fun y => principalResidueLabel q y = r))) :
      ∃ A : EuclideanJetLayers U O → ℂ, Spec r A ∧ Measurable A ∧
        Integrable (fun z => (p.condition _ hr).complexMean (fun y =>
          (allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y q f z : ℂ)) - A z) haar ∧
        (∫ z, ‖(p.condition _ hr).complexMean (fun y =>
          (allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y q f z : ℂ)) - A z‖ ∂haar) ≤
          δ * longBound := by
    obtain ⟨y₀, hy₀⟩ := p.exists_mem_positive_fiber (principalResidueLabel q) r hr
    subst r
    refine ⟨allocatedActivePlateauProfile B U b hR hσ S rowSets x hb o bW d q y₀ hr f hq hsize P δ M,
      ⟨y₀, hr, rfl, rfl⟩,
      allocatedActivePlateauProfile_measurable B U b hR hσ S rowSets x hb o bW d q y₀ hr f hq hsize P δ M hf, ?_⟩
    have h := allocatedActivePlateau_haar_error B U b hR hσ S rowSets x hb o bW d ν q y₀ hr
      f hf hT hs hC hCf hfb (hm y₀) hq hsize P δ M hperiod hP hδ hgamma L hL hcP hsP hM hrows hB
    simpa only [FiniteProbabilityWeights.complexMean_ofReal,
      ← allocatedActivePlateauProfile_error B U b hR hσ S rowSets x hb o bW d q y₀ hr f hq hsize P δ M] using h
  obtain ⟨A, hAm, hAs, hAi, hAe⟩ := p.exists_supported_fiber_l1_approximation
    (principalResidueLabel q) haar
    (fun y z => (allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d y q f z : ℂ))
    (fun _ => δ * longBound) Spec hlocal
  refine ⟨A, hAm, hAs, ?_, ?_⟩
  · simpa only [FiniteProbabilityWeights.complexMean_ofReal] using hAi
  · simpa only [FiniteProbabilityWeights.complexMean_ofReal, (p.fiberLaw (principalResidueLabel q)).mean_const] using hAe

end Erdos3.VectorPolynomial

end

end OAI
