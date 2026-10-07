/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.AllocatedWholeProfileEnvelope
import OAI.Combinatorics.Progressions.Geometry.SupportedFiberFiniteMeanError

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {X R K I : Type*} [Fintype X] [DecidableEq X]
variable [Fintype R] [DecidableEq R] [Fintype K] [Fintype I]
variable (p : FiniteProbabilityWeights X) (F : X → R)
variable (stride : I → ℕ) (cells : Finset (ColumnResiduePattern K I stride))
variable (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells W z)
variable (f : X → (K × I → ℤ) → ℂ) (target : R → (K × I → ℤ) → ℂ)

include hW hZ

theorem selectedResidue_supported_fiber_error (ε : R → ℝ)
    (he : ∀ r (hr : 0 < p.mass (Finset.univ.filter (fun x => F x = r))),
      selectedResidueDensityMass stride cells W
        (fun z => ‖(p.condition _ hr).complexMean (fun x => f x z) - target r z‖) ≤ ε r) :
    selectedResidueDensityMass stride cells W
      (fun z => ‖p.complexMean (fun x => f x z) -
        (p.fiberLaw F).complexMean (fun r => target r z)‖) ≤ (p.fiberLaw F).mean ε := by
  have h := p.mean_norm_supported_fiber_error (selectedResidueFiniteLaw stride cells W hW hZ)
    F (fun x z => f x z.val) (fun r z => target r z.val) ε (fun r hr => by
      rw [selectedResidueFiniteLaw_densityMass stride cells W hW hZ
        (fun z => ‖(p.condition _ hr).complexMean (fun x => f x z) - target r z‖)]
      exact he r hr)
  rw [selectedResidueFiniteLaw_densityMass stride cells W hW hZ
    (fun z => ‖p.complexMean (fun x => f x z) - (p.fiberLaw F).complexMean (fun r => target r z)‖)] at h
  exact h

theorem selectedResidue_supported_fiber_error_uniform {ε : ℝ}
    (he : ∀ r (hr : 0 < p.mass (Finset.univ.filter (fun x => F x = r))),
      selectedResidueDensityMass stride cells W
        (fun z => ‖(p.condition _ hr).complexMean (fun x => f x z) - target r z‖) ≤ ε) :
    selectedResidueDensityMass stride cells W
      (fun z => ‖p.complexMean (fun x => f x z) -
        (p.fiberLaw F).complexMean (fun r => target r z)‖) ≤ ε := by
  simpa only [FiniteProbabilityWeights.mean_const] using
    selectedResidue_supported_fiber_error p F stride cells W hW hZ f target (fun _ => ε) he

theorem selectedResidue_supported_fiber_test_error (ε : R → ℝ)
    (he : ∀ r (hr : 0 < p.mass (Finset.univ.filter (fun x => F x = r))),
      selectedResidueDensityMass stride cells W
        (fun z => ‖(p.condition _ hr).complexMean (fun x => f x z) - target r z‖) ≤ ε r)
    (φ : (K × I → ℤ) → ℂ) (hφ : ∀ z, ‖φ z‖ ≤ 1) :
    ‖∑' z, ((selectedResidueSmoothPMF stride cells W hW hZ z).toReal : ℂ) *
      ((p.complexMean (fun x => f x z) - (p.fiberLaw F).complexMean (fun r => target r z)) * φ z)‖ ≤
        (p.fiberLaw F).mean ε := by
  have h := p.complexMean_supported_fiber_test_error (selectedResidueFiniteLaw stride cells W hW hZ)
    F (fun x z => f x z.val) (fun r z => target r z.val) ε (fun r hr => by
      rw [selectedResidueFiniteLaw_densityMass stride cells W hW hZ
        (fun z => ‖(p.condition _ hr).complexMean (fun x => f x z) - target r z‖)]
      exact he r hr) (fun z => φ z.val) (fun z => hφ z.val)
  rw [selectedResidueFiniteLaw_complexMean stride cells W hW hZ
    (fun z => (p.complexMean (fun x => f x z) - (p.fiberLaw F).complexMean (fun r => target r z)) * φ z)] at h
  exact h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {X R K I : Type*} [Fintype X] [DecidableEq X]
variable [Fintype R] [DecidableEq R] [Fintype K] [Fintype I]
variable (p : FiniteProbabilityWeights X) (F : X → R)
variable (stride : I → ℕ) (cells : Finset (ColumnResiduePattern K I stride))
variable (W : K × I → ℝ) (hW : ∀ z, 0 < W z)
variable (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells W z)
variable (f : X → (K × I → ℤ) → ℂ) (target : R → (K × I → ℤ) → ℂ)
variable (weight : R → (K × I → ℤ) → ℂ) {C : ℝ} (hC : 0 ≤ C)
variable (hweight : ∀ r z, ‖weight r z‖ ≤ C)

include hW hZ hC hweight

omit [Fintype R] in
theorem selectedResidue_weighted_condition_error (r : R)
    (hr : 0 < p.mass (Finset.univ.filter (fun x => F x = r))) {ε : ℝ}
    (he : selectedResidueDensityMass stride cells W
      (fun z => ‖(p.condition _ hr).complexMean (fun x => f x z) - target r z‖) ≤ ε) :
    selectedResidueDensityMass stride cells W
      (fun z => ‖(p.condition _ hr).complexMean (fun x => weight (F x) z * f x z) -
        weight r z * target r z‖) ≤ C * ε := by
  let law := selectedResidueFiniteLaw stride cells W hW hZ
  rw [← selectedResidueFiniteLaw_densityMass stride cells W hW hZ
    (fun z => ‖(p.condition _ hr).complexMean (fun x => weight (F x) z * f x z) -
      weight r z * target r z‖)]
  have hid (z : K × I → ℤ) :
      (p.condition _ hr).complexMean (fun x => weight (F x) z * f x z) - weight r z * target r z =
        weight r z * ((p.condition _ hr).complexMean (fun x => f x z) - target r z) := by
    rw [p.condition_complexMean_fiber_mul F r hr (fun x => f x z) (fun r => weight r z), mul_sub]
  calc
    _ ≤ law.mean (fun z => C * ‖(p.condition _ hr).complexMean (fun x => f x z.val) - target r z.val‖) := by
      apply law.mean_mono
      intro z
      rw [hid, norm_mul]
      exact mul_le_mul_of_nonneg_right (hweight r z.val) (norm_nonneg _)
    _ = C * selectedResidueDensityMass stride cells W
        (fun z => ‖(p.condition _ hr).complexMean (fun x => f x z) - target r z‖) := by
      rw [law.mean_const_mul]
      exact congrArg (fun a : ℝ => C * a)
        (selectedResidueFiniteLaw_densityMass stride cells W hW hZ
          (fun z => ‖(p.condition _ hr).complexMean (fun x => f x z) - target r z‖))
    _ ≤ C * ε := mul_le_mul_of_nonneg_left he hC

theorem selectedResidue_supported_fiber_weighted_error (ε : R → ℝ)
    (he : ∀ r (hr : 0 < p.mass (Finset.univ.filter (fun x => F x = r))),
      selectedResidueDensityMass stride cells W
        (fun z => ‖(p.condition _ hr).complexMean (fun x => f x z) - target r z‖) ≤ ε r) :
    selectedResidueDensityMass stride cells W
      (fun z => ‖p.complexMean (fun x => weight (F x) z * f x z) -
        (p.fiberLaw F).complexMean (fun r => weight r z * target r z)‖) ≤
      C * (p.fiberLaw F).mean ε := by
  have h := selectedResidue_supported_fiber_error p F stride cells W hW hZ
    (fun x z => weight (F x) z * f x z) (fun r z => weight r z * target r z)
    (fun r => C * ε r) (fun r hr => selectedResidue_weighted_condition_error
      p F stride cells W hW hZ f target weight hC hweight r hr (he r hr))
  simpa only [FiniteProbabilityWeights.mean_const_mul] using h

theorem selectedResidue_supported_fiber_weighted_test_error (ε : R → ℝ)
    (he : ∀ r (hr : 0 < p.mass (Finset.univ.filter (fun x => F x = r))),
      selectedResidueDensityMass stride cells W
        (fun z => ‖(p.condition _ hr).complexMean (fun x => f x z) - target r z‖) ≤ ε r)
    (φ : (K × I → ℤ) → ℂ) (hφ : ∀ z, ‖φ z‖ ≤ 1) :
    ‖∑' z, ((selectedResidueSmoothPMF stride cells W hW hZ z).toReal : ℂ) *
      ((p.complexMean (fun x => weight (F x) z * f x z) -
        (p.fiberLaw F).complexMean (fun r => weight r z * target r z)) * φ z)‖ ≤
      C * (p.fiberLaw F).mean ε := by
  have h := selectedResidue_supported_fiber_test_error p F stride cells W hW hZ
    (fun x z => weight (F x) z * f x z) (fun r z => weight r z * target r z)
    (fun r => C * ε r) (fun r hr => selectedResidue_weighted_condition_error
      p F stride cells W hW hZ f target weight hC hweight r hr (he r hr)) φ hφ
  simpa only [FiniteProbabilityWeights.mean_const_mul] using h

end Erdos3

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

variable (q : ℕ)

local notation "tupleType" => PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim)
  (allocatedPrincipalSides B U b S)
local notation "tuples" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
local notation "labelType" => PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod q
abbrev AllocatedPositiveResidue :=
  {r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod q //
    0 < (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
        (Finset.univ.filter (fun y => principalResidueLabel q y = r))}

local notation "activeAxes" => {a : {a // allocatedGridAxis (I := I) U b S.value a} //
  allocatedActiveGrid B U b S a}

structure AllocatedResidueSiteWitness (r : (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod q)) where
  representative : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim)
    (allocatedPrincipalSides B U b S)
  label_eq : principalResidueLabel q representative = r
  positive : 0 < (tuples).mass (Finset.univ.filter
    (fun y => principalResidueLabel q y = principalResidueLabel q representative))
  expansion : activeAxes → ScalarSiteExpansion.{0,0} (Finset (Fin dim))

variable {r : (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod q)}
variable (w : AllocatedResidueSiteWitness (dim := dim) B U b S q r)
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type uQ} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (f : ((Σ a : {a // ¬allocatedGridAxis (I := I) U b S.value a},
  {t : Finset (Fin dim) // t ∈ boundedBooleanJetRows (Fin dim) ((Sigma.fst (Subtype.val a)).val + 1)}) → ℝ) → ℝ)

noncomputable def allocatedResidueWitnessProfile : EuclideanJetLayers U (rowTypes) → ℂ :=
  allocatedActiveSiteProfile B U b hR hσ S rowSets x hb o bW d q
    w.representative w.positive f w.expansion

noncomputable def allocatedSupportedResidueSiteProfile
    (W : (r : (AllocatedPositiveResidue (dim := dim) B U b S q)) → AllocatedResidueSiteWitness (dim := dim) B U b S q r.val)
    (r : (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod q)) : EuclideanJetLayers U (rowTypes) → ℂ :=
  if hr : 0 < (tuples).mass (Finset.univ.filter (fun y => principalResidueLabel q y = r)) then
    allocatedResidueWitnessProfile B U b hR hσ S q (W ⟨r, hr⟩) x hb o bW d f
  else fun _ => 0

theorem allocatedSupportedResidueSiteProfile_positive
    (W : (r : (AllocatedPositiveResidue (dim := dim) B U b S q)) → AllocatedResidueSiteWitness (dim := dim) B U b S q r.val)
    (r : (AllocatedPositiveResidue (dim := dim) B U b S q)) :
    allocatedSupportedResidueSiteProfile B U b hR hσ S q x hb o bW d f W r.val =
      allocatedResidueWitnessProfile B U b hR hσ S q (W r) x hb o bW d f := by
  unfold allocatedSupportedResidueSiteProfile
  rw [dite_eq_left r.property]

theorem allocatedResidueWitnessProfile_error
    (hr : 0 < (tuples).mass (Finset.univ.filter (fun y => principalResidueLabel q y = r))) :
    (fun z => ((tuples).condition _ hr).complexMean (fun y =>
      (allocatedWholeMaskedCoveredProfile (O := rowTypes) B U b hR hσ S x (rows) hb o bW d y q f z : ℂ)) -
      allocatedResidueWitnessProfile B U b hR hσ S q w x hb o bW d f z) =
    allocatedSelectedConditionalError (O := rowTypes) B U b hR hσ S x (rows) hb o bW d q
      w.representative w.positive (allocatedActiveGrid B U b S) f
      (allocatedActiveSiteApproximation B U b S rowSets w.expansion)
      (allocatedActiveNaturalVolume B U b S rowSets) := by
  rcases w with ⟨y₀, hy₀, hcell, e⟩
  subst r
  simpa only [allocatedResidueWitnessProfile, FiniteProbabilityWeights.complexMean_ofReal] using
    allocatedActiveSiteProfile_error B U b hR hσ S rowSets x hb o bW d q y₀ hcell f e

theorem allocatedSupportedResidueSiteProfile_error
    (W : (r : AllocatedPositiveResidue (dim := dim) B U b S q) → AllocatedResidueSiteWitness (dim := dim) B U b S q r.val)
    (r : AllocatedPositiveResidue (dim := dim) B U b S q) :
    (fun z => ((tuples).condition _ r.property).complexMean (fun y =>
      (allocatedWholeMaskedCoveredProfile (O := rowTypes) B U b hR hσ S x (rows) hb o bW d y q f z : ℂ)) -
      allocatedSupportedResidueSiteProfile B U b hR hσ S q x hb o bW d f W r.val z) =
    allocatedSelectedConditionalError (O := rowTypes) B U b hR hσ S x (rows) hb o bW d q
      (W r).representative (W r).positive (allocatedActiveGrid B U b S) f
      (allocatedActiveSiteApproximation B U b S rowSets (W r).expansion)
      (allocatedActiveNaturalVolume B U b S rowSets) := by
  rw [allocatedSupportedResidueSiteProfile_positive]
  exact allocatedResidueWitnessProfile_error B U b hR hσ S q (W r) x hb o bW d f r.property

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
variable (w : AllocatedResidueSiteWitness (dim := dim) B U b S q r)

def AllocatedResidueSiteSampling (δ : ℝ) : Prop :=
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
      hb o bW d q w.representative w.positive (allocatedActiveGrid B U b S) f
      (allocatedActiveSiteApproximation B U b S rowSets w.expansion)
      (allocatedActiveNaturalVolume B U b S rowSets)
    let mass := δ * A *
      (2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, (rowTypes) a.1)
    ∃ _hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells W z,
      selectedResidueDensityMass stride cells W
        (fun z => ‖error (physicalCubeRowSample (O := rowTypes) U d (rows) p hmp (standardPhysicalCubeOutput z))‖)
        ≤ mass + 2 * δFourier + ε

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "active" => allocatedActiveGrid B U b S
local notation "activeAxes" => {a : {a // grid a} // active a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "axisN" => allocatedGridNaturalScale B U b S
local notation "volumeN" => allocatedActiveNaturalVolume B U b S rowSets
local notation "rowFamily" => (fun a : (Σ j : Fin m, Fin (n j)) => rowSets (Sigma.fst a))

variable (hq : 0 < q) (hsize : (Fintype.card (Fin dim) + 1) * q ≤ S.value)
variable (P δ Λ : ℝ)
variable (M : {a : {a // allocatedGridAxis (I := I) U b S.value a} // allocatedActiveGrid B U b S a} → ℕ)
variable [∀ a, NeZero (M a)]

local notation "pointTolerance" => allocatedSitePointTolerance (G := G) B rowSets δ
local notation "trueCap" => allocatedGridFamilyCap B (rowFamily) P + 1
local notation "halfAccuracy" => uniformProductAccuracy (Fintype.card (Σ j : Fin m, Fin (n j))) trueCap pointTolerance / 2
local notation "torus" => (fun a : activeAxes => allocatedGridTorusFactor B (Fin dim) (ig (Subtype.val a)))
local notation "cap" => (fun a : activeAxes => allocatedGridPointCap B P (ig (Subtype.val a)) (rowSets (Sigma.fst (ig (Subtype.val a)))))
local notation "siteH" => (fun a : activeAxes =>
  allocatedNaturalSiteRadius (G := G) B (Sigma.fst (ig (Subtype.val a))) (Sigma.snd (ig (Subtype.val a))) (rowSets (Sigma.fst (ig (Subtype.val a)))) + 1 / 4)
local notation "bias" => (fun a : activeAxes => positiveModerateRetainedBias (Fin.val (Sigma.fst (ig (Subtype.val a))))
  (Finset.card (rowSets (Sigma.fst (ig (Subtype.val a))))) ((layerTailDegree m + 2) * Finset.card (rowSets (Sigma.fst (ig (Subtype.val a)))))
  P ((torus) a : ℝ) ((2 * ((torus) a : ℝ)) ^ Finset.card (rowSets (Sigma.fst (ig (Subtype.val a))))) halfAccuracy)
local notation "freq" => (fun a : activeAxes => Real.toNNReal (positiveRetainedFrequencyBound
  (Fin.val (Sigma.fst (ig (Subtype.val a)))) (Finset.card (rowSets (Sigma.fst (ig (Subtype.val a))))) P ((torus) a : ℝ) ((bias) a)))
include hq hsize in
theorem exists_allocated_residue_site_sampling
    (hP : 1 ≤ P) (hδ : 0 < δ) (hΛ : 0 ≤ Λ)
    (hgamma : ∀ a : activeAxes, principalProfileSize (R (ig a.val).1)
      (Finset.card (layerIntegerPrincipalSlots (G := G) B (ig a.val).1 (ig a.val).2)) ≤ S.value)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hcP : scalarCubePrimitiveEnvelope Empty L 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope (Fin dim) L 1 0 q ≤ P)
    (hM : ∀ a, M a = (torus) a * axisN a.val)
    (hB : ∀ a : activeAxes, positiveModerateSpectrumBlockCount (ig a.val).1.val
      (rowSets (ig a.val).1).card ((layerTailDegree m + 2) * (rowSets (ig a.val).1).card) ≤
        Fintype.card (B ⟨(ig a.val).1, Sum.inr (ig a.val).2⟩))
    (hHΛ : ∀ a, (siteH) a ≤ Real.exp Λ)
    (hδΛ : ∀ a, (halfAccuracy / ((cap) a + 1))⁻¹ ≤ Real.exp Λ)
    (hLΛ : ∀ a, ((CircleFourier.characterLipConstant * ((rowSets (ig a.val).1).card * (freq) a) + 4) *
      (2 : ℝ≥0) ^ Fintype.card (Fin dim) : ℝ≥0) ≤ Real.exp Λ) :
    ∃ W : (r : AllocatedPositiveResidue (dim := dim) B U b S q) → AllocatedResidueSiteWitness (dim := dim) B U b S q r.val,
      (∀ r, allocatedActiveSiteBounds B U b S rowSets P pointTolerance Λ M (W r).expansion) ∧
      ∀ r, AllocatedResidueSiteSampling B U b hR hσ S q (W r) δ := by
  have hreps (r : AllocatedPositiveResidue (dim := dim) B U b S q) :=
    (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).exists_mem_positive_fiber
      (principalResidueLabel q) r.val r.property
  choose rep hrep using hreps
  have hc (r : AllocatedPositiveResidue (dim := dim) B U b S q) :
      0 < (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
        (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)).mass
          (Finset.univ.filter (fun y => principalResidueLabel q y = principalResidueLabel q (rep r))) := by
    simpa only [hrep r] using r.property
  have hex (r : AllocatedPositiveResidue (dim := dim) B U b S q) :=
    exists_allocated_active_site_uniform_sampled_error
      B U b hR hσ S q (rep r) (hc r) hq hsize P δ Λ M hP hδ hΛ hgamma L hL hcP hsP hM hB hHΛ hδΛ hLΛ
  choose e hb he using hex
  let W : (r : AllocatedPositiveResidue (dim := dim) B U b S q) → AllocatedResidueSiteWitness (dim := dim) B U b S q r.val :=
    fun r => ⟨rep r, hrep r, hc r, e r⟩
  refine ⟨W, ?_, ?_⟩
  · intro r
    exact hb r
  · intro r
    simpa only [AllocatedResidueSiteSampling, W] using @he r

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
  AllocatedResidueSiteWitness (dim := dim) B U b S q r.val)
variable (hWitness : ∀ r, AllocatedResidueSiteSampling.{uG,uI,uB,uJ,uQ,uX}
  B U b hR hσ S q (witnesses r) δ)

include hWitness in
theorem allocated_residue_site_sampled_error :
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
    let target := allocatedSupportedResidueSiteProfile B U b hR hσ S q x hb o bW d f witnesses
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
    dsimp only [AllocatedResidueSiteSampling] at hc
    obtain ⟨hZ, hbound⟩ := @hc K hSampling x hb o Q _ bW d _ _ f CM Cf hCM hfb
      (hmask (witnesses rr).representative) hperiod C V hC hV
      X _ _ P₀ hP₀ hn hdim _ _ _ μ _ _ ν _ _ p hp hmp stride hs R₁ S₀ ρ ε
      hS hSP hρ hε hρP hεP hstride H hsize₁ hrank hR₁ cells hcells W hW hwidth
      δFourier LFourier hδFourier hLFourier hamb hδL hLip hfreqP hcoeffP
    refine ⟨hZ, ?_⟩
    have hid := allocatedSupportedResidueSiteProfile_error B U b hR hσ S q x hb o bW d f witnesses rr
    have hfun :
        (fun z => ‖(law.condition _ hr).complexMean (fun y => source y z) - targetSample r z‖) =
        (fun z => ‖allocatedSelectedConditionalError (O := rowTypes) B U b hR hσ S x (rows)
          hb o bW d q (witnesses rr).representative (witnesses rr).positive
          (allocatedActiveGrid B U b S) f
          (allocatedActiveSiteApproximation B U b S rowSets (witnesses rr).expansion)
          (allocatedActiveNaturalVolume B U b S rowSets) (sample z)‖) := by
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

section Constructed

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "active" => allocatedActiveGrid B U b S
local notation "activeAxes" => {a : {a // grid a} // active a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "axisN" => allocatedGridNaturalScale B U b S
local notation "volumeN" => allocatedActiveNaturalVolume B U b S rowSets
local notation "rowFamily" => (fun a : (Σ j : Fin m, Fin (n j)) => rowSets (Sigma.fst a))

variable (hq : 0 < q) (hsize : (Fintype.card (Fin dim) + 1) * q ≤ S.value)
variable (P Λ : ℝ)
variable (M : {a : {a // allocatedGridAxis (I := I) U b S.value a} // allocatedActiveGrid B U b S a} → ℕ)
variable [∀ a, NeZero (M a)]

local notation "pointTolerance" => allocatedSitePointTolerance (G := G) B rowSets δ
local notation "trueCap" => allocatedGridFamilyCap B (rowFamily) P + 1
local notation "halfAccuracy" => uniformProductAccuracy (Fintype.card (Σ j : Fin m, Fin (n j))) trueCap pointTolerance / 2
local notation "torus" => (fun a : activeAxes => allocatedGridTorusFactor B (Fin dim) (ig (Subtype.val a)))
local notation "cap" => (fun a : activeAxes => allocatedGridPointCap B P (ig (Subtype.val a)) (rowSets (Sigma.fst (ig (Subtype.val a)))))
local notation "siteH" => (fun a : activeAxes =>
  allocatedNaturalSiteRadius (G := G) B (Sigma.fst (ig (Subtype.val a))) (Sigma.snd (ig (Subtype.val a))) (rowSets (Sigma.fst (ig (Subtype.val a)))) + 1 / 4)
local notation "bias" => (fun a : activeAxes => positiveModerateRetainedBias (Fin.val (Sigma.fst (ig (Subtype.val a))))
  (Finset.card (rowSets (Sigma.fst (ig (Subtype.val a))))) ((layerTailDegree m + 2) * Finset.card (rowSets (Sigma.fst (ig (Subtype.val a)))))
  P ((torus) a : ℝ) ((2 * ((torus) a : ℝ)) ^ Finset.card (rowSets (Sigma.fst (ig (Subtype.val a))))) halfAccuracy)
local notation "freq" => (fun a : activeAxes => Real.toNNReal (positiveRetainedFrequencyBound
  (Fin.val (Sigma.fst (ig (Subtype.val a)))) (Finset.card (rowSets (Sigma.fst (ig (Subtype.val a))))) P ((torus) a : ℝ) ((bias) a)))
include hq hsize in
theorem exists_allocated_residue_site_sampled_error
    (hP : 1 ≤ P) (hδ : 0 < δ) (hΛ : 0 ≤ Λ)
    (hgamma : ∀ a : activeAxes, principalProfileSize (R (ig a.val).1)
      (Finset.card (layerIntegerPrincipalSlots (G := G) B (ig a.val).1 (ig a.val).2)) ≤ S.value)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hcP : scalarCubePrimitiveEnvelope Empty L 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope (Fin dim) L 1 0 q ≤ P)
    (hM : ∀ a, M a = (torus) a * axisN a.val)
    (hB : ∀ a : activeAxes, positiveModerateSpectrumBlockCount (ig a.val).1.val
      (rowSets (ig a.val).1).card ((layerTailDegree m + 2) * (rowSets (ig a.val).1).card) ≤
        Fintype.card (B ⟨(ig a.val).1, Sum.inr (ig a.val).2⟩))
    (hHΛ : ∀ a, (siteH) a ≤ Real.exp Λ)
    (hδΛ : ∀ a, (halfAccuracy / ((cap) a + 1))⁻¹ ≤ Real.exp Λ)
    (hLΛ : ∀ a, ((CircleFourier.characterLipConstant * ((rowSets (ig a.val).1).card * (freq) a) + 4) *
      (2 : ℝ≥0) ^ Fintype.card (Fin dim) : ℝ≥0) ≤ Real.exp Λ) :
    ∃ K : ℕ, 2 ≤ K ∧
      ∃ witnesses : (r : AllocatedPositiveResidue (dim := dim) B U b S q) →
        AllocatedResidueSiteWitness (dim := dim) B U b S q r.val,
      (∀ r, allocatedActiveSiteBounds B U b S rowSets P pointTolerance Λ M (witnesses r).expansion) ∧
      ∀
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
    let target := allocatedSupportedResidueSiteProfile B U b hR hσ S q x hb o bW d f witnesses
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
  obtain ⟨K, hK, hSampling⟩ :=
    exists_allocated_boolean_rows_sampling.{uX,uJ,uG,uI,uB,uQ} m dim
  obtain ⟨witnesses, hBounds, hWitnesses⟩ := exists_allocated_residue_site_sampling
    B U b hR hσ S q hq hsize P δ Λ M hP hδ hΛ hgamma L hL hcP hsP hM hB hHΛ hδΛ hLΛ
  refine ⟨K, hK, witnesses, hBounds, ?_⟩
  exact allocated_residue_site_sampled_error B U b hR hσ S q δ witnesses hWitnesses
    (K := K) (@hSampling (fun j => Finset.Subtype.fintype (rowSets j)))

end Constructed

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
  AllocatedResidueSiteWitness (dim := dim) B U b S q r.val)
variable (hWitness : ∀ r, AllocatedResidueSiteSampling.{uG,uI,uB,uJ,uQ,uX}
  B U b hR hσ S q (witnesses r) δ)

include hWitness in
theorem allocated_residue_site_weighted_sampled_error :
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
    let target := allocatedSupportedResidueSiteProfile B U b hR hσ S q x hb o bW d f witnesses
    let mass := δ * A *
      (2 * (∑ j, (C j : ℝ) * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, (rowTypes) a.1)
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells W z,
      ∀ (Cweight : ℝ), 0 ≤ Cweight →
      ∀ weight : (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod q) →
          (Option (Fin dim) × X → ℤ) → ℂ,
      (∀ r z, ‖weight r z‖ ≤ Cweight) →
      let sample := fun z : Option (Fin dim) × X → ℤ =>
        physicalCubeRowSample (O := rowTypes) U d (rows) p hmp (standardPhysicalCubeOutput z)
      let error := fun z : Option (Fin dim) × X → ℤ =>
        law.complexMean (fun y₀ => weight (principalResidueLabel q y₀) z *
          (allocatedWholeMaskedCoveredProfile (O := rowTypes) B U b hR hσ S x (rows) hb o bW d y₀ q f (sample z) : ℂ)) -
        (law.fiberLaw (principalResidueLabel q)).complexMean (fun r => weight r z * target r (sample z))
      selectedResidueDensityMass stride cells W (fun z => ‖error z‖) ≤ Cweight * (mass + 2 * δFourier + ε) ∧
      ∀ φ : (Option (Fin dim) × X → ℤ) → ℂ, (∀ z, ‖φ z‖ ≤ 1) →
        ‖∑' z, ((selectedResidueSmoothPMF stride cells W hW hZ z).toReal : ℂ) *
          (error z * φ z)‖ ≤ Cweight * (mass + 2 * δFourier + ε) := by
  intro K hSampling x hb o Q _ bW d _ _ f CM Cf hCM hfb hmask hperiod C V hC hV
    X _ _ P₀ hP₀ hn hdim _ _ _ μ _ _ ν _ _ p hp hmp stride hs R₁ S₀ ρ ε
    hS hSP hρ hε hρP hεP hstride H hsize₁ hrank hR₁ cells hcells W hW hwidth
    δFourier LFourier hδFourier hLFourier hamb hδL A hLip hfreqP hcoeffP law target mass
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
    dsimp only [AllocatedResidueSiteSampling] at hc
    obtain ⟨hZ, hbound⟩ := @hc K hSampling x hb o Q _ bW d _ _ f CM Cf hCM hfb
      (hmask (witnesses rr).representative) hperiod C V hC hV
      X _ _ P₀ hP₀ hn hdim _ _ _ μ _ _ ν _ _ p hp hmp stride hs R₁ S₀ ρ ε
      hS hSP hρ hε hρP hεP hstride H hsize₁ hrank hR₁ cells hcells W hW hwidth
      δFourier LFourier hδFourier hLFourier hamb hδL hLip hfreqP hcoeffP
    refine ⟨hZ, ?_⟩
    have hid := allocatedSupportedResidueSiteProfile_error B U b hR hσ S q x hb o bW d f witnesses rr
    have hfun :
        (fun z => ‖(law.condition _ hr).complexMean (fun y => source y z) - targetSample r z‖) =
        (fun z => ‖allocatedSelectedConditionalError (O := rowTypes) B U b hR hσ S x (rows)
          hb o bW d q (witnesses rr).representative (witnesses rr).positive
          (allocatedActiveGrid B U b S) f
          (allocatedActiveSiteApproximation B U b S rowSets (witnesses rr).expansion)
          (allocatedActiveNaturalVolume B U b S rowSets) (sample z)‖) := by
      funext z
      exact congrArg norm (congrFun hid (sample z))
    rw [hfun]
    exact hbound
  obtain ⟨r₀, hr₀⟩ := (law.fiberLaw (principalResidueLabel q)).exists_weight_pos
  rw [law.fiberLaw_weight_eq_mass] at hr₀
  obtain ⟨hZ, _⟩ := hlocal r₀ hr₀
  have heach r hr := (hlocal r hr).choose_spec
  refine ⟨hZ, ?_⟩
  intro Cweight hCweight weight hweight sample' error
  refine ⟨?_, ?_⟩
  · have h := selectedResidue_supported_fiber_weighted_error law (principalResidueLabel q)
      stride cells W hW hZ source targetSample weight hCweight hweight
      (fun _ => mass + 2 * δFourier + ε) heach
    simpa only [FiniteProbabilityWeights.mean_const] using h
  · intro φ hφ
    have h := selectedResidue_supported_fiber_weighted_test_error law (principalResidueLabel q)
      stride cells W hW hZ source targetSample weight hCweight hweight
      (fun _ => mass + 2 * δFourier + ε) heach φ hφ
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
  AllocatedResidueSiteWitness (dim := dim) B U b S q r.val)
variable (hWitness : ∀ r, AllocatedResidueSiteSampling.{uG,uI,uB,uJ,uQ,uX}
  B U b hR hσ S q (witnesses r) δ)

include hWitness in
theorem allocated_residue_site_primitive_error
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
    (_hperiod : ∀ j, integerScalarLattice (rowTypes j) (q : ℤ) ≤
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
    (H : X → ℝ) (_hsize : ∀ x, Real.exp ((P₀ + K) ^ K) ≤ H x)
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H R₁ (U j) (p j))
    (_hR : Real.exp ((P₀ + K) ^ K) ≤ R₁)
    (cells : Finset (ColumnResiduePattern (Option (Fin dim)) X stride)) (_hcells : cells.Nonempty)
    (W : Option (Fin dim) × X → ℝ) (hW : ∀ z, 0 < W z) (_hwidth : ∀ z, ρ * H z.2 ≤ W z),
    let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let target := allocatedSupportedResidueSiteProfile B U b hR hσ S q x hb o bW d f witnesses
    let error := fun y : EuclideanJetLayers U (rowTypes) =>
      law.complexMean (fun y₀ =>
        (allocatedWholeMaskedCoveredProfile (O := rowTypes) B U b hR hσ S x (rows) hb o bW d y₀ q f y : ℂ)) -
      (law.fiberLaw (principalResidueLabel q)).complexMean (fun r => target r y)
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells W z,
      selectedResidueDensityMass stride cells W
        (fun z => ‖error (physicalCubeRowSample (O := rowTypes) U d (rows) p hmp (standardPhysicalCubeOutput z))‖)
        ≤ Real.exp (-E) ∧
      ∀ φ : (Option (Fin dim) × X → ℤ) → ℂ, (∀ z, ‖φ z‖ ≤ 1) →
        ‖∑' z, ((selectedResidueSmoothPMF stride cells W hW hZ z).toReal : ℂ) *
          (error (physicalCubeRowSample (O := rowTypes) U d (rows) p hmp (standardPhysicalCubeOutput z)) * φ z)‖
          ≤ Real.exp (-E) := by
  intro K hSampling x hb o Q _ bW d _ _ f CM Cf hCM hfb hCMexp hCfexp hmask hperiod C V hC hV
    hCexp hVexp X _ _ P₀ hP₀ hn hdim hbudget _ _ _ μ _ _ ν _ _ p hp hmp stride hs R₁ S₀ ρ
    hS hSP hρ hρP hstride H hsize₁ hrank hR₁ cells hcells W hW hwidth law target error
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
  have hprevious := allocated_residue_site_sampled_error B U b hR hσ S q δ witnesses hWitness
    (K := K) hSampling
  obtain ⟨hZ, hmean, htest⟩ := @hprevious x hb o Q _ bW d _ _ f CM Cf hCM hfb hmask hperiod C V hC hV
    X _ _ P₀ hP₀ hn hdim _ _ _ μ _ _ ν _ _ p hp hmp stride hs R₁ S₀ ρ (physicalIdealErrorShare E 1)
    hS hSP hρ (physicalIdealErrorShare_pos E 1) hρP hεP hstride H hsize₁ hrank hR₁ cells hcells W hW hwidth
    (physicalIdealErrorShare E 1) (allocatedSiteErrorFourierInput m p₁ w v)
    (physicalIdealErrorShare_pos E 1) hLF hamb hδL hLip (hfreq.trans heP) (hcoeff.trans heP)
  have hmass := allocatedSiteSpatial_primitive_error_budget B U b (rows) hrowdim
    (fun _ => Subtype.val_injective) hb bW M₀ q hqM CM Cf C hp₁ hw hvars hI hn₁ hJ
    hM₀ hCexp hCMexp hCfexp hδ (le_refl (physicalIdealErrorShare E 1))
    (le_refl (physicalIdealErrorShare E 1))
  exact ⟨hZ, hmean.trans hmass, fun φ hφ => (htest φ hφ).trans hmass⟩

section Constructed

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "active" => allocatedActiveGrid B U b S
local notation "activeAxes" => {a : {a // grid a} // active a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "axisN" => allocatedGridNaturalScale B U b S
local notation "volumeN" => allocatedActiveNaturalVolume B U b S rowSets
local notation "rowFamily" => (fun a : (Σ j : Fin m, Fin (n j)) => rowSets (Sigma.fst a))

variable (hq : 0 < q) (hsize : (Fintype.card (Fin dim) + 1) * q ≤ S.value)
variable (P Λ : ℝ)
variable (M : {a : {a // allocatedGridAxis (I := I) U b S.value a} // allocatedActiveGrid B U b S a} → ℕ)
variable [∀ a, NeZero (M a)]

local notation "pointTolerance" => allocatedSitePointTolerance (G := G) B rowSets δ
local notation "trueCap" => allocatedGridFamilyCap B (rowFamily) P + 1
local notation "halfAccuracy" => uniformProductAccuracy (Fintype.card (Σ j : Fin m, Fin (n j))) trueCap pointTolerance / 2
local notation "torus" => (fun a : activeAxes => allocatedGridTorusFactor B (Fin dim) (ig (Subtype.val a)))
local notation "cap" => (fun a : activeAxes => allocatedGridPointCap B P (ig (Subtype.val a)) (rowSets (Sigma.fst (ig (Subtype.val a)))))
local notation "siteH" => (fun a : activeAxes =>
  allocatedNaturalSiteRadius (G := G) B (Sigma.fst (ig (Subtype.val a))) (Sigma.snd (ig (Subtype.val a))) (rowSets (Sigma.fst (ig (Subtype.val a)))) + 1 / 4)
local notation "bias" => (fun a : activeAxes => positiveModerateRetainedBias (Fin.val (Sigma.fst (ig (Subtype.val a))))
  (Finset.card (rowSets (Sigma.fst (ig (Subtype.val a))))) ((layerTailDegree m + 2) * Finset.card (rowSets (Sigma.fst (ig (Subtype.val a)))))
  P ((torus) a : ℝ) ((2 * ((torus) a : ℝ)) ^ Finset.card (rowSets (Sigma.fst (ig (Subtype.val a))))) halfAccuracy)
local notation "freq" => (fun a : activeAxes => Real.toNNReal (positiveRetainedFrequencyBound
  (Fin.val (Sigma.fst (ig (Subtype.val a)))) (Finset.card (rowSets (Sigma.fst (ig (Subtype.val a))))) P ((torus) a : ℝ) ((bias) a)))
include hq hsize in
theorem exists_allocated_residue_site_primitive_error
    {p₁ w v E : ℝ} (hp₁ : 0 ≤ p₁) (hw : 0 ≤ w) (hv : 0 ≤ v) (hE : 0 ≤ E)
    (hdimSmall : dim ≤ m + 1)
    (hvars : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ p₁)
    (hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ p₁) (hn₁ : ∀ j, (n j : ℝ) ≤ p₁)
    (hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ p₁)
    (M₀ : ℕ) (hqM : q ≤ M₀ ^ (m + 1)) (hM₀ : (M₀ : ℝ) ≤ Real.exp p₁)
    (hS₁ : (S.value : ℝ) ≤ Real.exp p₁)
    (hδbudget : δ ≤ allocatedSitePrimitiveTolerance m p₁ w v E) (hEbudget : E + 4 ≤ p₁)
    (hP : 1 ≤ P) (hδ : 0 < δ) (hΛ : 0 ≤ Λ)
    (hgamma : ∀ a : activeAxes, principalProfileSize (R (ig a.val).1)
      (Finset.card (layerIntegerPrincipalSlots (G := G) B (ig a.val).1 (ig a.val).2)) ≤ S.value)
    (L : ℝ≥0) (hL : LipschitzWith L Real.smoothTransition)
    (hcP : scalarCubePrimitiveEnvelope Empty L 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope (Fin dim) L 1 0 q ≤ P)
    (hM : ∀ a, M a = (torus) a * axisN a.val)
    (hB : ∀ a : activeAxes, positiveModerateSpectrumBlockCount (ig a.val).1.val
      (rowSets (ig a.val).1).card ((layerTailDegree m + 2) * (rowSets (ig a.val).1).card) ≤
        Fintype.card (B ⟨(ig a.val).1, Sum.inr (ig a.val).2⟩))
    (hHΛ : ∀ a, (siteH) a ≤ Real.exp Λ)
    (hδΛ : ∀ a, (halfAccuracy / ((cap) a + 1))⁻¹ ≤ Real.exp Λ)
    (hLΛ : ∀ a, ((CircleFourier.characterLipConstant * ((rowSets (ig a.val).1).card * (freq) a) + 4) *
      (2 : ℝ≥0) ^ Fintype.card (Fin dim) : ℝ≥0) ≤ Real.exp Λ) :
    ∃ K : ℕ, 2 ≤ K ∧
      ∃ witnesses : (r : AllocatedPositiveResidue (dim := dim) B U b S q) →
        AllocatedResidueSiteWitness (dim := dim) B U b S q r.val,
      (∀ r, allocatedActiveSiteBounds B U b S rowSets P pointTolerance Λ M (witnesses r).expansion) ∧
      ∀
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
    (_hperiod : ∀ j, integerScalarLattice (rowTypes j) (q : ℤ) ≤
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
    (H : X → ℝ) (_hsize : ∀ x, Real.exp ((P₀ + K) ^ K) ≤ H x)
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H R₁ (U j) (p j))
    (_hR : Real.exp ((P₀ + K) ^ K) ≤ R₁)
    (cells : Finset (ColumnResiduePattern (Option (Fin dim)) X stride)) (_hcells : cells.Nonempty)
    (W : Option (Fin dim) × X → ℝ) (hW : ∀ z, 0 < W z) (_hwidth : ∀ z, ρ * H z.2 ≤ W z),
    let law := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
      (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)
    let target := allocatedSupportedResidueSiteProfile B U b hR hσ S q x hb o bW d f witnesses
    let error := fun y : EuclideanJetLayers U (rowTypes) =>
      law.complexMean (fun y₀ =>
        (allocatedWholeMaskedCoveredProfile (O := rowTypes) B U b hR hσ S x (rows) hb o bW d y₀ q f y : ℂ)) -
      (law.fiberLaw (principalResidueLabel q)).complexMean (fun r => target r y)
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells W z,
      selectedResidueDensityMass stride cells W
        (fun z => ‖error (physicalCubeRowSample (O := rowTypes) U d (rows) p hmp (standardPhysicalCubeOutput z))‖)
        ≤ Real.exp (-E) ∧
      ∀ φ : (Option (Fin dim) × X → ℤ) → ℂ, (∀ z, ‖φ z‖ ≤ 1) →
        ‖∑' z, ((selectedResidueSmoothPMF stride cells W hW hZ z).toReal : ℂ) *
          (error (physicalCubeRowSample (O := rowTypes) U d (rows) p hmp (standardPhysicalCubeOutput z)) * φ z)‖
          ≤ Real.exp (-E) := by
  obtain ⟨K, hK, hSampling⟩ :=
    exists_allocated_boolean_rows_sampling.{uX,uJ,uG,uI,uB,uQ} m dim
  obtain ⟨witnesses, hBounds, hWitnesses⟩ := exists_allocated_residue_site_sampling
    B U b hR hσ S q hq hsize P δ Λ M hP hδ hΛ hgamma L hL hcP hsP hM hB hHΛ hδΛ hLΛ
  refine ⟨K, hK, witnesses, hBounds, ?_⟩
  exact allocated_residue_site_primitive_error B U b hR hσ S q δ witnesses hWitnesses
    hp₁ hw hv hE hdimSmall hvars hI hn₁ hJ M₀ hqM hM₀ hS₁ hδbudget hEbudget
    (K := K) (@hSampling (fun j => Finset.Subtype.fintype (rowSets j)))

end Constructed

end Erdos3.VectorPolynomial

end

end OAI
