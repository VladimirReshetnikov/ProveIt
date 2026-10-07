import OAI.Combinatorics.Progressions.Estimates.AllocatedCoveredFixedTest
import OAI.Combinatorics.Progressions.Estimates.ComplexSampledSquarePerturbation
import OAI.Combinatorics.Progressions.Estimates.CoveredJetSampleMeasurable
import OAI.Combinatorics.Progressions.Geometry.PrincipalCubeSupportedCell

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped Classical

variable {K : Type*} [Fintype K] {m : ℕ} {J I B : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (B j)] {n : Fin m → ℕ}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

variable [CompactSpace (CoefficientTorus (K := K) U)]
variable [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

omit [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
  [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ] in
def CoefficientDeckDensityLaw
    (source : Measure (CoefficientSamplerArrays (K := K) I n))
    (density : CoefficientTorus (K := K) U → ℝ) (d : ℕ) [NeZero d] : Prop :=
    (source.prod (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).toMeasure).map
      (fun x : CoefficientSamplerArrays (K := K) I n × CoefficientDeckResidues (K := K) B d =>
        canonicalCoefficientDeckSample U bW b hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) x.1 x.2) =
      realDensityMeasure μ (fun y => density (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d y))

include ν in
theorem canonicalCoefficientDeckSample_law_of_eq
    (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
    (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)
    (hw : ∀ j i e, 0 < w j i e)
    (hs : ∀ j e x, mixedCoefficientDensity (fun i => c j i e) (fun i => w j i e)
      (fun i => p j i e) x ≠ 0 → normalizedLatticePoint (euclideanSubspace (U j)) (b j)
        (orthonormalMixedChart (o j) x) ∈ standardLatticeSmallBox (J j))
    (source : Measure (CoefficientSamplerArrays (K := K) I n))
    (density : CoefficientTorus (K := K) U → ℝ)
    (hsource : source = Measure.pi (fun j => mixedScalarArrayLaw (c j) (w j) (p j)))
    (hdensity : density = canonicalCoefficientDensity U b hb o c w p)
    (d : ℕ) [NeZero d] :
    CoefficientDeckDensityLaw U bW b hb o μ source density d := by
  subst source density
  exact canonicalCoefficientDeckSample_law U bW b hb o μ ν c w p hw hs d

omit [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
  [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ] in
theorem CoefficientDeckDensityLaw.test_integral
    (source : Measure (CoefficientSamplerArrays (K := K) I n))
    (density : CoefficientTorus (K := K) U → ℝ) (d : ℕ) [NeZero d]
    (hlaw : CoefficientDeckDensityLaw U bW b hb o μ source density d)
    (φ : CoefficientTorus (K := K) U → ℂ) (hφ : Measurable φ) :
    (∫ p : CoefficientSamplerArrays (K := K) I n × CoefficientDeckResidues (K := K) B d,
      φ (canonicalCoefficientDeckSample U bW b hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) p.1 p.2)
      ∂source.prod (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).toMeasure) =
      ∫ z, φ z ∂realDensityMeasure μ (fun z => density (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d z)) := by
  have h := (integral_map (μ := source.prod (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).toMeasure)
    (canonicalCoefficientDeckSample_measurable U bW b hb o d).aemeasurable hφ.aestronglyMeasurable).symm
  exact h.trans (congrArg (fun ν => ∫ z, φ z ∂ν) hlaw)

omit [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
  [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ] in
theorem CoefficientDeckDensityLaw.mapped_test_integral
    (source : Measure (CoefficientSamplerArrays (K := K) I n))
    (density : CoefficientTorus (K := K) U → ℝ) (d : ℕ) [NeZero d]
    (hlaw : CoefficientDeckDensityLaw U bW b hb o μ source density d)
    {Y : Type*} [MeasurableSpace Y] (ξ : Measure Y)
    (T : CoefficientTorus (K := K) U → Y) (hT : Measurable T)
    (g : Y → ℝ) (hgm : Measurable g) (hg0 : ∀ y, 0 ≤ g y)
    (hglaw : (realDensityMeasure μ (fun z => density
      (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d z))).map T = realDensityMeasure ξ g)
    (φ : Y → ℂ) (hφ : Measurable φ) :
    (∫ p : CoefficientSamplerArrays (K := K) I n × CoefficientDeckResidues (K := K) B d,
      φ (T (canonicalCoefficientDeckSample U bW b hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) p.1 p.2))
      ∂source.prod (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).toMeasure) =
      ∫ z, (g z : ℂ) * φ z ∂ξ := by
  have hfirst := hlaw.test_integral U bW b hb o μ source density d (φ ∘ T) (hφ.comp hT)
  have hsecond := (integral_map
    (μ := realDensityMeasure μ (fun z => density (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d z)))
    hT.aemeasurable hφ.aestronglyMeasurable).symm
  rw [hglaw] at hsecond
  exact hfirst.trans (hsecond.trans (realDensityMeasure_integral_complex ξ g hgm hg0 φ))

omit [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
  [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ] in
theorem CoefficientDeckDensityLaw.mean_mapped_test_integral
    (source : Measure (CoefficientSamplerArrays (K := K) I n)) [IsProbabilityMeasure source]
    (density : CoefficientTorus (K := K) U → ℝ) (d : ℕ) [NeZero d]
    (hlaw : CoefficientDeckDensityLaw U bW b hb o μ source density d)
    {Y V : Type*} [MeasurableSpace Y] [Fintype V] (ξ : Measure Y) (law : FiniteProbabilityWeights V)
    (T : V → CoefficientTorus (K := K) U → Y) (hT : ∀ v, Measurable (T v))
    (g : V → Y → ℝ) (hgm : ∀ v, Measurable (g v)) (hg0 : ∀ v y, 0 ≤ g v y)
    (hgi : ∀ v, Integrable (g v) ξ)
    (hglaw : ∀ v, (realDensityMeasure μ (fun z => density
      (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d z))).map (T v) = realDensityMeasure ξ (g v))
    (φ : Y → ℂ) (hφ : Measurable φ) (hφb : ∀ y, ‖φ y‖ ≤ 1) :
    (∫ p : CoefficientSamplerArrays (K := K) I n × CoefficientDeckResidues (K := K) B d,
      law.complexMean (fun v => φ (T v (canonicalCoefficientDeckSample U bW b hb o d
        (Nat.pos_of_ne_zero (NeZero.ne d)) p.1 p.2)))
      ∂source.prod (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).toMeasure) =
      ∫ z, (law.mean (fun v => g v z) : ℂ) * φ z ∂ξ := by
  have hi (v) : Integrable (fun p : CoefficientSamplerArrays (K := K) I n × CoefficientDeckResidues (K := K) B d =>
      φ (T v (canonicalCoefficientDeckSample U bW b hb o d
        (Nat.pos_of_ne_zero (NeZero.ne d)) p.1 p.2)))
      (source.prod (PMF.uniformOfFintype (CoefficientDeckResidues (K := K) B d)).toMeasure) :=
    Integrable.of_bound ((hφ.comp (hT v)).comp
      (canonicalCoefficientDeckSample_measurable U bW b hb o d)).aestronglyMeasurable
      1 (Filter.Eventually.of_forall (fun p => hφb _))
  refine (law.complexMean_integral _ _ hi).symm.trans ?_
  have he (v) := CoefficientDeckDensityLaw.mapped_test_integral U bW b hb o μ source density d hlaw ξ
    (T v) (hT v) (g v) (hgm v) (hg0 v) (hglaw v) φ hφ
  exact (congrArg (fun f => law.complexMean f) (funext he)).trans
    (law.mean_density_test_integral ξ g hgi φ hφ hφb)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
local notation "source" => allocatedCoefficientSource B U basis hR hσ S
local notation "density" => allocatedCoefficientDensity B U basis hb o hR hσ S
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)
local notation "cover" => quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d

include ν in
theorem allocatedCoefficientDeckSample_density_law
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ C j * ‖z‖)
    (hsmall : ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4) :
    CoefficientDeckDensityLaw U bW basis hb o μ source density d := by
  exact canonicalCoefficientDeckSample_law_of_eq U bW basis hb o μ ν
    (allocatedLayerCenters B U basis S) (allocatedLayerWidths B U basis S)
    (allocatedLayerIntegerPMFs B U basis hR hσ S)
    (allocatedLayerWidths_pos B U basis hR hσ S)
    (allocatedLayerColumns_chart B U basis hR hσ S o hσ1 C hC hchart hsmall)
    source density rfl rfl d

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (x : G → IntegerScalarCubeBox α S.value)
local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (F : AllocatedFrozenCoefficients B U basis S × EuclideanJetLayers U O → ℂ)

local notation "source" => allocatedCoefficientSource B U basis hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U basis hR hσ S
variable (H₀ step₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH₀ : ∀ t, 0 < H₀ t)
variable (hsubset₀ : ∀ t, integerProgressionSupport (c₀ t) (step₀ t : ℤ) (H₀ t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (modulus : ℕ) (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "wholeLaw" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell
local notation "wholeRoot" y => allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y
local notation "wholeDirs" y => allocatedPhysicalCubeDirections B U basis S x y
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)
local notation "actual" => (∫ p, FiniteProbabilityWeights.complexMean wholeLaw (fun y =>
  F (Prod.fst ((allocatedCoefficientSplit B U basis S) (Prod.fst p)),
    euclideanCoefficientJetMap U (wholeRoot y) (wholeDirs y) rows
      (canonicalCoefficientDeckSample U bW basis hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) (Prod.fst p) (Prod.snd p))))
  ∂(Measure.prod source (PMF.toMeasure deck)))

noncomputable def allocatedProgressionCoveredExpectation : ℂ := actual

omit [DecidableEq G] [∀ index, DecidableEq (B index)]
  [∀ index, DecidableEq (O index)] in
theorem allocatedProgressionCoveredIntegrand_integrable
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S))
    (hF : Measurable F) (hFbound : ∀ p, ‖F p‖ ≤ 1) :
    Integrable (fun p : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n ×
      CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d =>
      F (((allocatedCoefficientSplit B U basis S) p.1).1,
        euclideanCoefficientJetMap U (wholeRoot y) (wholeDirs y) rows
          (canonicalCoefficientDeckSample U bW basis hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) p.1 p.2)))
      ((source).prod (deck).toMeasure) := by
  let : IsProbabilityMeasure source := allocatedCoefficientSource_probability B U basis hR hσ S
  apply Integrable.of_bound (C := 1)
  · exact (hF.comp
      ((((allocatedCoefficientSplit B U basis S).measurable.comp measurable_fst).fst).prodMk
        (canonicalCoefficientDeckSample_jet_measurable U o (wholeRoot y) (wholeDirs y)
          rows basis hb bW d))).aestronglyMeasurable
  · exact ae_of_all _ (fun p => hFbound _)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open MeasureTheory Module Submodule
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)
variable (x : G → IntegerScalarCubeBox α S.value)
local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "degree" => layerSamplerDegree I n
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "source" => allocatedCoefficientSource B U basis hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U basis hR hσ S
variable (H₀ step₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH₀ : ∀ t, 0 < H₀ t)
variable (hsubset₀ : ∀ t, integerProgressionSupport (c₀ t) (step₀ t : ℤ) (H₀ t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (modulus : ℕ) (r₀ : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod modulus)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H₀ hH₀).mass
  (Finset.univ.filter (fun y => principalResidueLabel modulus y = r₀)))
local notation "wholeLaw" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H₀ step₀ c₀ (allocatedPrincipalSides_pos B U basis S) hH₀ hsubset₀ modulus r₀ hcell
local notation "wholeRoot" y => allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y
local notation "wholeDirs" y => allocatedPhysicalCubeDirections B U basis S x y
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
local notation "ξ" => Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))
local notation "density" => allocatedCoefficientDensity B U basis hb o hR hσ S
local notation "cover" => quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d

omit [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
  [DecidableEq G] [∀ index, DecidableEq (B index)] [∀ index, DecidableEq (O index)]
  [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)] in
private theorem allocatedPhysicalCubeJet_measurable
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S)) :
    Measurable (euclideanCoefficientJetMap U (wholeRoot y) (wholeDirs y) rows) :=
  (euclideanCoefficientJetMap_continuous U (wholeRoot y) (wholeDirs y) rows).measurable

omit [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
  [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ] [∀ j, (ν j).IsAddLeftInvariant]
  [∀ j, IsProbabilityMeasure (ν j)] [DecidableEq G]
  [∀ index, DecidableEq (O index)] in
theorem allocatedProgressionCoveredExpectation_density
    (hdeck : CoefficientDeckDensityLaw U bW basis hb o μ source density d)
    (g : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U basis S) →
      EuclideanJetLayers U O → ℝ)
    (hgm : ∀ y, Measurable (g y)) (hg0 : ∀ y z, 0 ≤ g y z)
    (hgi : ∀ y, Integrable (g y) ξ)
    (hglaw : ∀ y, (realDensityMeasure μ (fun z => density (cover z))).map
      (euclideanCoefficientJetMap U (wholeRoot y) (wholeDirs y) rows) = realDensityMeasure ξ (g y))
    (φ : EuclideanJetLayers U O → ℂ) (hφ : Measurable φ) (hbφ : ∀ z, ‖φ z‖ ≤ 1) :
    allocatedProgressionCoveredExpectation B U basis hR hσ S rows x Q hb o bW d
      (fun p => φ p.2) H₀ step₀ c₀ hH₀ hsubset₀ modulus r₀ hcell =
      ∫ z, ((wholeLaw).mean (fun y => g y z) : ℂ) * φ z ∂ξ := by
  let : IsProbabilityMeasure source := allocatedCoefficientSource_probability B U basis hR hσ S
  rw [allocatedProgressionCoveredExpectation]
  have ht := CoefficientDeckDensityLaw.mean_mapped_test_integral U bW basis hb o μ source density d hdeck ξ wholeLaw
    (fun y => euclideanCoefficientJetMap U (wholeRoot y) (wholeDirs y) rows)
    (allocatedPhysicalCubeJet_measurable B U basis S rows x)
    g hgm hg0 hgi hglaw φ hφ hbφ
  refine Eq.trans ?_ ht
  dsimp only
  congr! (transparency := .reducible) 5

end Erdos3.VectorPolynomial

end

end OAI
