import OAI.Combinatorics.Progressions.Sampling.AllocatedOriginalForecastSpatialIntegral
import OAI.Combinatorics.Progressions.Sampling.ForecastActualPhysicalSourceContinuous
import OAI.Combinatorics.Progressions.Sampling.ForecastOriginalDensityRegularity

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Active" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)
local notation "Principal" => PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S)
local notation "law" => principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout short)
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

local notation "region" => mixedCoveredJetRegion (O := single) (E := Eout) U o basis N
  (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
local notation "chartSource" => forecastDensityPhysicalChartSource B U basis S density selected sample x
  active Y N volume base physicalN τ

 theorem forecastDensityPhysicalChartSource_mem_quarter
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (hexhaustive : ∀ a, short a → ∃ i,
      (⟨(selected i).1, Sum.inr (selected i).2⟩ : LayerSamplerAxis I n) = a)
    (hactive : ∀ y, density y ≠ 0 → ∀ a, |y.2 a| ≤ 3)
    (r : ℝ≥0) (hr : 0 < r) (hr3 : (3 : ℝ) ≤ r)
    (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ r)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤
      C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (u : X → ℤ) (z : MixedCoveredJetSource I single Eout n N)
    (hz : chartSource u z ≠ 0) : z ∈ region := by
  have hc := forecastDensityPhysicalDeckSource_cutoff B U basis S density selected sample x
    active Y N volume base physicalN τ hR hσ hs hσ1 hexhaustive hactive r hr hr3 hradius
    u (fun j => mixedArrayRegroup _ _ _ (z.1 j) ())
    (fun j i => ((z.2 j () i).val : ℤ)) hz
  have hn : allocatedBufferedAmbientCutoff (R := R) U basis o r hr
      (mixedJetAmbientPoint U basis o z.1) ≠ 0 := by
    unfold allocatedBufferedAmbientCutoff
    rw [allocatedFullAmbientSiteCoordinates_point, hc]
    exact one_ne_zero
  have hsmall := allocatedBufferedAmbientCutoff_support U basis o r hr hR C hC hchart hbudget
    (mixedJetAmbientPoint U basis o z.1) hn
  intro j hj t ht
  cases t
  refine ⟨?_, Set.mem_univ _⟩
  intro i
  exact hsmall ⟨j, (), i⟩

theorem forecastDensityPhysicalChartSource_haar_integral_unrestricted
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (hexhaustive : ∀ a, short a → ∃ i,
      (⟨(selected i).1, Sum.inr (selected i).2⟩ : LayerSamplerAxis I n) = a)
    (hactive : ∀ y, density y ≠ 0 → ∀ a, |y.2 a| ≤ 3)
    (r : ℝ≥0) (hr : 0 < r) (hr3 : (3 : ℝ) ≤ r)
    (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ r)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤
      C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
      projectedIntegerLattice (euclideanSubspace (U j)))
    (bW : ∀ j, Module.Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
      (euclideanSubspace (U j)))]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hdensity : Measurable density) (u : X → ℤ)
    (test : EuclideanJetLayers U single → ℂ) (htest : Measurable test) :
    let chart := mixedCoveredJetChart (O := single) U o basis hb bW N
    (∫ y, restrictedComplexChartDensity chart region 1 (chartSource u) y * test y
      ∂Measure.pi (fun j => Measure.pi (fun _ : Unit => ν j))) =
      (coveredJetArrayScale (O := single) U : ℂ) *
        ∫ z, chartSource u z * test (chart z)
          ∂mixedCoveredJetRawReference (I := I) (O := single) (E := Eout) (n := n) N := by
  intro chart
  rw [forecastDensityPhysicalChartSource_weighted_haar_integral B U basis S density selected
    sample x active Y N volume base physicalN τ o hb bW ν hdensity u test htest]
  congr 1
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  have he : chartSource u z = 0 := by
    by_contra hn
    exact hz (forecastDensityPhysicalChartSource_mem_quarter B U basis S density selected sample x
      active Y N volume base physicalN τ o hR hσ hs hσ1 hexhaustive hactive r hr hr3 hradius
      C hC hchart hbudget u z hn)
  rw [he, zero_mul]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Active" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)
local notation "Principal" => PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S)
local notation "law" => principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout short)
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

local notation "region" => mixedCoveredJetRegion (O := single) (E := Eout) U o basis N
  (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
local notation "chartSource" => forecastDensityPhysicalChartSource B U basis S density selected sample x
  active Y N volume base physicalN τ

include o in
theorem forecastDensityPhysicalChartSource_integrable
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (hexhaustive : ∀ a, short a → ∃ i,
      (⟨(selected i).1, Sum.inr (selected i).2⟩ : LayerSamplerAxis I n) = a)
    (hactive : ∀ y, density y ≠ 0 → ∀ a, |y.2 a| ≤ 3)
    (r : ℝ≥0) (hr : 0 < r) (hr3 : (3 : ℝ) ≤ r)
    (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ r)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤
      C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (hdensity : Continuous density) (u : X → ℤ) :
    Integrable (chartSource u)
      (mixedCoveredJetRawReference (I := I) (O := single) (E := Eout) (n := n) N) := by
  apply mixedCoveredJetRawReference_integrable_of_continuous_of_support U o basis N
    (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
    (fun j _ => standardLatticeClosedQuarterBox_isCompact (J j))
    (chartSource u)
    (forecastDensityPhysicalChartSource_continuous B U basis S density selected sample x
      active Y N volume base physicalN τ hdensity u)
  intro z hz
  exact forecastDensityPhysicalChartSource_mem_quarter B U basis S density selected sample x
    active Y N volume base physicalN τ o hR hσ hs hσ1 hexhaustive hactive r hr hr3 hradius
    C hC hchart hbudget u z hz

theorem forecastDensityPhysicalChartSource_mul_test_integrable
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (hexhaustive : ∀ a, short a → ∃ i,
      (⟨(selected i).1, Sum.inr (selected i).2⟩ : LayerSamplerAxis I n) = a)
    (hactive : ∀ y, density y ≠ 0 → ∀ a, |y.2 a| ≤ 3)
    (r : ℝ≥0) (hr : 0 < r) (hr3 : (3 : ℝ) ≤ r)
    (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ r)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤
      C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
      projectedIntegerLattice (euclideanSubspace (U j)))
    (bW : ∀ j, Module.Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (hdensity : Continuous density) (u : X → ℤ)
    (test : EuclideanJetLayers U single → ℂ) (htest : Measurable test)
    {testCap : ℝ} (hbound : ∀ y, ‖test y‖ ≤ testCap) :
    Integrable (fun z => chartSource u z * test (mixedCoveredJetChart U o basis hb bW N z))
      (mixedCoveredJetRawReference (I := I) (O := single) (E := Eout) (n := n) N) := by
  have hsource := forecastDensityPhysicalChartSource_integrable B U basis S density selected sample x
    active Y N volume base physicalN τ o hR hσ hs hσ1 hexhaustive hactive r hr hr3 hradius
    C hC hchart hbudget hdensity u
  have hm : Measurable (mixedCoveredJetChart (O := single) U o basis hb bW N) :=
    (coveredJetChart_continuous (O := single) U basis hb bW N).measurable.comp
      (mixedCoveredJetCoordinates_measurable (O := single) (B := Eout) (n := n) U o N)
  exact hsource.mul_bdd (htest.comp hm).aestronglyMeasurable
    (ae_of_all _ (fun z => hbound _))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Active" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)
local notation "Principal" => PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S)
local notation "law" => principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
local notation "selected" => allocatedShortIntegerSelection U basis S.value
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout short)
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

local notation "region" => mixedCoveredJetRegion (O := single) (E := Eout) U o basis N
  (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
local notation "chartSource" => forecastDensityPhysicalChartSource B U basis S density selected sample x
  active Y N volume base physicalN τ

variable {periodCap coverCap : ℝ} {Lip : ℝ≥0}

theorem forecastNativeHaarMean_eq_rawSum
    (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (hactive : ∀ y, density y ≠ 0 → ∀ a, |y.2 a| ≤ 3)
    (r : ℝ≥0) (hr : 0 < r) (hr3 : (3 : ℝ) ≤ r)
    (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ r)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤
      C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
      projectedIntegerLattice (euclideanSubspace (U j)))
    (bW : ∀ j, Module.Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
      (euclideanSubspace (U j)))]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hdensity : Continuous density) (κ : ℂ) :
    let chart := mixedCoveredJetChart (O := single) U o basis hb bW N
    κ * (𝔼 u ∈ integerBox physicalN,
      ∫ y, restrictedComplexChartDensity chart region 1 (chartSource u) y *
        nativeSingleSiteCoverObservable U W physicalN u N y
        ∂Measure.pi (fun j => Measure.pi (fun _ : Unit => ν j))) =
      (κ * (coveredJetArrayScale (O := single) U : ℂ) /
        ((integerBox physicalN).card : ℂ)) *
      ∑ u ∈ integerBox physicalN,
        ∫ z, chartSource u z * nativeSingleSiteCoverObservable U W physicalN u N (chart z)
          ∂mixedCoveredJetRawReference (I := I) (O := single) (E := Eout) (n := n) N := by
  intro chart
  have hexhaustive : ∀ a, short a → ∃ i,
      (⟨(selected i).1, Sum.inr (selected i).2⟩ : LayerSamplerAxis I n) = a := by
    intro a ha
    obtain ⟨i, hi⟩ := (allocatedShortIntegerAxisEquiv (I := I) U basis S.value).surjective ⟨a, ha⟩
    exact ⟨i, congrArg Subtype.val hi⟩
  have hpoint (u : X → ℤ) :=
    forecastDensityPhysicalChartSource_haar_integral_unrestricted B U basis S density selected
      sample x active Y N volume base physicalN τ o hR hσ hs hσ1 hexhaustive hactive
      r hr hr3 hradius C hC hchart hbudget hb bW ν hdensity.measurable u
      (nativeSingleSiteCoverObservable U W physicalN u N)
      (nativeSingleSiteCoverObservable_continuous U W physicalN u N).measurable
  rw [Finset.expect_eq_sum_div_card]
  calc
    _ = κ * ((∑ u ∈ integerBox physicalN,
        (coveredJetArrayScale (O := single) U : ℂ) *
        ∫ z, chartSource u z * nativeSingleSiteCoverObservable U W physicalN u N (chart z)
          ∂mixedCoveredJetRawReference (I := I) (O := single) (E := Eout) (n := n) N) /
        ((integerBox physicalN).card : ℂ)) := by
      congr 2
      apply Finset.sum_congr rfl
      intro u hu
      exact hpoint u
    _ = _ := by rw [← Finset.mul_sum]; ring

theorem forecastNativeRawMean_normalization
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
      (euclideanSubspace (U j)))]
    (hR : ∀ j, 0 < R j) (hN : ∀ x, 0 < physicalN x)
    (hV : 0 < volume) (hτ : 0 < τ) (rawSum jointMean : ℂ)
    (hraw : rawSum = ((∏ a : Σ j, I j, R a.1 : ℝ) : ℂ) *
      ((volume : ℂ) *
        ((∏ j, forecastJointGridScale U basis R S.value physicalN τ j : ℝ) : ℂ) *
        jointMean)) :
    ((forecastGeometricJacobian (X := X) (I := I) U basis R S.value volume τ : ℂ) *
      (coveredJetArrayScale (O := single) U : ℂ) /
      ((integerBox physicalN).card : ℂ)) * rawSum = jointMean := by
  rw [hraw]
  have hn := forecastJointScale_complex_normalization (I := I) U basis hR S.value
    physicalN hN hV hτ
  calc
    _ = ((forecastGeometricJacobian (X := X) (I := I) U basis R S.value volume τ : ℂ) *
      (coveredJetArrayScale (O := single) U : ℂ) *
      ((∏ a : Σ j, I j, R a.1 : ℝ) : ℂ) * (volume : ℂ) *
      ((∏ j, forecastJointGridScale U basis R S.value physicalN τ j : ℝ) : ℂ) /
      ((integerBox physicalN).card : ℂ)) * jointMean := by ring
    _ = jointMean := by rw [Complex.ofReal_prod, Complex.ofReal_prod, hn, one_mul]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Active" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)
local notation "Principal" => PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S)
local notation "law" => principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
variable {A : Type*} (selected : A → Σ j : Fin m, Fin (n j))
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout short)
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

local notation "region" => mixedCoveredJetRegion (O := single) (E := Eout) U o basis N
  (fun j (_ : Unit) => standardLatticeClosedQuarterBox (J j))
local notation "chartSource" => forecastDensityPhysicalChartSource B U basis S density selected sample x
  active Y N volume base physicalN τ

include o in
theorem forecastDensityPhysicalChartSource_haar_normalized_split_integral
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hσ1 : ∀ a, σ (selected a).1 ≤ 1)
    (hexhaustive : ∀ a, short a → ∃ i,
      (⟨(selected i).1, Sum.inr (selected i).2⟩ : LayerSamplerAxis I n) = a)
    (hactive : ∀ y, density y ≠ 0 → ∀ a, |y.2 a| ≤ 3)
    (r : ℝ≥0) (hr : 0 < r) (hr3 : (3 : ℝ) ≤ r)
    (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ r)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤
      C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
      projectedIntegerLattice (euclideanSubspace (U j)))
    (bW : ∀ j, Module.Basis (Eout j) ℤ
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j))
      (euclideanSubspace (U j)))]
    (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
    [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
    (hdensity : Continuous density) (u : X → ℤ)
    (test : EuclideanJetLayers U single → ℂ) (htest : Measurable test)
    {testCap : ℝ} (hbound : ∀ y, ‖test y‖ ≤ testCap) :
    let chart := mixedCoveredJetChart (O := single) U o basis hb bW N
    (∫ y, restrictedComplexChartDensity chart region 1 (chartSource u) y * test y
      ∂Measure.pi (fun j => Measure.pi (fun _ : Unit => ν j))) =
      (coveredJetArrayScale (O := single) U : ℂ) *
        ((∏ a : Σ j, I j, R a.1 : ℝ) : ℂ) *
        ∫ v : (Σ j, I j) → ℝ,
          ∫ k : (AllocatedShortIntegerAxis U basis S.value → ℤ) ×
              (AllocatedActiveIntegerAxis U basis S.value → ℤ),
            ∫ deck : ForecastSingleDeckResidues Eout N,
              let z := forecastSingleMixedRawPoint I Eout n N
                (fun a => R a.1 * v a) (forecastIntegerAxisMerge U basis S.value k.1 k.2) deck
              chartSource u z * test (chart z)
              ∂mixedCoveredJetDeckReference single Eout N ∂Measure.count.prod Measure.count := by
  intro chart
  have hi := forecastDensityPhysicalChartSource_mul_test_integrable B U basis S density selected
    sample x active Y N volume base physicalN τ o hR hσ hs hσ1 hexhaustive hactive r hr hr3
    hradius C hC hchart hbudget hb bW hdensity u test htest hbound
  rw [forecastDensityPhysicalChartSource_haar_integral_unrestricted B U basis S density selected
    sample x active Y N volume base physicalN τ o hR hσ hs hσ1 hexhaustive hactive r hr hr3
    hradius C hC hchart hbudget hb bW ν hdensity.measurable u test htest]
  rw [forecastSingleMixedRaw_normalized_split_integral I Eout N U basis S.value R hR _ hi,
    mul_assoc]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "Spatial" => (Σ _ : X, Unit ⊕ Empty)
local notation "Active" => (Σ _a : {a : LayerSamplerAxis I n // ¬short a}, Unit)
local notation "Principal" => PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S)
local notation "law" => principalTupleWeights (α := Empty) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)
local notation "single" => (fun _ : Fin m => Unit)

variable (density : (((Σ _ : X, Unit ⊕ Empty) → ℝ) ×
  ((Σ _a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a}, Unit) → ℝ)) → ℝ)
local notation "selected" => allocatedShortIntegerSelection U basis S.value
variable (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
variable (x : G → IntegerScalarCubeBox Empty S.value)
variable {Ω : Type*} [Fintype Ω] {Eout : Fin m → Type*} [∀ j, Fintype (Eout j)]
local notation "Out" => Sigma (AllocatedCongruenceRankOutput X Eout short)
variable (active : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → FiniteProbabilityWeights Ω)
variable (Y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty
  (allocatedPrincipalSides B U basis S) → Ω →
  Sigma (AllocatedCongruenceRankOutput X Eout (allocatedShortAxis (I := I) U basis S.value)) → ℤ)
variable (N : ℕ) [NeZero N] (volume : ℝ)
variable (base : X → ℤ) (physicalN : X → ℕ) (τ : ℝ)

variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

local notation "chartSource" => forecastDensityPhysicalChartSource B U basis S density selected sample x
  active Y N volume base physicalN τ

variable (hb : ∀ j, Submodule.span ℤ (Set.range (basis j)) =
  projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Module.Basis (Eout j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable {pw cw : ℝ} {Lw : ℝ≥0}
variable (Wtest : NormalizedPolynomialTwist X (Σ j, J j) pw cw Lw)
local notation "raw" => mixedCoveredJetRawReference (I := I) (O := single) (E := Eout) (n := n) N
local notation "RawSource" => MixedCoveredJetSource I single Eout n N

noncomputable def forecastNativeRawSpatialFamily (u : X → ℤ) (z : RawSource) : ℂ :=
  chartSource u z * nativeSingleSiteCoverObservable U Wtest physicalN u N
    (mixedCoveredJetChart U o basis hb bW N z)

private theorem allShortSelection_exhaustive (T : ℕ) :
    ∀ a : LayerSamplerAxis I n, allocatedShortAxis U basis T a →
      ∃ i : AllocatedShortIntegerAxis U basis T,
      (⟨i.val.1, Sum.inr i.val.2⟩ : LayerSamplerAxis I n) = a := by
  let _ : ∀ j, Fintype (I j) := inferInstance
  rintro ⟨j, i | i⟩ ha
  · exact False.elim ha
  · exact ⟨⟨⟨j, i⟩, ha⟩, rfl⟩

theorem forecastNativeRawSpatialFamily_integrable
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hσ1 : ∀ a : AllocatedShortIntegerAxis U basis S.value, σ a.val.1 ≤ 1)
    (hactive : ∀ y, density y ≠ 0 → ∀ a, |y.2 a| ≤ 3)
    (r : ℝ≥0) (hr : 0 < r) (hr3 : (3 : ℝ) ≤ r)
    (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ r)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤
      C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    (hdensity : Continuous density) (u : X → ℤ) :
    Integrable (forecastNativeRawSpatialFamily B U basis S density sample x active Y N volume
      base physicalN τ o hb bW Wtest u) raw := by
  exact forecastDensityPhysicalChartSource_mul_test_integrable B U basis S density selected
    sample x active Y N volume base physicalN τ o hR hσ hs hσ1
    (allShortSelection_exhaustive (I := I) U basis S.value) hactive r hr hr3 hradius
    C hC hchart hbudget hb bW hdensity u
    (nativeSingleSiteCoverObservable U Wtest physicalN u N)
    (nativeSingleSiteCoverObservable_continuous U Wtest physicalN u N).measurable
    (norm_nativeSingleSiteCoverObservable_le U Wtest physicalN u N)

section OriginalDensity

variable [DecidableEq X] [∀ a, DecidableEq (B a)]
variable {Zsp : Type*} [Fintype Zsp] [DecidableEq Zsp]
variable (s : Empty ↪ Zsp) (root : Zsp → ℤ) (D : Matrix Empty Zsp ℤ)
  (hp : (selectedSpatialPivot root D s).det ≠ 0)
  {Wgeo Lgeo : ℝ} (hW : 0 ≤ Wgeo) (hL : 0 < Lgeo)
variable (hB : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    4 ≤ Fintype.card (B a.val))
  (lower width : ∀ a : {a : LayerSamplerAxis I n // ¬allocatedShortAxis (I := I) U basis S.value a},
    B a.val × Fin (layerSamplerDegree I n a.val) → ℝ)
local notation "original" => allocatedOriginalSampleForecastDensity (X := X)
  B U basis S s root D hp hW hL hB lower width sample

theorem forecastNativeRawSpatialFamily_original_zero_outside
    (hroot : (∑ j, |(root j : ℝ)|) ≤ Wgeo)
    (hN : ∀ i, 0 < physicalN i) (hτ : 0 < τ)
    (hmargin : ∀ i, 2 * spatialTrimMargin τ physicalN i ≤ physicalN i)
    (hbase : base ∈ trimmedIntegerBox physicalN (spatialTrimMargin τ physicalN))
    (u : X → ℤ) (hu : u ∉ integerBox physicalN) (z : RawSource) :
    forecastNativeRawSpatialFamily B U basis S original sample x active Y N volume
      base physicalN τ o hb bW Wtest u z = 0 := by
  unfold forecastNativeRawSpatialFamily forecastDensityPhysicalChartSource
    forecastDensityPhysicalDeckSource
  rw [allocatedOriginalSampleForecastDensity_zero_outside_integerBox B U basis S
    s root D hp hW hL hB lower width hroot sample physicalN hN hτ hmargin base hbase u _ hu,
    Complex.ofReal_zero, zero_mul, zero_mul]

theorem forecastNativeRawSpatialFamily_original_integrable
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hσ1 : ∀ a : AllocatedShortIntegerAxis U basis S.value, σ a.val.1 ≤ 1)
    (r : ℝ≥0) (hr : 0 < r) (hr3 : (3 : ℝ) ≤ r)
    (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ r)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤
      C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    {δ : ℝ} (hδ : 0 < δ)
    (hw : ∀ a p, δ ≤ width a p) (hl : ∀ a p, 0 ≤ lower a p)
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    (hroot : ∀ j, |(root j : ℝ)| ≤ 1 + Wgeo) (u : X → ℤ) :
    Integrable (forecastNativeRawSpatialFamily B U basis S original sample x active Y N volume
      base physicalN τ o hb bW Wtest u) raw := by
  let _ : DecidableEq X := inferInstance
  apply forecastNativeRawSpatialFamily_integrable B U basis S original sample x active Y N volume
    base physicalN τ o hb bW Wtest hR hσ hs hσ1
    (allocatedOriginalSampleForecastDensity_active_bound_three_of_supported
      B U basis hR hσ S s root D hp hW hL hB lower width hδ hw hl sample hs hwidth)
    r hr hr3 hradius C hC hchart hbudget
  exact allocatedOriginalSampleForecastDensity_continuous_of_supported
    B U basis hR hσ S s root D hp hW hL hB lower width hδ hw hl sample hs hroot

theorem forecastNativeRawSpatialFamily_original_normalized_integral
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
    (hs : ∀ j, mixedArraySupported (allocatedLayerCenters B U basis S j)
      (allocatedLayerWidths B U basis S j)
      (allocatedLayerIntegerPMFs B U basis hR hσ S j) (sample j))
    (hσ1 : ∀ a : AllocatedShortIntegerAxis U basis S.value, σ a.val.1 ≤ 1)
    (r : ℝ≥0) (hr : 0 < r) (hr3 : (3 : ℝ) ≤ r)
    (hradius : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ r)
    (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm v‖ ≤
      C j * ‖v‖)
    (hbudget : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)) ≤ 1 / 4)
    {δ : ℝ} (hδ : 0 < δ)
    (hw : ∀ a p, δ ≤ width a p) (hl : ∀ a p, 0 ≤ lower a p)
    (hwidth : ∀ a p, |lower a p| + |width a p| ≤ 1)
    (hroot : (∑ j, |(root j : ℝ)|) ≤ Wgeo)
    (hN : ∀ i, 0 < physicalN i) (hτ : 0 < τ)
    (hmargin : ∀ i, 2 * spatialTrimMargin τ physicalN i ≤ physicalN i)
    (hbase : base ∈ trimmedIntegerBox physicalN (spatialTrimMargin τ physicalN)) :
    let F := forecastNativeRawSpatialFamily B U basis S original sample x active Y N volume
      base physicalN τ o hb bW Wtest
    (∑ u ∈ integerBox physicalN, ∫ z, F u z ∂raw) =
      ((∏ a : Σ j, I j, R a.1 : ℝ) : ℂ) *
      ∫ deck : ForecastSingleDeckResidues Eout N,
        ∫ v : (Σ j, I j) → ℝ,
          ∑' ks : AllocatedShortIntegerAxis U basis S.value → ℤ,
          ∑' k : (X ⊕ AllocatedActiveIntegerAxis U basis S.value) → ℤ,
            F (fun i => k (Sum.inl i))
              (forecastSingleMixedRawPoint I Eout n N (fun a => R a.1 * v a)
                (forecastIntegerAxisMerge U basis S.value ks (fun a => k (Sum.inr a))) deck)
          ∂MeasureTheory.volume ∂mixedCoveredJetDeckReference single Eout N := by
  dsimp only
  apply forecastRawSpatialBox_normalized_integral I Eout N U basis S.value X R hR
  · intro u _
    apply forecastNativeRawSpatialFamily_original_integrable B U basis S sample x active Y N volume
      base physicalN τ o hb bW Wtest s root D hp hW hL hB lower width hR hσ hs hσ1
      r hr hr3 hradius C hC hchart hbudget hδ hw hl hwidth
    intro j
    have hj : |(root j : ℝ)| ≤ ∑ j, |(root j : ℝ)| :=
      Finset.single_le_sum (fun i _ => abs_nonneg (root i : ℝ)) (Finset.mem_univ j)
    linarith
  · intro u hu z
    exact forecastNativeRawSpatialFamily_original_zero_outside B U basis S sample x active Y N volume
      base physicalN τ o hb bW Wtest s root D hp hW hL hB lower width hroot hN hτ hmargin
      hbase u hu z

end OriginalDensity

end Erdos3.VectorPolynomial

end

end OAI
