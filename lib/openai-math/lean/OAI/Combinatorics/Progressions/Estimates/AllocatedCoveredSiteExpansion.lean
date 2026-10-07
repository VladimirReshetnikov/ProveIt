import Mathlib.MeasureTheory.Integral.Bochner.Set
import OAI.Combinatorics.Progressions.Geometry.RestrictedComplexChartSupport
import OAI.Combinatorics.Progressions.Probability.AllocatedLongIntegralMass

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical

variable {m : ℕ} {I O J E : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
variable (hΩm : ∀ j t, MeasurableSet (Ω j t))
variable (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d Ω

include hΩ in
omit [∀ j, Fintype (O j)] in
theorem mixedCoveredJet_restrictedDensity_eq (f : MixedCoveredJetSource I O E n d → ℝ) :
    restrictedChartDensity chart region 1 f =
      restrictedChartDensity (coveredJetChart U b hb bW d) (coveredJetSourceRegion U b d Ω) 1
        (fun z => f ((mixedCoveredJetEquiv U o d).symm z)) := by
  symm
  apply restrictedChartDensity_eq_of_values chart region
    (mixedCoveredJetChart_injOn U o b hb bW d Ω hΩ)
  · intro z hz
    rw [mixedCoveredJetChart, restrictedChartDensity_apply _ _ _ _
      (coveredJetChart_injOn U b hb bW d Ω hΩ) hz, one_mul]
    exact congrArg f ((mixedCoveredJetEquiv U o d).symm_apply_apply z)
  · intro y hy
    apply restrictedChartDensity_zero
    rwa [← mixedCoveredJetChart_image U o b hb bW d Ω]

include hΩm hΩ in
theorem mixedCoveredJet_restrictedDensity_measurable
    (f : MixedCoveredJetSource I O E n d → ℝ) (hf : Measurable f) :
    Measurable (restrictedChartDensity chart region 1 f) := by
  rw [mixedCoveredJet_restrictedDensity_eq U o b hb bW d Ω hΩ]
  exact restrictedChartDensity_measurable _ (coveredJetChart_embedding U b hb bW d Ω hΩm hΩ)
    1 _ (hf.comp (mixedCoveredJetEquiv U o d).symm.measurable)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical

variable {m : ℕ} {I O J E : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
variable (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d Ω

include hΩ

omit [∀ j, Fintype (O j)] in
theorem mixedCoveredJet_restrictedComplexDensity_eq (f : MixedCoveredJetSource I O E n d → ℂ) :
    restrictedComplexChartDensity chart region 1 f =
      restrictedComplexChartDensity (coveredJetChart U b hb bW d) (coveredJetSourceRegion U b d Ω) 1
        (fun z => f ((mixedCoveredJetEquiv U o d).symm z)) := by
  funext y
  by_cases hy : y ∈ chart '' region
  · obtain ⟨z, hz, rfl⟩ := hy
    rw [restrictedComplexChartDensity_apply _ _ _ _
      (mixedCoveredJetChart_injOn U o b hb bW d Ω hΩ) hz]
    change _ = restrictedComplexChartDensity (coveredJetChart U b hb bW d)
      (coveredJetSourceRegion U b d Ω) 1 _
      (coveredJetChart U b hb bW d (mixedCoveredJetCoordinates U o d z))
    rw [restrictedComplexChartDensity_apply _ _ _ _
      (coveredJetChart_injOn U b hb bW d Ω hΩ) hz]
    exact congrArg (fun w => (1 : ℂ) * f w) ((mixedCoveredJetEquiv U o d).symm_apply_apply z).symm
  · rw [restrictedComplexChartDensity_zero _ _ _ _ hy]
    symm
    apply restrictedComplexChartDensity_zero
    rwa [← mixedCoveredJetChart_image U o b hb bW d Ω]

theorem mixedCoveredJet_restrictedComplexDensity_measurable
    (hΩm : ∀ j t, MeasurableSet (Ω j t))
    (f : MixedCoveredJetSource I O E n d → ℂ) (hf : Measurable f) :
    Measurable (restrictedComplexChartDensity chart region 1 f) := by
  rw [mixedCoveredJet_restrictedComplexDensity_eq U o b hb bW d Ω hΩ]
  exact restrictedComplexChartDensity_measurable _ _
    (coveredJetChart_embedding U b hb bW d Ω hΩm hΩ) 1 _
    (hf.comp (mixedCoveredJetEquiv U o d).symm.measurable)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical

variable {m : ℕ} {I O J E : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
variable (hΩm : ∀ j t, MeasurableSet (Ω j t))
variable (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d Ω
local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))
local notation "raw" => mixedCoveredJetRawReference (I := I) (O := O) (E := E) (n := n) d

include hΩm hΩ in
theorem mixedCoveredJet_normalized_complex_integral
    (f : MixedCoveredJetSource I O E n d → ℝ) (hfm : Measurable f)
    (hf0 : ∀ z, 0 ≤ f z) (hfs : ∀ z ∉ region, f z = 0)
    (φ : EuclideanJetLayers U O → ℂ) (hφ : Measurable φ) :
    (∫ z, (f z : ℂ) * φ (chart z) ∂raw) =
      ∫ y, (restrictedChartDensity chart region 1
        (fun z => f z / coveredJetArrayScale (O := O) U) y : ℂ) * φ y ∂haar := by
  let ρ := restrictedChartDensity chart region 1
    (fun z => f z / coveredJetArrayScale (O := O) U)
  have hρm : Measurable ρ :=
    mixedCoveredJet_restrictedDensity_measurable U o b hb bW d Ω hΩm hΩ _ (hfm.div_const _)
  have hρ0 : ∀ y, 0 ≤ ρ y := by
    intro y
    by_cases hy : y ∈ chart '' region
    · obtain ⟨z, hz, rfl⟩ := hy
      dsimp only [ρ]
      rw [restrictedChartDensity_apply _ _ _ _
        (mixedCoveredJetChart_injOn U o b hb bW d Ω hΩ) hz, one_mul]
      exact div_nonneg (hf0 z) (coveredJetArrayScale_pos U).le
    · exact (restrictedChartDensity_zero chart region 1 _ hy).ge
  have hi : Set.indicator region f = f := by
    funext z
    by_cases hz : z ∈ region
    · exact Set.indicator_of_mem hz f
    · rw [Set.indicator_of_notMem hz, hfs z hz]
  have hlaw := mixedCoveredJet_normalized_density_law U o b hb bW d ν Ω hΩm hΩ f
  rw [hi] at hlaw
  have hchart : Measurable chart :=
    (coveredJetChart_continuous (O := O) U b hb bW d).measurable.comp
      (mixedCoveredJetCoordinates_measurable (O := O) (B := E) (n := n) U o d)
  rw [← realDensityMeasure_integral_complex raw f hfm hf0,
    ← integral_map hchart.aemeasurable hφ.aestronglyMeasurable, hlaw]
  exact realDensityMeasure_integral_complex haar ρ hρm hρ0 φ

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open MeasureTheory _root_.Set _root_.OAI.Set
open scoped Classical

theorem restrictedComplexChartDensity_weighted_integral_of_map
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (q : X → Y) (hq : Measurable q) (S : Set X) (hS : MeasurableSet S)
    (hinj : Set.InjOn q S) (himage : MeasurableSet (q '' S))
    (μ : Measure X) (ν : Measure Y)
    (hmap : Measure.map q (μ.restrict S) = ν.restrict (q '' S))
    (f : X → ℂ) (test : Y → ℂ)
    (hm : Measurable (fun y => restrictedComplexChartDensity q S 1 f y * test y)) :
    (∫ y, restrictedComplexChartDensity q S 1 f y * test y ∂ν) =
      ∫ x in S, f x * test (q x) ∂μ := by
  let F := fun y => restrictedComplexChartDensity q S 1 f y * test y
  have hind : (q '' S).indicator F = F := by
    funext y
    by_cases hy : y ∈ q '' S
    · exact indicator_of_mem hy F
    · simp only [indicator_of_notMem hy, F,
        restrictedComplexChartDensity_zero q S 1 f hy, zero_mul]
  calc
    _ = ∫ y in q '' S, F y ∂ν := by rw [← integral_indicator himage, hind]
    _ = ∫ x in S, F (q x) ∂μ := by
      rw [← hmap, integral_map_of_stronglyMeasurable hq hm.stronglyMeasurable]
    _ = _ := by
      apply setIntegral_congr_fun hS
      intro x hx
      simp only [F, restrictedComplexChartDensity_apply q S 1 f hinj hx,
        Complex.ofReal_one, one_mul]

namespace VectorPolynomial

open Module Submodule

variable {m : ℕ} {I O J E : Fin m → Type*}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (O j)] [∀ j, Fintype (J j)] [∀ j, Fintype (E j)]
variable {n : Fin m → ℕ} (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
variable (hΩm : ∀ j t, MeasurableSet (Ω j t))
variable (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := E) U o b d Ω
local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))
local notation "raw" => mixedCoveredJetRawReference (I := I) (O := O) (E := E) (n := n) d

include hΩm hΩ

theorem mixedCoveredJet_reference_map :
    Measure.map chart ((coveredJetArrayReference U d).restrict region) =
      (haar).restrict (chart '' region) := by
  let e := mixedCoveredJetEquiv (O := O) (B := E) (n := n) U o d
  have hp := mixedCoveredJetEquiv_measurePreserving (O := O) (B := E) (n := n) U o d
  have he : Measure.map e ((coveredJetArrayReference U d).restrict region) =
      (coveredJetReference U d).restrict (coveredJetSourceRegion U b d Ω) := by
    rw [← hp.map_eq, e.restrict_map]
    rfl
  change Measure.map (coveredJetChart U b hb bW d ∘ e) _ = _
  rw [← Measure.map_map (coveredJetChart_continuous (O := O) U b hb bW d).measurable
    e.measurable, he, coveredJetChart_reference_map U b hb bW d ν Ω hΩm hΩ,
    mixedCoveredJetChart_image U o b hb bW d Ω]

theorem mixedCoveredJet_weighted_complex_integral
    (f : MixedCoveredJetSource I O E n d → ℂ) (hf : Measurable f)
    (test : EuclideanJetLayers U O → ℂ) (htest : Measurable test) :
    (∫ y, restrictedComplexChartDensity chart region 1 f y * test y ∂haar) =
      (coveredJetArrayScale (O := O) U : ℂ) *
        ∫ z in region, f z * test (chart z) ∂raw := by
  have hq : Measurable chart :=
    (coveredJetChart_continuous (O := O) U b hb bW d).measurable.comp
      (mixedCoveredJetCoordinates_measurable (O := O) (B := E) (n := n) U o d)
  have hS : MeasurableSet region :=
    (coveredJetSourceRegion_measurable U b d Ω hΩm).preimage
      (mixedCoveredJetCoordinates_measurable (O := O) (B := E) (n := n) U o d)
  have himage : MeasurableSet (chart '' region) := by
    rw [mixedCoveredJetChart_image U o b hb bW d Ω]
    have h := (coveredJetChart_embedding U b hb bW d Ω hΩm hΩ).measurableSet_range
    have he : Set.range (fun x : coveredJetSourceRegion U b d Ω =>
        coveredJetChart U b hb bW d x.val) =
        coveredJetChart U b hb bW d '' coveredJetSourceRegion U b d Ω := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x.val, x.property, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
    rwa [he] at h
  rw [restrictedComplexChartDensity_weighted_integral_of_map chart hq region hS
    (mixedCoveredJetChart_injOn U o b hb bW d Ω hΩ) himage
    (coveredJetArrayReference U d) haar
    (mixedCoveredJet_reference_map U o b hb bW d ν Ω hΩm hΩ) f test
    ((mixedCoveredJet_restrictedComplexDensity_measurable U o b hb bW d Ω hΩ hΩm f hf).mul htest)]
  rw [coveredJetArrayReference_eq_real_smul, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (coveredJetArrayScale_pos (O := O) U).le]
  rfl

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit O I n grid
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)

theorem allocatedGridJetDensity_measurable :
    Measurable (allocatedGridJetDensity B U b hR hσ S x u v rows) := by
  have hr (a : {a // grid a}) : Measurable (allocatedGridJetFactor B U b hR hσ S x u v rows a) := by
    rcases a with ⟨⟨j, i | i⟩, ha⟩
    · exact False.elim ha
    · change Measurable (fun z : O j → ℤ =>
        (integerMatrixImagePMF (boundedCoefficientJetMatrix root dirs (j.val + 1) (rows j))
          (allocatedLayerIntegerPMFs B U b hR hσ S j i) z).toReal)
      exact measurable_of_countable _
  exact Finset.measurable_prod _ (fun a _ => (hr a).comp (measurable_pi_apply a))

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := Q) U o b d Ω

noncomputable def allocatedCoveredProfileDensity (f : AllocatedLongJetRows B U b S O → ℝ) :
    EuclideanJetLayers U O → ℝ :=
  restrictedChartDensity chart region 1 (fun z : MixedCoveredJetSource I O Q n d =>
    allocatedCoveredFixedFactor B U b hR hσ S x u v rows Q d z.1 z.2 * f ((split z.1).2))

variable (hΩm : ∀ j t, MeasurableSet (Ω j t))
variable (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))

local notation "profile" => allocatedCoveredProfileDensity B U b hR hσ S x u v rows hb o bW d Ω

include hΩ in
omit [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in
theorem allocatedCoveredProfileDensity_sub (f g : AllocatedLongJetRows B U b S O → ℝ) :
    (fun y => profile f y - profile g y) = profile (fun z => f z - g z) := by
  unfold allocatedCoveredProfileDensity
  rw [restrictedChartDensity_sub _ _ (mixedCoveredJetChart_injOn U o b hb bW d Ω hΩ)]
  congr 1
  funext z
  exact (mul_sub _ _ _).symm

include hΩm hΩ in
omit [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in
theorem allocatedCoveredProfileDensity_measurable
    (f : AllocatedLongJetRows B U b S O → ℝ) (hf : Measurable f) : Measurable (profile f) := by
  apply mixedCoveredJet_restrictedDensity_measurable U o b hb bW d Ω hΩm hΩ
  have hs : Measurable (fun z : MixedCoveredJetSource I O Q n d => split z.1) :=
    (split).measurable.comp measurable_fst
  have hd : Measurable (coefficientDeckJetDensity root dirs rows d : (∀ j, O j → Q j → ZMod d) → ℝ) :=
    measurable_of_finite _
  change Measurable (fun z : MixedCoveredJetSource I O Q n d =>
    (allocatedGridJetDensity B U b hR hσ S x u v rows ((split z.1).1) *
      coefficientDeckJetDensity root dirs rows d z.2 / coveredJetArrayScale (O := O) U) * f ((split z.1).2))
  exact (((allocatedGridJetDensity_measurable B U b hR hσ S x u v rows).comp
    (measurable_fst.comp hs)).mul (hd.comp measurable_snd)).div_const _ |>.mul (hf.comp (measurable_snd.comp hs))

variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))
local notation "reference" => allocatedLongJetReference B U b S O

include hΩm hΩ in
theorem allocatedCoveredProfileDensity_lintegral_abs
    (f : AllocatedLongJetRows B U b S O → ℝ) (hf : Integrable f reference) :
    (∫⁻ y, ENNReal.ofReal |profile f y| ∂haar) ≤ ENNReal.ofReal (∫ z, |f z| ∂reference) := by
  let μf := allocatedFrozenJetReference B U b S O
  let μd := (PMF.uniformOfFintype (∀ j, O j → Q j → ZMod d)).toMeasure
  let μraw := (Measure.pi (fun j => mixedArrayReference (I j) (Fin (n j)) (O j))).prod μd
  let fg := allocatedGridJetDensity B U b hR hσ S x u v rows
  let fd : (∀ j, O j → Q j → ZMod d) → ℝ := coefficientDeckJetDensity root dirs rows d
  let e := MeasurableEquiv.prodCongr split (MeasurableEquiv.refl (∀ j, O j → Q j → ZMod d))
  let F := fun z : (AllocatedFrozenJetRows B U b S O × AllocatedLongJetRows B U b S O) ×
      (∀ j, O j → Q j → ZMod d) => fg z.1.1 * |f z.1.2| * fd z.2
  have hfg : Integrable fg μf ∧ (∫ z, fg z ∂μf) = 1 :=
    allocatedGridJetDensity_probability_data B U b S O hR hσ x u v rows
  have hfg0 (z) : 0 ≤ fg z := (allocatedGridJetDensity_mem_Icc B U b hR hσ S x u v rows z).1
  let : IsProbabilityMeasure (realDensityMeasure μd fd) := coefficientDeckJetDensity_probability _ _ rows d
  have hfd := boundedDensity_mass μd fd (measurable_of_finite _) (coefficientDeckJetDensity_nonneg _ _ rows d)
    (coefficientDeckJetDensity_le_card _ _ rows d)
  have hFi : Integrable F ((μf.prod reference).prod μd) := (hfg.1.mul_prod hf.abs).mul_prod hfd.1
  have hF0 (z) : 0 ≤ F z := mul_nonneg (mul_nonneg (hfg0 _) (abs_nonneg _))
    (coefficientDeckJetDensity_nonneg _ _ rows d _)
  have hFm : (∫ z, F z ∂(μf.prod reference).prod μd) = ∫ z, |f z| ∂reference := by
    dsimp only [F]
    rw [integral_prod_mul (μ := μf.prod reference) (ν := μd)
      (fun z : AllocatedFrozenJetRows B U b S O × AllocatedLongJetRows B U b S O => fg z.1 * |f z.2|) fd,
      integral_prod_mul (μ := μf) (ν := reference) fg (fun z => |f z|), hfg.2, hfd.2, one_mul, mul_one]
  have he : MeasurePreserving e μraw ((μf.prod reference).prod μd) :=
    (coefficientJetAxisSplit_measurePreserving O I n grid).prod (MeasurePreserving.id μd)
  have hident : (fun z : MixedCoveredJetSource I O Q n d =>
      |allocatedCoveredFixedFactor B U b hR hσ S x u v rows Q d z.1 z.2 * f ((split z.1).2)|) =
      (fun z => F (e z) / coveredJetArrayScale (O := O) U) := by
    funext z
    change |(fg ((split z.1).1) * fd z.2 / coveredJetArrayScale (O := O) U) * f ((split z.1).2)| =
      (fg ((split z.1).1) * |f ((split z.1).2)| * fd z.2) / coveredJetArrayScale (O := O) U
    rw [abs_mul, abs_div, abs_mul, abs_of_nonneg (hfg0 _),
      abs_of_nonneg (coefficientDeckJetDensity_nonneg _ _ rows d _), abs_of_pos (coveredJetArrayScale_pos U)]
    ring
  have ha := restrictedChartDensity_abs chart region
    (mixedCoveredJetChart_injOn U o b hb bW d Ω hΩ)
    (fun z : MixedCoveredJetSource I O Q n d =>
      allocatedCoveredFixedFactor B U b hR hσ S x u v rows Q d z.1 z.2 * f ((split z.1).2))
  calc
    _ = ∫⁻ y, ENNReal.ofReal (restrictedChartDensity chart region 1
        (fun z => F (e z) / coveredJetArrayScale (O := O) U) y) ∂haar := by
      apply lintegral_congr
      intro y
      change ENNReal.ofReal |restrictedChartDensity chart region 1 _ y| = _
      rw [congrFun ha y, hident]
    _ = ∫⁻ z in region, ENNReal.ofReal (F (e z)) ∂μraw :=
      mixedCoveredJet_normalized_lintegral U o b hb bW d ν Ω hΩm hΩ (fun z => F (e z))
    _ ≤ ∫⁻ z, ENNReal.ofReal (F (e z)) ∂μraw := lintegral_mono' Measure.restrict_le_self le_rfl
    _ = ∫⁻ z, ENNReal.ofReal (F z) ∂(μf.prod reference).prod μd :=
      he.lintegral_comp_emb e.measurableEmbedding (fun z => ENNReal.ofReal (F z))
    _ = ENNReal.ofReal (∫ z, |f z| ∂reference) := by
      rw [← ofReal_integral_eq_lintegral_ofReal hFi (Filter.Eventually.of_forall hF0), hFm]

include hΩm hΩ in
theorem allocatedCoveredProfileDensity_integrable
    (f : AllocatedLongJetRows B U b S O → ℝ) (hfm : Measurable f) (hf : Integrable f reference) :
    Integrable (profile f) haar := by
  refine ⟨(allocatedCoveredProfileDensity_measurable B U b hR hσ S x u v rows hb o bW d Ω hΩm hΩ f hfm).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  simpa only [Real.norm_eq_abs] using
    (allocatedCoveredProfileDensity_lintegral_abs B U b hR hσ S x u v rows hb o bW d Ω hΩm hΩ ν f hf).trans_lt
      ENNReal.ofReal_lt_top

include hΩm hΩ in
theorem allocatedCoveredProfileDensity_integral_abs
    (f : AllocatedLongJetRows B U b S O → ℝ) (hfm : Measurable f) (hf : Integrable f reference) :
    (∫ y, |profile f y| ∂haar) ≤ ∫ z, |f z| ∂reference := by
  have hi := allocatedCoveredProfileDensity_integrable B U b hR hσ S x u v rows hb o bW d Ω hΩm hΩ ν f hfm hf
  have h := allocatedCoveredProfileDensity_lintegral_abs B U b hR hσ S x u v rows hb o bW d Ω hΩm hΩ ν f hf
  rw [← ofReal_integral_eq_lintegral_ofReal hi.abs (Filter.Eventually.of_forall (fun y => abs_nonneg (profile f y)))] at h
  have hleft : 0 ≤ ∫ y, |profile f y| ∂haar := integral_nonneg (fun y => abs_nonneg _)
  have hright : 0 ≤ ∫ z, |f z| ∂reference := integral_nonneg (fun z => abs_nonneg _)
  simpa only [ENNReal.toReal_ofReal hleft, ENNReal.toReal_ofReal hright] using
    ENNReal.toReal_mono ENNReal.ofReal_ne_top h

include hΩm hΩ in
theorem allocatedCoveredProfileDensity_l1
    (f g : AllocatedLongJetRows B U b S O → ℝ) (hfm : Measurable f) (hgm : Measurable g)
    (hf : Integrable f reference) (hg : Integrable g reference) :
    (∫ y, |profile f y - profile g y| ∂haar) ≤ ∫ z, |f z - g z| ∂reference := by
  have h := allocatedCoveredProfileDensity_integral_abs B U b hR hσ S x u v rows hb o bW d Ω hΩm hΩ ν
    (fun z => f z - g z) (hfm.sub hgm) (hf.sub hg)
  rw [← allocatedCoveredProfileDensity_sub B U b hR hσ S x u v rows hb o bW d Ω hΩ] at h
  exact h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit O I n grid
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := Q) U o b d Ω

noncomputable def allocatedCoveredComplexProfileDensity
    (f : AllocatedLongJetRows B U b S O → ℂ) : EuclideanJetLayers U O → ℂ :=
  restrictedComplexChartDensity chart region 1 (fun z : MixedCoveredJetSource I O Q n d =>
    (allocatedCoveredFixedFactor B U b hR hσ S x u v rows Q d z.1 z.2 : ℂ) * f ((split z.1).2))

variable (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))

include hΩ in
omit [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in
theorem allocatedCoveredComplexProfileDensity_real
    (f : AllocatedLongJetRows B U b S O → ℝ) (y : EuclideanJetLayers U O) :
    allocatedCoveredComplexProfileDensity B U b hR hσ S x u v rows hb o bW d Ω (fun z => (f z : ℂ)) y =
      (allocatedCoveredProfileDensity B U b hR hσ S x u v rows hb o bW d Ω f y : ℂ) := by
  unfold allocatedCoveredComplexProfileDensity allocatedCoveredProfileDensity
  simp only [← Complex.ofReal_mul]
  exact restrictedComplexChartDensity_real chart region 1
    (mixedCoveredJetChart_injOn U o b hb bW d Ω hΩ) _ y

include hΩ in
omit [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in
theorem allocatedCoveredComplexProfileDensity_sum {T : Type*} [Fintype T]
    (a : T → ℂ) (f : T → AllocatedLongJetRows B U b S O → ℂ) (y : EuclideanJetLayers U O) :
    allocatedCoveredComplexProfileDensity B U b hR hσ S x u v rows hb o bW d Ω
      (fun z => ∑ i, a i * f i z) y =
      ∑ i, a i * allocatedCoveredComplexProfileDensity B U b hR hσ S x u v rows hb o bW d Ω (f i) y := by
  unfold allocatedCoveredComplexProfileDensity
  have hfun : (fun z : MixedCoveredJetSource I O Q n d =>
      (allocatedCoveredFixedFactor B U b hR hσ S x u v rows Q d z.1 z.2 : ℂ) *
        ∑ i, a i * f i ((split z.1).2)) =
      fun z => ∑ i, a i * ((allocatedCoveredFixedFactor B U b hR hσ S x u v rows Q d z.1 z.2 : ℂ) *
        f i ((split z.1).2)) := by
    funext z
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hfun]
  exact restrictedComplexChartDensity_sum chart region 1
    (mixedCoveredJetChart_injOn U o b hb bW d Ω hΩ) a _ y

include hΩ in
theorem allocatedCoveredComplexProfileDensity_pointwise_error
    (f g : AllocatedLongJetRows B U b S O → ℂ)
    (envelope : AllocatedLongJetRows B U b S O → ℝ) (ε : ℝ)
    (he : ∀ z, ‖f z - g z‖ ≤ ε * envelope z) (y : EuclideanJetLayers U O) :
    ‖allocatedCoveredComplexProfileDensity B U b hR hσ S x u v rows hb o bW d Ω f y -
      allocatedCoveredComplexProfileDensity B U b hR hσ S x u v rows hb o bW d Ω g y‖ ≤
      ε * allocatedCoveredProfileDensity B U b hR hσ S x u v rows hb o bW d Ω envelope y := by
  unfold allocatedCoveredComplexProfileDensity allocatedCoveredProfileDensity
  have h := restrictedComplexChartDensity_pointwise_error chart region 1
    (mixedCoveredJetChart_injOn U o b hb bW d Ω hΩ)
    (fun z : MixedCoveredJetSource I O Q n d =>
      (allocatedCoveredFixedFactor B U b hR hσ S x u v rows Q d z.1 z.2 : ℂ) * f ((split z.1).2))
    (fun z : MixedCoveredJetSource I O Q n d =>
      (allocatedCoveredFixedFactor B U b hR hσ S x u v rows Q d z.1 z.2 : ℂ) * g ((split z.1).2))
    (fun z : MixedCoveredJetSource I O Q n d =>
      allocatedCoveredFixedFactor B U b hR hσ S x u v rows Q d z.1 z.2 * envelope ((split z.1).2)) ε
    (fun z _ => ?_) y
  · simpa only [abs_one] using h
  · have hnonneg := allocatedCoveredFixedFactor_nonneg B U b hR hσ S x u v rows Q d z.1 z.2
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_of_nonneg hnonneg]
    exact (mul_le_mul_of_nonneg_left (he _) hnonneg).trans_eq (by ring)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d] (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))
variable (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := Q) U o b d Ω
local notation "profile" => allocatedCoveredProfileDensity B U b hR hσ S x u v rows hb o bW d Ω

include hΩ in
theorem allocatedCoveredProfileDensity_abs_mono
    (f g : AllocatedLongJetRows B U b S O → ℝ) (hfg : ∀ z, |f z| ≤ |g z|)
    (y : EuclideanJetLayers U O) : |profile f y| ≤ |profile g y| := by
  by_cases hy : y ∈ chart '' region
  · obtain ⟨z, hz, rfl⟩ := hy
    simp only [allocatedCoveredProfileDensity,
      restrictedChartDensity_apply _ _ _ _ (mixedCoveredJetChart_injOn U o b hb bW d Ω hΩ) hz,
      one_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hfg _) (abs_nonneg _)
  · simp only [allocatedCoveredProfileDensity, restrictedChartDensity_zero _ _ _ _ hy, abs_zero, le_refl]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit O I n grid
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (Ω : ∀ j, O j → Set (EuclideanSpace ℝ (J j)))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := Q) U o b d Ω

variable (hΩ : ∀ j t, Ω j t ⊆ standardLatticeSmallBox (J j))

local notation "profile" => allocatedCoveredProfileDensity B U b hR hσ S x u v rows hb o bW d Ω

include hΩ in
omit [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in
theorem allocatedCoveredProfileDensity_zero (y : EuclideanJetLayers U O) :
    profile (fun _ => 0) y = 0 := by
  by_cases hy : y ∈ chart '' region
  · obtain ⟨z, hz, rfl⟩ := hy
    simp only [allocatedCoveredProfileDensity,
      restrictedChartDensity_apply _ _ _ _ (mixedCoveredJetChart_injOn U o b hb bW d Ω hΩ) hz,
      mul_zero]
  · exact restrictedChartDensity_zero _ _ _ _ hy

include hΩ in
theorem allocatedCoveredProfileDensity_abs (f : AllocatedLongJetRows B U b S O → ℝ)
    (y : EuclideanJetLayers U O) :
    |profile f y| = profile (fun z => |f z|) y := by
  by_cases hy : y ∈ chart '' region
  · obtain ⟨z, hz, rfl⟩ := hy
    simp only [allocatedCoveredProfileDensity,
      restrictedChartDensity_apply _ _ _ _ (mixedCoveredJetChart_injOn U o b hb bW d Ω hΩ) hz,
      one_mul, abs_mul,
      abs_of_nonneg (allocatedCoveredFixedFactor_nonneg B U b hR hσ S x u v rows Q d z.1 z.2)]
  · simp only [allocatedCoveredProfileDensity, restrictedChartDensity_zero _ _ _ _ hy, abs_zero]

include hΩ in
theorem allocatedCoveredComplexProfileDensity_pointwise_abs_error
    (f g : AllocatedLongJetRows B U b S O → ℂ)
    (envelope : AllocatedLongJetRows B U b S O → ℝ) (ε : ℝ)
    (he : ∀ z, ‖f z - g z‖ ≤ ε * |envelope z|) (y : EuclideanJetLayers U O) :
    ‖allocatedCoveredComplexProfileDensity B U b hR hσ S x u v rows hb o bW d Ω f y -
      allocatedCoveredComplexProfileDensity B U b hR hσ S x u v rows hb o bW d Ω g y‖ ≤
      ε * |profile envelope y| := by
  have h := allocatedCoveredComplexProfileDensity_pointwise_error B U b hR hσ S x u v rows hb o bW d Ω hΩ
    f g (fun z => |envelope z|) ε he y
  rw [← allocatedCoveredProfileDensity_abs B U b hR hσ S x u v rows hb o bW d Ω hΩ envelope y] at h
  exact h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped Classical BigOperators NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "jets" => (fun j : Fin m => BoundedBooleanJet α ((j : ℕ) + 1))
local notation "jetRows" => (fun j => (Subtype.val : jets j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "output" => (Σ a : {a // ¬grid a}, jets (Sigma.fst (Subtype.val a)))
local notation "volume" => (∏ q : output, R (Sigma.fst (Subtype.val (Sigma.fst q))))
local notation "region" => (fun j (_ : jets j) => standardLatticeClosedQuarterBox (J j))
local notation "realProfile" => allocatedCoveredProfileDensity B U b hR hσ S x u v jetRows hb o bW d region
local notation "complexProfile" => allocatedCoveredComplexProfileDensity B U b hR hσ S x u v jetRows hb o bW d region

variable (modulus : ℕ)

theorem allocatedCoveredSiteTermDensity_error
    (residue : ∀ j : Fin m, Matrix (BoundedBooleanJet α (j.val + 1))
      (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (ideal : (output → ℝ) → ℝ)
    {T : Type*} [Fintype T] (c : T → ℂ)
    (f : T → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (he : ∀ z : AllocatedLongJetRows B U b S jets,
      ‖(ideal (allocatedLongJetRealCoordinates B U b S z) : ℂ) -
        (∑ i, c i * ∏ s, f i s (allocatedIdealSiteCoordinates B U b S z s)) / ((volume : ℝ) : ℂ)‖ ≤
        ε * allocatedIdealSiteEnvelope B U b S z)
    (y : EuclideanJetLayers U jets) :
    ‖(realProfile (allocatedLongProfileDensity B U b S x jetRows modulus residue ideal) y : ℂ) -
      ∑ i, c i * complexProfile (allocatedSiteTermDensity B U b S x modulus residue (f i)) y‖ ≤
      ε * |realProfile (allocatedLongProfileDensity B U b S x jetRows modulus residue
        (allocatedSiteBuffer B U b S)) y| := by
  have h := allocatedCoveredComplexProfileDensity_pointwise_abs_error B U b hR hσ S x u v jetRows hb o bW d
    region (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))
    (fun z => (allocatedLongProfileDensity B U b S x jetRows modulus residue ideal z : ℂ))
    (fun z => ∑ i, c i * allocatedSiteTermDensity B U b S x modulus residue (f i) z)
    (allocatedLongProfileDensity B U b S x jetRows modulus residue (allocatedSiteBuffer B U b S)) ε
    (allocatedSiteTermDensity_error B U b S x modulus residue hR ideal c f hε he) y
  rw [allocatedCoveredComplexProfileDensity_real B U b hR hσ S x u v jetRows hb o bW d region
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j)),
    allocatedCoveredComplexProfileDensity_sum B U b hR hσ S x u v jetRows hb o bW d region
      (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))] at h
  exact h

theorem allocatedCoveredIdealSiteApproximation_error
    (residue : ∀ j : Fin m, Matrix (BoundedBooleanJet α (j.val + 1))
      (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    {T : Type*} [Fintype T] (c : T → ℂ)
    (f : T → Finset α → (LayerSamplerAxis I n → ℝ) → ℂ)
    (δ : ℝ≥0) (hδ : 0 < δ) (hδ1 : δ ≤ 1) {ε : ℝ} (hε : 0 ≤ ε)
    (hsupport : ∀ i s w, (∃ a, 2 * idealSiteBoxRadius α m < |w a|) → f i s w = 0)
    (he : ∀ z : AllocatedLongJetRows B U b S jets,
      ‖(physicalActiveProfileIdeal (G := G) (B := B) (G × Option α) (layerSamplerDegree I n) grid
          (fun a => (Subtype.val : jets a.val.1 → Finset α))
          (fun a => R a.1) (fun a => hR a.1) δ (allocatedLongJetRealCoordinates B U b S z) : ℂ) -
        (∑ i, c i * ∏ s, f i s (allocatedIdealSiteCoordinates B U b S z s)) / ((volume : ℝ) : ℂ)‖ ≤
        ε / volume)
    (y : EuclideanJetLayers U jets) :
    ‖(realProfile (allocatedLongProfileDensity B U b S x jetRows modulus residue
        (physicalActiveProfileIdeal (G := G) (B := B) (G × Option α) (layerSamplerDegree I n) grid
          (fun a => (Subtype.val : jets a.val.1 → Finset α))
          (fun a => R a.1) (fun a => hR a.1) δ)) y : ℂ) -
      ∑ i, c i * complexProfile (allocatedSiteTermDensity B U b S x modulus residue (f i)) y‖ ≤
      ε * |realProfile (allocatedLongProfileDensity B U b S x jetRows modulus residue
        (allocatedSiteBuffer B U b S)) y| := by
  exact allocatedCoveredSiteTermDensity_error B U b hR hσ S x u v hb o bW d modulus residue _ c f hε
    (allocatedIdealSiteApproximation_envelope B U b S hR δ hδ hδ1 c f ε hsupport he) y

end Erdos3.VectorPolynomial

end

end OAI
