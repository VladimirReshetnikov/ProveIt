/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.AllocatedCoveredSiteBuffer
import OAI.Combinatorics.Progressions.Probability.MixedCoveredAbsoluteMass

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

local notation "grid" => allocatedGridAxis (I := I) U b S.value

theorem exists_allocated_ambient_grid_factor
    (C : Fin m → ℝ≥0)
    (hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    (K : ℝ≥0) (D : ℕ)
    (hscale : ∀ a : {a // grid a}, allocatedGridAxisScale B U b S a ≤ K)
    (hD : ∀ a : {a // grid a}, Fintype.card (O a.val.1) ≤ D) :
    ∃ g : (JetAmbientIndex O J → UnitAddCircle) → ℝ,
      LipschitzWith ((Fintype.card {a // grid a} * (D * (2 * K ^ 2))) *
        (∑ j, C j * Fintype.card (J j))) g ∧
      (∀ z, g z ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ w : JetAmbientIndex O J → ℝ, (∀ i, |w i| ≤ 1 / 4) →
        g (fun i => (w i : UnitAddCircle)) =
          allocatedNormalizedGridInterpolation B U b hR hσ S u rows
            (allocatedGridAmbientCoordinates B U b S o w) := by
  obtain ⟨hbound, hLip⟩ := allocatedNormalizedGridInterpolation_bounds
    B U b hR hσ S u rows K D hscale hD
  exact exists_real_quarter_torus_extension
    (fun w => allocatedNormalizedGridInterpolation B U b hR hσ S u rows
      (allocatedGridAmbientCoordinates B U b S o w)) _
    (hLip.comp (allocatedGridAmbientCoordinates_lipschitz B U b S o C hC))
    0 1 zero_le_one (fun w => hbound _)

theorem exists_allocated_ambient_grid_factor_uniform
    (C : Fin m → ℝ≥0)
    (hC : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖) :
    let K : ℝ≥0 := (S.value : ℝ≥0) ^ (layerTailDegree m + 1)
    let D := Fintype.card (Σ a : LayerSamplerAxis I n, O a.1)
    ∃ g : (JetAmbientIndex O J → UnitAddCircle) → ℝ,
      LipschitzWith ((Fintype.card {a // grid a} * (D * (2 * K ^ 2))) *
        (∑ j, C j * Fintype.card (J j))) g ∧
      (∀ z, g z ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ w : JetAmbientIndex O J → ℝ, (∀ i, |w i| ≤ 1 / 4) →
        g (fun i => (w i : UnitAddCircle)) =
          allocatedNormalizedGridInterpolation B U b hR hσ S u rows
            (allocatedGridAmbientCoordinates B U b S o w) := by
  intro K D
  apply exists_allocated_ambient_grid_factor B U b hR hσ S u rows o C hC K D
  · exact fun a => (allocatedGridAxisScale_bounds B U b S a).2
  · intro a
    apply Fintype.card_le_of_injective (fun t : O a.val.1 => (⟨a.val, t⟩ : Σ c : LayerSamplerAxis I n, O c.1))
    intro t w h
    exact eq_of_heq (Sigma.mk.inj h).2

theorem allocatedAmbientGridFactor_chart
    (g : (JetAmbientIndex O J → UnitAddCircle) → ℝ)
    (hvalue : ∀ w : JetAmbientIndex O J → ℝ, (∀ i, |w i| ≤ 1 / 4) →
      g (fun i => (w i : UnitAddCircle)) =
        allocatedNormalizedGridInterpolation B U b hR hσ S u rows
          (allocatedGridAmbientCoordinates B U b S o w))
    (x : G → IntegerScalarCubeBox α S.value)
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) (allocatedPrincipalSides B U b S))
    (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
    (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
    (d : ℕ) [NeZero d] (z : MixedCoveredJetSource I O Q n d)
    (hz : z ∈ mixedCoveredJetRegion U o b d (fun j _ => standardLatticeClosedQuarterBox (J j))) :
    g (coveredJetAmbientTorus U d (mixedCoveredJetChart U o b hb bW d z)) =
      allocatedGridJetDensity B U b hR hσ S x u v rows
        (fun a => coefficientJetAxisEquiv O I n z.1 a.val) := by
  rw [coveredJetAmbientTorus_chart U b hb o bW d z]
  have hsmall : ∀ a, |mixedJetAmbientPoint U b o z.1 a| ≤ 1 / 4 := by
    rintro ⟨j, t, i⟩
    exact (hz j (Set.mem_univ j) t (Set.mem_univ t)).1 i
  rw [hvalue _ hsmall, allocatedGridAmbientCoordinates_point,
    allocatedNormalizedGridInterpolation_grid B U b hR hσ S u rows x v]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit O I n grid
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)
local notation "quarter" => (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := Q) U o b d quarter

noncomputable def allocatedGridlessCoveredProfile (f : AllocatedLongJetRows B U b S O → ℝ) :
    EuclideanJetLayers U O → ℝ :=
  restrictedChartDensity chart region 1 (fun z : MixedCoveredJetSource I O Q n d =>
    (coefficientDeckJetDensity root dirs rows d z.2 / coveredJetArrayScale (O := O) U) *
      f ((split z.1).2))

theorem allocatedCoveredProfileDensity_grid_factor
    (g : (JetAmbientIndex O J → UnitAddCircle) → ℝ)
    (hvalue : ∀ w : JetAmbientIndex O J → ℝ, (∀ i, |w i| ≤ 1 / 4) →
      g (fun i => (w i : UnitAddCircle)) =
        allocatedNormalizedGridInterpolation B U b hR hσ S u rows
          (allocatedGridAmbientCoordinates B U b S o w))
    (f : AllocatedLongJetRows B U b S O → ℝ) :
    allocatedCoveredProfileDensity B U b hR hσ S x u v rows hb o bW d quarter f =
      fun y => g (coveredJetAmbientTorus U d y) *
        allocatedGridlessCoveredProfile B U b S x u v rows hb o bW d f y := by
  have hinj := mixedCoveredJetChart_injOn U o b hb bW d quarter
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))
  unfold allocatedCoveredProfileDensity
  symm
  apply restrictedChartDensity_eq_of_values chart region hinj
  · intro z hz
    rw [allocatedGridlessCoveredProfile, restrictedChartDensity_apply chart region 1 _ hinj hz, one_mul,
      allocatedAmbientGridFactor_chart B U b hR hσ S u rows o g hvalue x v hb bW d z hz]
    unfold allocatedCoveredFixedFactor
    ring
  · intro y hy
    rw [allocatedGridlessCoveredProfile, restrictedChartDensity_zero chart region 1 _ hy, mul_zero]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit O I n grid
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)
local notation "quarter" => (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := Q) U o b d quarter

theorem allocatedCoveredProfileDensity_grid_factor_on_chart
    (g : (JetAmbientIndex O J → UnitAddCircle) → ℝ)
    (hvalue : ∀ z : MixedCoveredJetSource I O Q n d, z ∈ region →
      g (coveredJetAmbientTorus U d (chart z)) =
        allocatedGridJetDensity B U b hR hσ S x u v rows
          (fun a => coefficientJetAxisEquiv O I n z.1 a.val))
    (f : AllocatedLongJetRows B U b S O → ℝ) :
    allocatedCoveredProfileDensity B U b hR hσ S x u v rows hb o bW d quarter f =
      fun y => g (coveredJetAmbientTorus U d y) *
        allocatedGridlessCoveredProfile B U b S x u v rows hb o bW d f y := by
  have hinj := mixedCoveredJetChart_injOn U o b hb bW d quarter
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))
  unfold allocatedCoveredProfileDensity
  symm
  apply restrictedChartDensity_eq_of_values chart region hinj
  · intro z hz
    rw [allocatedGridlessCoveredProfile, restrictedChartDensity_apply chart region 1 _ hinj hz,
      one_mul, hvalue z hz]
    unfold allocatedCoveredFixedFactor
    ring
  · intro y hy
    rw [allocatedGridlessCoveredProfile, restrictedChartDensity_zero chart region 1 _ hy, mul_zero]

theorem allocatedCoveredProfileDensity_grid_error_on_chart
    (g : (JetAmbientIndex O J → UnitAddCircle) → ℂ) (ε : ℝ)
    (hvalue : ∀ z : MixedCoveredJetSource I O Q n d, z ∈ region →
      ‖(allocatedGridJetDensity B U b hR hσ S x u v rows
          (fun a => coefficientJetAxisEquiv O I n z.1 a.val) : ℂ) -
        g (coveredJetAmbientTorus U d (chart z))‖ ≤ ε)
    (f : AllocatedLongJetRows B U b S O → ℝ) (y : EuclideanJetLayers U O) :
    ‖(allocatedCoveredProfileDensity B U b hR hσ S x u v rows hb o bW d quarter f y : ℂ) -
      g (coveredJetAmbientTorus U d y) *
        (allocatedGridlessCoveredProfile B U b S x u v rows hb o bW d f y : ℂ)‖ ≤
      ε * restrictedChartDensity chart region 1
        (fun z : MixedCoveredJetSource I O Q n d =>
          |(coefficientDeckJetDensity root dirs rows d z.2 / coveredJetArrayScale (O := O) U) *
            f ((split z.1).2)|) y := by
  have hinj := mixedCoveredJetChart_injOn U o b hb bW d quarter
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))
  unfold allocatedCoveredProfileDensity allocatedGridlessCoveredProfile
  by_cases hy : y ∈ chart '' region
  · obtain ⟨z, hz, rfl⟩ := hy
    simp only [restrictedChartDensity_apply chart region 1 _ hinj hz, one_mul]
    let a := allocatedGridJetDensity B U b hR hσ S x u v rows
      (fun a => coefficientJetAxisEquiv O I n z.1 a.val)
    let w := coefficientDeckJetDensity root dirs rows d z.2 / coveredJetArrayScale (O := O) U
    have he : ((allocatedCoveredFixedFactor B U b hR hσ S x u v rows Q d z.1 z.2 *
        f ((split z.1).2) : ℝ) : ℂ) = (a : ℂ) * ((w * f ((split z.1).2) : ℝ) : ℂ) := by
      dsimp [a, w, allocatedCoveredFixedFactor]
      push_cast
      ring
    rw [he, ← sub_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hvalue z hz) (abs_nonneg _)
  · simp [restrictedChartDensity_zero chart region 1 _ hy]

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
variable {R σ : Fin m → ℝ}
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

variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)] (d : ℕ) [NeZero d]

local notation "gridRef" => allocatedFrozenJetReference B U b S O
local notation "longRef" => allocatedLongJetReference B U b S O
local notation "raw" => mixedCoveredJetRawReference (I := I) (O := O) (E := Q) (n := n) d

noncomputable def allocatedGridlessWeightedKernel
    (g : AllocatedFrozenJetRows B U b S O → ℝ) (f : AllocatedLongJetRows B U b S O → ℝ)
    (z : MixedCoveredJetSource I O Q n d) : ℝ :=
  g ((split z.1).1) * f ((split z.1).2) * coefficientDeckJetDensity root dirs rows d z.2

theorem allocatedGridlessWeightedKernel_measurable
    (g : AllocatedFrozenJetRows B U b S O → ℝ) (f : AllocatedLongJetRows B U b S O → ℝ)
    (hg : Measurable g) (hf : Measurable f) :
    Measurable (allocatedGridlessWeightedKernel B U b S x u v rows (Q := Q) d g f) := by
  have hs : Measurable (fun z : MixedCoveredJetSource I O Q n d => split z.1) :=
    (split).measurable.comp measurable_fst
  have hd : Measurable (coefficientDeckJetDensity root dirs rows d : (∀ j, O j → Q j → ZMod d) → ℝ) :=
    measurable_of_finite _
  exact ((hg.comp (measurable_fst.comp hs)).mul (hf.comp (measurable_snd.comp hs))).mul
    (hd.comp measurable_snd)

theorem allocatedGridlessWeightedKernel_mass_data
    (g : AllocatedFrozenJetRows B U b S O → ℝ) (f : AllocatedLongJetRows B U b S O → ℝ)
    (hg : Integrable g gridRef) (hf : Integrable f longRef) :
    Integrable (allocatedGridlessWeightedKernel B U b S x u v rows (Q := Q) d g f) raw ∧
      (∫ z, |allocatedGridlessWeightedKernel B U b S x u v rows (Q := Q) d g f z| ∂raw) =
        (∫ z, |g z| ∂gridRef) * ∫ z, |f z| ∂longRef := by
  let μd := (PMF.uniformOfFintype (∀ j, O j → Q j → ZMod d)).toMeasure
  let fd : (∀ j, O j → Q j → ZMod d) → ℝ := coefficientDeckJetDensity root dirs rows d
  let e := MeasurableEquiv.prodCongr split (MeasurableEquiv.refl (∀ j, O j → Q j → ZMod d))
  let F (z : (AllocatedFrozenJetRows B U b S O × AllocatedLongJetRows B U b S O) ×
      (∀ j, O j → Q j → ZMod d)) : ℝ := g z.1.1 * f z.1.2 * fd z.2
  let : IsProbabilityMeasure (realDensityMeasure μd fd) := coefficientDeckJetDensity_probability _ _ rows d
  have hfd := boundedDensity_mass μd fd (measurable_of_finite _) (coefficientDeckJetDensity_nonneg _ _ rows d)
    (coefficientDeckJetDensity_le_card _ _ rows d)
  have hFi : Integrable F (((gridRef).prod longRef).prod μd) := (hg.mul_prod hf).mul_prod hfd.1
  have he : MeasurePreserving e raw (((gridRef).prod longRef).prod μd) :=
    (coefficientJetAxisSplit_measurePreserving O I n grid).prod (MeasurePreserving.id μd)
  refine ⟨(he.integrable_comp_emb e.measurableEmbedding).mpr hFi, ?_⟩
  change (∫ z, |F (e z)| ∂raw) = _
  rw [he.integral_comp e.measurableEmbedding (fun z => |F z|)]
  have habs : (fun z => |F z|) = (fun z => |g z.1.1| * |f z.1.2| * fd z.2) := by
    funext z
    dsimp only [F]
    rw [abs_mul, abs_mul, abs_of_nonneg (coefficientDeckJetDensity_nonneg root dirs rows d z.2)]
  rw [habs, integral_prod_mul (μ := (gridRef).prod longRef) (ν := μd)
    (fun z : AllocatedFrozenJetRows B U b S O × AllocatedLongJetRows B U b S O => |g z.1| * |f z.2|) fd,
    integral_prod_mul (μ := gridRef) (ν := longRef) (fun z => |g z|) (fun z => |f z|), hfd.2, mul_one]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (y y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "root" z => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x z
local notation "dirs" z => allocatedPhysicalCubeDirections B U b S x z

variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

theorem allocatedWholeDeckDensity_eq (M : ℕ)
    (hperiod : ∀ j, integerScalarLattice (O j) (M : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (hlabel : principalResidueLabel M y = principalResidueLabel M y₀)
    (r : ∀ j, O j → Q j → ZMod d) :
    coefficientDeckJetDensity (root y) (dirs y) rows d r =
      coefficientDeckJetDensity (root y₀) (dirs y₀) rows d r := by
  unfold coefficientDeckJetDensity
  have h := congrArg (fun p : PMF (∀ j, O j → Q j → ZMod d) =>
    (Fintype.card (∀ j, O j → Q j → ZMod d) : ℝ) * (p r).toReal)
      (allocatedWholeDeckJet_law_eq B U b S x y y₀ rows Q M hperiod hlabel d)
  convert h using 6

theorem allocatedWholeGridlessProfile_eq (M : ℕ)
    (hperiod : ∀ j, integerScalarLattice (O j) (M : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (hlabel : principalResidueLabel M y = principalResidueLabel M y₀)
    (f : AllocatedLongJetRows B U b S O → ℝ) :
    allocatedGridlessCoveredProfile B U b S x (principalAxisRestrict grid y)
      (principalAxisRestrict (fun a => ¬grid a) y) rows hb o bW d f =
    allocatedGridlessCoveredProfile B U b S x (principalAxisRestrict grid y₀)
      (principalAxisRestrict (fun a => ¬grid a) y₀) rows hb o bW d f := by
  unfold allocatedGridlessCoveredProfile
  simp only [principalAxisJoin_restrict]
  congr 1
  funext z
  rw [allocatedWholeDeckDensity_eq B U b S x y y₀ rows d M hperiod hlabel]

noncomputable def allocatedWholeMaskedGridlessProfile (M : ℕ)
    (f : ((Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a))) → ℝ) → ℝ) :
    EuclideanJetLayers U O → ℝ :=
  allocatedGridlessCoveredProfile B U b S x (principalAxisRestrict grid y)
    (principalAxisRestrict (fun a => ¬grid a) y) rows hb o bW d
    (allocatedLongProfileDensity B U b S x rows M
      (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
        (principalAxisRestrict grid y) rows j (principalAxisRestrict (fun a => ¬grid a) y)) M) f)

theorem allocatedWholeMaskedGridlessProfile_eq (M : ℕ)
    (hperiod : ∀ j, integerScalarLattice (O j) (M : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (hlabel : principalResidueLabel M y = principalResidueLabel M y₀)
    (f : ((Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a))) → ℝ) → ℝ) :
    allocatedWholeMaskedGridlessProfile B U b S x y rows hb o bW d M f =
      allocatedWholeMaskedGridlessProfile B U b S x y₀ rows hb o bW d M f := by
  have hres : (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict grid y) rows j (principalAxisRestrict (fun a => ¬grid a) y)) M) =
    (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) M) :=
    funext (allocatedWholeNonkernelJetMatrix_residue B U b S x y y₀ rows M hlabel)
  unfold allocatedWholeMaskedGridlessProfile
  rw [hres]
  exact allocatedWholeGridlessProfile_eq B U b S x y y₀ rows hb o bW d M hperiod hlabel _

theorem exists_allocatedWholeMaskedGridlessProfile_by_residue (M : ℕ)
    (hperiod : ∀ j, integerScalarLattice (O j) (M : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (f : ((Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a))) → ℝ) → ℝ) :
    ∃ P : (PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod M) →
        EuclideanJetLayers U O → ℝ,
      ∀ z : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S),
        allocatedWholeMaskedGridlessProfile B U b S x z rows hb o bW d M f =
          P (principalResidueLabel M z) := by
  let profile := fun z => allocatedWholeMaskedGridlessProfile B U b S x z rows hb o bW d M f
  refine ⟨fun r => if hr : ∃ z, principalResidueLabel M z = r then profile hr.choose else 0, ?_⟩
  intro z
  have hr : ∃ w, principalResidueLabel M w = principalResidueLabel M z := ⟨z, rfl⟩
  simp only [dite_eq_left hr]
  exact allocatedWholeMaskedGridlessProfile_eq B U b S x z hr.choose rows hb o bW d M
    hperiod hr.choose_spec.symm f

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ}
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit O I n grid
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)
local notation "quarter" => (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := Q) U o b d quarter

theorem allocatedGridlessCoveredProfile_measurable
    (f : AllocatedLongJetRows B U b S O → ℝ) (hf : Measurable f) :
    Measurable (allocatedGridlessCoveredProfile B U b S x u v rows hb o bW d f) := by
  apply mixedCoveredJet_restrictedDensity_measurable U o b hb bW d quarter
    (fun j _ => (standardLatticeClosedQuarterBox_isCompact (J j)).measurableSet)
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))
  have hs : Measurable (fun z : MixedCoveredJetSource I O Q n d => split z.1) :=
    (split).measurable.comp measurable_fst
  have hd : Measurable (coefficientDeckJetDensity root dirs rows d : (∀ j, O j → Q j → ZMod d) → ℝ) :=
    measurable_of_finite _
  exact ((hd.comp measurable_snd).div_const _).mul (hf.comp (measurable_snd.comp hs))

theorem allocatedGridlessCoveredProfile_mul_eq
    (g : AllocatedFrozenJetRows B U b S O → ℝ) (f : AllocatedLongJetRows B U b S O → ℝ)
    (χ : EuclideanJetLayers U O → ℝ)
    (hχ : ∀ z ∈ region, χ (chart z) = g ((split z.1).1)) :
    (fun y => χ y * allocatedGridlessCoveredProfile B U b S x u v rows hb o bW d f y) =
      restrictedChartDensity chart region 1 (fun z =>
        allocatedGridlessWeightedKernel B U b S x u v rows d g f z / coveredJetArrayScale (O := O) U) := by
  have hinj := mixedCoveredJetChart_injOn U o b hb bW d quarter
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))
  apply restrictedChartDensity_eq_of_values chart region hinj
  · intro z hz
    rw [allocatedGridlessCoveredProfile, restrictedChartDensity_apply chart region 1 _ hinj hz,
      one_mul, hχ z hz]
    unfold allocatedGridlessWeightedKernel
    ring
  · intro y hy
    rw [allocatedGridlessCoveredProfile, restrictedChartDensity_zero chart region 1 _ hy, mul_zero]

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

local notation "gridRef" => allocatedFrozenJetReference B U b S O
local notation "longRef" => allocatedLongJetReference B U b S O
local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))

theorem allocatedGridlessCoveredProfile_weighted_mass
    (g : AllocatedFrozenJetRows B U b S O → ℝ) (f : AllocatedLongJetRows B U b S O → ℝ)
    (χ : EuclideanJetLayers U O → ℝ)
    (hχ : ∀ z ∈ region, χ (chart z) = g ((split z.1).1))
    (hgm : Measurable g) (hfm : Measurable f)
    (hgi : Integrable g gridRef) (hfi : Integrable f longRef) :
    Integrable (fun y => χ y * allocatedGridlessCoveredProfile B U b S x u v rows hb o bW d f y) haar ∧
      (∫ y, |χ y * allocatedGridlessCoveredProfile B U b S x u v rows hb o bW d f y| ∂haar) ≤
        (∫ z, |g z| ∂gridRef) * ∫ z, |f z| ∂longRef := by
  have heq := allocatedGridlessCoveredProfile_mul_eq B U b S x u v rows hb o bW d g f χ hχ
  have hm := allocatedGridlessWeightedKernel_measurable B U b S x u v rows (Q := Q) d g f hgm hfm
  have hk := allocatedGridlessWeightedKernel_mass_data B U b S x u v rows (Q := Q) d g f hgi hfi
  have hi := mixedCoveredJet_normalized_integrable U o b hb bW d ν quarter
    (fun j _ => (standardLatticeClosedQuarterBox_isCompact (J j)).measurableSet)
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j)) _ hm hk.1
  have he := (mixedCoveredJet_normalized_integral_abs_le U o b hb bW d ν quarter
    (fun j _ => (standardLatticeClosedQuarterBox_isCompact (J j)).measurableSet)
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j)) _ hm hk.1).trans_eq hk.2
  exact ⟨by simpa only [← heq] using hi, by simpa only [← heq] using he⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (O : Fin m → Type*) [∀ j, Fintype (O j)]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit O I n grid
local notation "quarter" => (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := Q) U o b d quarter

noncomputable def allocatedChartGridMultiplier (g : AllocatedFrozenJetRows B U b S O → ℝ) :
    EuclideanJetLayers U O → ℝ :=
  restrictedChartDensity chart region 1 (fun z => g ((split z.1).1))

omit [∀ j, Fintype (O j)] in
theorem allocatedChartGridMultiplier_apply (g : AllocatedFrozenJetRows B U b S O → ℝ)
    (z : MixedCoveredJetSource I O Q n d) (hz : z ∈ region) :
    allocatedChartGridMultiplier B U b S O hb o bW d g (chart z) = g ((split z.1).1) := by
  rw [allocatedChartGridMultiplier, restrictedChartDensity_apply _ _ _ _
    (mixedCoveredJetChart_injOn U o b hb bW d quarter
      (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))) hz, one_mul]

theorem allocatedChartGridMultiplier_measurable (g : AllocatedFrozenJetRows B U b S O → ℝ)
    (hg : Measurable g) : Measurable (allocatedChartGridMultiplier B U b S O hb o bW d g) := by
  apply mixedCoveredJet_restrictedDensity_measurable U o b hb bW d quarter
    (fun j _ => (standardLatticeClosedQuarterBox_isCompact (J j)).measurableSet)
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))
  exact hg.comp (measurable_fst.comp ((split).measurable.comp measurable_fst))

omit [∀ j, Fintype (O j)] in
theorem allocatedChartGridMultiplier_mean {A : Type*} [Fintype A]
    (p : FiniteProbabilityWeights A) (g : A → AllocatedFrozenJetRows B U b S O → ℝ) :
    (fun y => p.mean (fun a => allocatedChartGridMultiplier B U b S O hb o bW d (g a) y)) =
      allocatedChartGridMultiplier B U b S O hb o bW d (fun z => p.mean (fun a => g a z)) := by
  apply restrictedChartDensity_eq_of_values chart region
    (mixedCoveredJetChart_injOn U o b hb bW d quarter
      (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j)))
  · intro z hz
    simp only [allocatedChartGridMultiplier_apply B U b S O hb o bW d _ z hz]
  · intro y hy
    simp only [allocatedChartGridMultiplier, restrictedChartDensity_zero _ _ _ _ hy, p.mean_const]

variable {α : Type*} [DecidableEq α] (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a) (allocatedPrincipalSides B U b S))
variable (rows : ∀ j, O j → Finset α)

theorem allocatedCoveredProfileDensity_grid_multiplier (f : AllocatedLongJetRows B U b S O → ℝ) :
    allocatedCoveredProfileDensity B U b hR hσ S x u v rows hb o bW d quarter f =
      fun y => allocatedChartGridMultiplier B U b S O hb o bW d
        (allocatedGridJetDensity B U b hR hσ S x u v rows) y *
          allocatedGridlessCoveredProfile B U b S x u v rows hb o bW d f y := by
  symm
  rw [allocatedGridlessCoveredProfile_mul_eq B U b S x u v rows hb o bW d
    (allocatedGridJetDensity B U b hR hσ S x u v rows) f
    (allocatedChartGridMultiplier B U b S O hb o bW d
      (allocatedGridJetDensity B U b hR hσ S x u v rows))
    (allocatedChartGridMultiplier_apply B U b S O hb o bW d _)]
  unfold allocatedCoveredProfileDensity
  congr 1
  funext z
  change (allocatedGridJetDensity B U b hR hσ S x u v rows ((split z.1).1) *
      f ((split z.1).2) * _ / coveredJetArrayScale (O := O) U) =
    (allocatedGridJetDensity B U b hR hσ S x u v rows ((split z.1).1) *
      _ / coveredJetArrayScale (O := O) U) * f ((split z.1).2)
  ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (O : Fin m → Type*) [∀ j, Fintype (O j)]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit O I n grid
local notation "quarter" => (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := Q) U o b d quarter

noncomputable def allocatedComplexGridMultiplier (g : AllocatedFrozenJetRows B U b S O → ℂ)
    (y : EuclideanJetLayers U O) : ℂ :=
  (allocatedChartGridMultiplier B U b S O hb o bW d (fun z => (g z).re) y : ℂ) +
    (allocatedChartGridMultiplier B U b S O hb o bW d (fun z => (g z).im) y : ℂ) * Complex.I

omit [∀ j, Fintype (O j)] in
theorem allocatedComplexGridMultiplier_apply (g : AllocatedFrozenJetRows B U b S O → ℂ)
    (z : MixedCoveredJetSource I O Q n d) (hz : z ∈ region) :
    allocatedComplexGridMultiplier B U b S O hb o bW d g (chart z) = g ((split z.1).1) := by
  simp only [allocatedComplexGridMultiplier,
    allocatedChartGridMultiplier_apply B U b S O hb o bW d _ z hz, Complex.re_add_im]

omit [∀ j, Fintype (O j)] in
theorem allocatedComplexGridMultiplier_zero (g : AllocatedFrozenJetRows B U b S O → ℂ)
    (y : EuclideanJetLayers U O) (hy : y ∉ chart '' region) :
    allocatedComplexGridMultiplier B U b S O hb o bW d g y = 0 := by
  simp only [allocatedComplexGridMultiplier, allocatedChartGridMultiplier,
    restrictedChartDensity_zero _ _ _ _ hy, Complex.ofReal_zero, zero_mul, zero_add]

theorem allocatedComplexGridMultiplier_measurable (g : AllocatedFrozenJetRows B U b S O → ℂ)
    (hg : Measurable g) : Measurable (allocatedComplexGridMultiplier B U b S O hb o bW d g) := by
  exact ((allocatedChartGridMultiplier_measurable B U b S O hb o bW d _
    (Complex.measurable_re.comp hg)).complex_ofReal).add
      (((allocatedChartGridMultiplier_measurable B U b S O hb o bW d _
        (Complex.measurable_im.comp hg)).complex_ofReal).mul_const Complex.I)

omit [∀ j, Fintype (O j)] in
theorem allocatedChartGridMultiplier_nonneg (g : AllocatedFrozenJetRows B U b S O → ℝ)
    (hg : ∀ z, 0 ≤ g z) (y : EuclideanJetLayers U O) :
    0 ≤ allocatedChartGridMultiplier B U b S O hb o bW d g y := by
  by_cases hy : y ∈ chart '' region
  · obtain ⟨z, hz, rfl⟩ := hy
    rw [allocatedChartGridMultiplier_apply B U b S O hb o bW d _ z hz]
    exact hg _
  · rw [allocatedChartGridMultiplier, restrictedChartDensity_zero _ _ _ _ hy]

omit [∀ j, Fintype (O j)] in
theorem allocatedComplexGridMultiplier_norm (g : AllocatedFrozenJetRows B U b S O → ℂ)
    (y : EuclideanJetLayers U O) :
    ‖allocatedComplexGridMultiplier B U b S O hb o bW d g y‖ =
      allocatedChartGridMultiplier B U b S O hb o bW d (fun z => ‖g z‖) y := by
  by_cases hy : y ∈ chart '' region
  · obtain ⟨z, hz, rfl⟩ := hy
    rw [allocatedComplexGridMultiplier_apply B U b S O hb o bW d _ z hz,
      allocatedChartGridMultiplier_apply B U b S O hb o bW d _ z hz]
  · rw [allocatedComplexGridMultiplier_zero B U b S O hb o bW d _ y hy,
      allocatedChartGridMultiplier, restrictedChartDensity_zero _ _ _ _ hy, norm_zero]

omit [∀ j, Fintype (O j)] in
theorem allocatedGridMultiplier_error
    (f : AllocatedFrozenJetRows B U b S O → ℝ)
    (g : AllocatedFrozenJetRows B U b S O → ℂ)
    (w : AllocatedFrozenJetRows B U b S O → ℝ) (E : ℝ)
    (he : ∀ z, ‖(f z : ℂ) - g z‖ ≤ E * w z) (y : EuclideanJetLayers U O) :
    ‖(allocatedChartGridMultiplier B U b S O hb o bW d f y : ℂ) -
        allocatedComplexGridMultiplier B U b S O hb o bW d g y‖ ≤
      E * allocatedChartGridMultiplier B U b S O hb o bW d w y := by
  by_cases hy : y ∈ chart '' region
  · obtain ⟨z, hz, rfl⟩ := hy
    simpa only [allocatedComplexGridMultiplier_apply B U b S O hb o bW d _ z hz,
      allocatedChartGridMultiplier_apply B U b S O hb o bW d _ z hz] using he ((split z.1).1)
  · simp only [allocatedComplexGridMultiplier_zero B U b S O hb o bW d _ y hy,
      allocatedChartGridMultiplier, restrictedChartDensity_zero _ _ _ _ hy,
      Complex.ofReal_zero, sub_zero, norm_zero, mul_zero, le_refl]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "longScale" => (∏ a, allocatedLongJetOutputScale B U b S (O := O) a)
local notation "covolumes" => (∏ j, mixedDensityCovolumeRatio (euclideanSubspace (U j)) (b j) ^ Fintype.card (O j))

theorem allocatedGridlessScale_cancel (c : ℝ) :
    c / longScale / coveredJetArrayScale (O := O) U =
      c * allocatedGridJetScale B U b S (O := O) * covolumes := by
  rw [← allocatedGridLongJetScale_covolume B U b S]
  have hg := (allocatedGridJetScale_pos B U b S (O := O)).ne'
  have hl : longScale ≠ 0 := (Finset.prod_pos
    (fun a _ => allocatedLongJetOutputScale_pos B U b S (O := O) a)).ne'
  have hc := (coveredJetArrayScale_pos (O := O) U).ne'
  field_simp

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable (rows : ∀ j, O j → Finset α)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)
local notation "quarter" => (fun j (_ : O j) => standardLatticeClosedQuarterBox (J j))
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (E := Q) U o b d quarter

omit [Fintype α] in
theorem allocatedGridlessCoveredProfile_abs_le
    (f : AllocatedLongJetRows B U b S O → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hf : ∀ z (r : ∀ j, O j → Q j → ZMod d),
      coefficientDeckJetDensity root dirs rows d r * |f z| ≤ c / longScale)
    (y : EuclideanJetLayers U O) :
    |allocatedGridlessCoveredProfile B U b S x u v rows hb o bW d f y| ≤
      c * allocatedGridJetScale B U b S (O := O) * covolumes := by
  rw [← allocatedGridlessScale_cancel B U b S c]
  have hl : 0 < longScale := Finset.prod_pos (fun a _ => allocatedLongJetOutputScale_pos B U b S a)
  by_cases hy : y ∈ chart '' region
  · obtain ⟨z, hz, rfl⟩ := hy
    rw [allocatedGridlessCoveredProfile, restrictedChartDensity_apply chart region 1 _
      (mixedCoveredJetChart_injOn U o b hb bW d quarter
        (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))) hz, one_mul]
    rw [abs_mul, abs_div, abs_of_nonneg (coefficientDeckJetDensity_nonneg root dirs rows d z.2),
      abs_of_pos (coveredJetArrayScale_pos (O := O) U)]
    calc
      _ = (coefficientDeckJetDensity root dirs rows d z.2 *
          |f ((coefficientJetAxisSplit O I n grid z.1).2)|) / coveredJetArrayScale (O := O) U := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (hf _ _) (coveredJetArrayScale_pos (O := O) U).le
  · rw [allocatedGridlessCoveredProfile, restrictedChartDensity_zero chart region 1 _ hy, abs_zero]
    exact div_nonneg (div_nonneg hc hl.le) (coveredJetArrayScale_pos (O := O) U).le

end Erdos3.VectorPolynomial

end

end OAI
