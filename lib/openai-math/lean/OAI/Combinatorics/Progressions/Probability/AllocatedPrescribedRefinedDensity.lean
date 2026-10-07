import OAI.Combinatorics.Progressions.Estimates.AllocatedNarrowReferenceTest
import OAI.Combinatorics.Progressions.Estimates.AllocatedStrideRefinedStatement

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical Matrix

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
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)
local notation "axis" => coefficientJetAxisEquiv O I n

local notation "rootAt" => (fun w => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u w))
local notation "dirsAt" => (fun w => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u w))
local notation "scale" => (∏ a, allocatedLongJetOutputScale B U b S (O := O) a)

variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)] (d : ℕ) [NeZero d]

noncomputable def allocatedCoveredFixedFactor
    (z : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ))
    (r : ∀ j, O j → Q j → ZMod d) : ℝ :=
  allocatedGridJetDensity B U b hR hσ S x u v rows (fun a => axis z a.val) *
    coefficientDeckJetDensity root dirs rows d r / coveredJetArrayScale (O := O) U

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

omit [Fintype α] [∀ j, DecidableEq (O j)] in
theorem allocatedCoveredFixedFactor_nonneg
    (z : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ))
    (r : ∀ j, O j → Q j → ZMod d) :
    0 ≤ allocatedCoveredFixedFactor B U b hR hσ S x u v rows Q d z r :=
  div_nonneg (mul_nonneg (allocatedGridJetDensity_mem_Icc B U b hR hσ S x u v rows _).1
    (coefficientDeckJetDensity_nonneg root dirs rows d r)) (coveredJetArrayScale_pos U).le

omit [Fintype α]
  [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in
theorem allocatedPhysicalDeckDensity_eq
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    (M : ℕ) (hperiod : ∀ j, integerScalarLattice (O j) (M : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (hv : principalResidueLabel M v = principalResidueLabel M v₀)
    (r : ∀ j, O j → Q j → ZMod d) :
    coefficientDeckJetDensity root dirs rows d r =
      coefficientDeckJetDensity (rootAt v₀) (dirsAt v₀) rows d r := by
  unfold coefficientDeckJetDensity
  have heq := allocatedPhysicalDeckJet_law_eq_of_residue B U b S x u v v₀ rows Q M hperiod hv d
  have hval := congrArg (fun p : PMF (∀ j, O j → Q j → ZMod d) =>
    (Fintype.card (∀ j, O j → Q j → ZMod d) : ℝ) * (p r).toReal) heq
  convert hval using 6

omit [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in
theorem allocatedPhysicalCoveredDensity_factorization
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
    (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
    (pivot : ∀ j, O j ↪ BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1))
    (hpivot : ∀ j, ((boundedCoefficientJetMatrix root dirs (j.val + 1) (rows j)).submatrix id (pivot j)).det ≠ 0)
    (hσ1 : ∀ j, σ j ≤ 1)
    (M : ℕ) (hperiod : ∀ j, integerScalarLattice (O j) (M : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (hv : principalResidueLabel M v = principalResidueLabel M v₀)
    (z : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ))
    (r : ∀ j, O j → Q j → ZMod d) :
    canonicalCoveredArrayDensity U root dirs rows pivot hpivot
      (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
      (allocatedLayerIntegerPMFs B U b hR hσ S) d (z, r) =
    allocatedCoveredFixedFactor B U b hR hσ S x u v₀ rows Q d z r *
      allocatedLongJetDensity B U b hR hσ S x u v rows s hA hσ1 (fun a => axis z a.val) := by
  rw [canonicalCoveredArrayDensity,
    allocatedPhysicalMixedDensity_factorization B U b hR hσ S x u v rows v₀ s hA pivot hpivot hσ1 z,
    allocatedPhysicalDeckDensity_eq B U b S x u v rows Q d v₀ M hperiod hv r]
  unfold allocatedCoveredFixedFactor
  ring

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]

omit [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in
theorem allocatedPhysicalCoveredDensity_mean
    (weights : FiniteProbabilityWeights (PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides))
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
    (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
    (pivot : ∀ j, O j ↪ BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1))
    (hpivot : ∀ w j, ((boundedCoefficientJetMatrix (rootAt w) (dirsAt w)
      (j.val + 1) (rows j)).submatrix id (pivot j)).det ≠ 0)
    (hσ1 : ∀ j, σ j ≤ 1)
    (M : ℕ) (hperiod : ∀ j, integerScalarLattice (O j) (M : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (hresidue : ∀ w, weights.weight w ≠ 0 → principalResidueLabel M w = principalResidueLabel M v₀)
    (z : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ))
    (r : ∀ j, O j → Q j → ZMod d) :
    weights.mean (fun w => canonicalCoveredArrayDensity U (rootAt w) (dirsAt w) rows pivot (hpivot w)
      (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
      (allocatedLayerIntegerPMFs B U b hR hσ S) d (z, r)) =
    allocatedCoveredFixedFactor B U b hR hσ S x u v₀ rows Q d z r *
      weights.mean (fun w => allocatedLongJetDensity B U b hR hσ S x u w rows s hA hσ1
        (fun a => axis z a.val)) := by
  rw [← weights.mean_const_mul]
  exact weights.mean_congr_on_support (fun w hw =>
    allocatedPhysicalCoveredDensity_factorization B U b hR hσ S x u w rows Q d
      v₀ s hA pivot (hpivot w) hσ1 M hperiod (hresidue w hw) z r)

theorem allocatedPhysicalCoveredDensity_residue_comparison
    (M : ℕ) (hM : 0 < M)
    (label : PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
      (fun a => layerSamplerDegree I n a.val) → Option α → ZMod M)
    (hsize : ∀ t, (Fintype.card α + 1) * M ≤ principalAxisLength (fun a => ¬grid a) sides t)
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    (hv₀ : principalResidueLabel M v₀ = label)
    (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
    (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
    (pivot : ∀ j, O j ↪ BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1))
    (hpivot : ∀ w j, ((boundedCoefficientJetMatrix (rootAt w) (dirsAt w)
      (j.val + 1) (rows j)).submatrix id (pivot j)).det ≠ 0)
    (hσ1 : ∀ j, σ j ≤ 1)
    (hperiod : ∀ j, integerScalarLattice (O j) (M : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod M))
    {ε : ℝ} (hpoint : ∀ z, |(allocatedLongResidueWeights B U b S M hM label hsize).mean
      (fun w => scale * allocatedLongJetDensity B U b hR hσ S x u w rows s hA hσ1 z) -
        allocatedLongJetProxy B U b S x u rows s hA M residue z| ≤ ε)
    (z : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ))
    (r : ∀ j, O j → Q j → ZMod d) :
    |(allocatedLongResidueWeights B U b S M hM label hsize).mean
      (fun w => canonicalCoveredArrayDensity U (rootAt w) (dirsAt w) rows pivot (hpivot w)
        (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
        (allocatedLayerIntegerPMFs B U b hR hσ S) d (z, r)) -
      allocatedCoveredFixedFactor B U b hR hσ S x u v₀ rows Q d z r *
        (allocatedLongJetProxy B U b S x u rows s hA M residue (fun a => axis z a.val) / scale)| ≤
      allocatedCoveredFixedFactor B U b hR hσ S x u v₀ rows Q d z r * (ε / scale) := by
  let weights := allocatedLongResidueWeights B U b S M hM label hsize
  have hresidue (w) (hw : weights.weight w ≠ 0) :
      principalResidueLabel M w = principalResidueLabel M v₀ :=
    (allocatedLongResidueWeights_support_label B U b S M hM label hsize w hw).trans hv₀.symm
  rw [allocatedPhysicalCoveredDensity_mean B U b hR hσ S x u rows Q d
    weights v₀ s hA pivot hpivot hσ1 M hperiod hresidue z r,
    ← mul_sub, abs_mul, abs_of_nonneg (allocatedCoveredFixedFactor_nonneg B U b hR hσ S x u v₀ rows Q d z r)]
  apply mul_le_mul_of_nonneg_left _ (allocatedCoveredFixedFactor_nonneg B U b hR hσ S x u v₀ rows Q d z r)
  have hscale : 0 < scale := Finset.prod_pos (fun a _ => allocatedLongJetOutputScale_pos B U b S a)
  have he := hpoint (fun a => axis z a.val)
  rw [weights.mean_const_mul] at he
  calc
    _ = |(scale * weights.mean (fun w => allocatedLongJetDensity B U b hR hσ S x u w rows s hA hσ1
        (fun a => axis z a.val)) - allocatedLongJetProxy B U b S x u rows s hA M residue
          (fun a => axis z a.val)) / scale| := by congr 1; field_simp [hscale.ne']
    _ ≤ ε / scale := by
      rw [abs_div, abs_of_pos hscale]
      exact div_le_div_of_nonneg_right he hscale.le

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule Set
open scoped BigOperators Classical

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
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "split" => coefficientJetAxisSplit O I n grid
local notation "scale" => (∏ a, allocatedLongJetOutputScale B U b S (O := O) a)
local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (O := O) (E := Q) U o b d
  (fun j _ => standardLatticeClosedQuarterBox (J j))
local notation "haar" => Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))

theorem allocatedRestrictedCoefficientError_mass_of_box {T η : ℝ}
    (hT : 0 ≤ T) (hη : 0 ≤ η)
    (hbox : ∀ z ∈ region, (split z.1).2 ∈ allocatedLongJetBox B U b S O T) :
    (∫⁻ y, ENNReal.ofReal (restrictedChartDensity chart region 1
      (fun z : MixedCoveredJetSource I O Q n d =>
        allocatedCoveredFixedFactor B U b hR hσ S x u v rows Q d z.1 z.2 * (η / scale)) y) ∂haar) ≤
      ENNReal.ofReal (η * (2 * T + 1) ^ Fintype.card (Σ a : LayerSamplerAxis I n, O a.1)) := by
  let μf := allocatedFrozenJetReference B U b S O
  let μl := allocatedLongJetReference B U b S O
  let μd := (PMF.uniformOfFintype (∀ j, O j → Q j → ZMod d)).toMeasure
  let μraw := (Measure.pi (fun j => mixedArrayReference (I j) (Fin (n j)) (O j))).prod μd
  let box := allocatedLongJetBox B U b S O T
  let fg := allocatedGridJetDensity B U b hR hσ S x u v rows
  let fd : (∀ j, O j → Q j → ZMod d) → ℝ := coefficientDeckJetDensity
    (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v))
    (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)) rows d
  let e := MeasurableEquiv.prodCongr split (MeasurableEquiv.refl (∀ j, O j → Q j → ZMod d))
  let f := fun z : MixedCoveredJetSource I O Q n d => fg ((split z.1).1) * fd z.2 * (η / scale)
  let k := box.indicator (fun _ => η / scale)
  let F := fun z : (AllocatedFrozenJetRows B U b S O × AllocatedLongJetRows B U b S O) ×
      (∀ j, O j → Q j → ZMod d) => fg z.1.1 * k z.1.2 * fd z.2
  have hscale : 0 < scale := Finset.prod_pos (fun a _ => allocatedLongJetOutputScale_pos B U b S a)
  have hfg : Integrable fg μf ∧ (∫ z, fg z ∂μf) = 1 :=
    allocatedGridJetDensity_probability_data B U b S O hR hσ x u v rows
  have hfg0 (z) : 0 ≤ fg z := (allocatedGridJetDensity_mem_Icc B U b hR hσ S x u v rows z).1
  let : IsProbabilityMeasure (realDensityMeasure μd fd) := coefficientDeckJetDensity_probability _ _ rows d
  have hfd := boundedDensity_mass μd fd (measurable_of_finite _) (coefficientDeckJetDensity_nonneg _ _ rows d)
    (coefficientDeckJetDensity_le_card _ _ rows d)
  have hki : Integrable k μl := (integrableOn_const (allocatedLongJetBox_measure_lt_top B U b S O T).ne).integrable_indicator
    (allocatedLongJetBox_measurable B U b S O T)
  have hFi : Integrable F ((μf.prod μl).prod μd) := (hfg.1.mul_prod hki).mul_prod hfd.1
  have hk0 (z) : 0 ≤ k z := Set.indicator_nonneg (fun _ _ => div_nonneg hη hscale.le) z
  have hF0 (z) : 0 ≤ F z := mul_nonneg (mul_nonneg (hfg0 _) (hk0 _))
    (coefficientDeckJetDensity_nonneg _ _ rows d _)
  have hFm : (∫ z, F z ∂(μf.prod μl).prod μd) = (η / scale) * μl.real box := by
    dsimp only [F]
    rw [integral_prod_mul (μ := μf.prod μl) (ν := μd)
      (fun z : AllocatedFrozenJetRows B U b S O × AllocatedLongJetRows B U b S O => fg z.1 * k z.2) fd,
      integral_prod_mul (μ := μf) (ν := μl) fg k, hfg.2, hfd.2, one_mul, mul_one]
    dsimp only [k]
    rw [integral_indicator (allocatedLongJetBox_measurable B U b S O T), setIntegral_const, smul_eq_mul]
    ring
  have hbound : (η / scale) * μl.real box ≤
      η * (2 * T + 1) ^ Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) := by
    calc
      _ ≤ (η / scale) * ((2 * T + 1) ^ Fintype.card (Σ a : LayerSamplerAxis I n, O a.1) * scale) :=
        mul_le_mul_of_nonneg_left (allocatedLongJetBox_measure_bound B U b S O hT) (div_nonneg hη hscale.le)
      _ = _ := by field_simp [hscale.ne']
  have he : MeasurePreserving e μraw ((μf.prod μl).prod μd) :=
    (coefficientJetAxisSplit_measurePreserving O I n grid).prod (MeasurePreserving.id μd)
  have hregion : MeasurableSet region :=
    (coveredJetSourceRegion_measurable U b d _ (fun j _ => (standardLatticeClosedQuarterBox_isCompact (J j)).measurableSet)).preimage
      (mixedCoveredJetCoordinates_measurable (O := O) (B := Q) (n := n) U o d)
  have hident : (fun z : MixedCoveredJetSource I O Q n d =>
      allocatedCoveredFixedFactor B U b hR hσ S x u v rows Q d z.1 z.2 * (η / scale)) =
      (fun z => f z / coveredJetArrayScale (O := O) U) := by
    funext z
    change (fg ((split z.1).1) * fd z.2 / coveredJetArrayScale (O := O) U) * (η / scale) =
      (fg ((split z.1).1) * fd z.2 * (η / scale)) / coveredJetArrayScale (O := O) U
    ring
  rw [hident, mixedCoveredJet_normalized_lintegral U o b hb bW d ν _
    (fun j _ => (standardLatticeClosedQuarterBox_isCompact (J j)).measurableSet)
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))]
  calc
    _ = ∫⁻ z in region, ENNReal.ofReal (F (e z)) ∂μraw := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem hregion] with z hz
      congr 1
      change fg ((split z.1).1) * fd z.2 * (η / scale) = fg ((split z.1).1) * k ((split z.1).2) * fd z.2
      dsimp only [k]
      rw [Set.indicator_of_mem (hbox z hz)]
      ring
    _ ≤ ∫⁻ z, ENNReal.ofReal (F (e z)) ∂μraw := lintegral_mono' Measure.restrict_le_self le_rfl
    _ = ∫⁻ z, ENNReal.ofReal (F z) ∂(μf.prod μl).prod μd :=
      he.lintegral_comp_emb e.measurableEmbedding (fun z => ENNReal.ofReal (F z))
    _ = ENNReal.ofReal ((η / scale) * μl.real box) := by
      rw [← ofReal_integral_eq_lintegral_ofReal hFi (Filter.Eventually.of_forall hF0), hFm]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hbound

theorem allocatedRestrictedCoefficientError_mass (C : Fin m → ℝ)
    (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j w, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) w‖ ≤ C j * ‖w‖)
    {η : ℝ} (hη : 0 ≤ η) :
    (∫⁻ y, ENNReal.ofReal (restrictedChartDensity chart region 1
      (fun z : MixedCoveredJetSource I O Q n d =>
        allocatedCoveredFixedFactor B U b hR hσ S x u v rows Q d z.1 z.2 * (η / scale)) y) ∂haar) ≤
      ENNReal.ofReal (η * (2 * (∑ j, C j * ((Fintype.card (J j) : ℝ) + 1)) + 1) ^
        Fintype.card (Σ a : LayerSamplerAxis I n, O a.1)) := by
  let T := ∑ j, C j * ((Fintype.card (J j) : ℝ) + 1)
  have hT : 0 ≤ T := Finset.sum_nonneg (fun j _ => mul_nonneg (hC j) (by positivity))
  have hCT (j) : C j * ((Fintype.card (J j) : ℝ) + 1) ≤ T :=
    Finset.single_le_sum (f := fun i : Fin m => C i * ((Fintype.card (J i) : ℝ) + 1))
      (fun i _ => mul_nonneg (hC i) (by positivity)) (Finset.mem_univ j)
  exact allocatedRestrictedCoefficientError_mass_of_box B U b S hR hσ x u v rows o hb bW d ν hT hη
    (fun z hz => allocatedChart_long_rows_box B U b S O Q d o hC hT hchart hCT z hz)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators Classical Matrix

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
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "rootAt" => (fun w => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u w))
local notation "dirsAt" => (fun w => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u w))
local notation "axis" => coefficientJetAxisEquiv O I n
local notation "scale" => (∏ a, allocatedLongJetOutputScale B U b S (O := O) a)

noncomputable def allocatedPhysicalKernelPivot
    (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1)) :
    ∀ j, O j ↪ BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) :=
  fun j => (s j).trans (kernelExponentEmbedding G (PrincipalTupleIndex B (layerSamplerDegree I n)) (j.val + 1))

omit [Fintype α] in
theorem allocatedPhysicalKernelPivot_det
    (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
    (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides) (j : Fin m) :
    ((boundedCoefficientJetMatrix (rootAt v) (dirsAt v) (j.val + 1) (rows j)).submatrix
      id (allocatedPhysicalKernelPivot B s j)).det ≠ 0 := by
  rw [allocatedPhysicalKernelPivot, allocatedPhysicalJetMatrix_pivot B U b S x u v rows j]
  exact hA j

variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B α C 1 j)
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable (g : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S) → EuclideanJetLayers U O → ℝ)
variable (hg : ∀ w, Continuous (g w)) (hg0 : ∀ w z, 0 ≤ g w z)
variable (hlaw : ∀ w, (realDensityMeasure μ (fun z => allocatedCoefficientDensity B U b hb o hR hσ S
    (quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d z))).map
    (euclideanCoefficientJetMap U
      (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin (allocatedGridAxis (I := I) U b S.value) u w))
      (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin (allocatedGridAxis (I := I) U b S.value) u w)) rows) =
    realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) (g w))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (O := O) (E := E) U o b d
  (fun j _ => standardLatticeClosedQuarterBox (J j))
local notation "fullPivot" => allocatedPhysicalKernelPivot B s
local notation "fullPivot_det" => allocatedPhysicalKernelPivot_det B U b S x u rows s hA
local notation "rawDensity" => (fun w z => canonicalCoveredArrayDensity U (rootAt w) (dirsAt w) rows fullPivot
  (fullPivot_det w) (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
  (allocatedLayerIntegerPMFs B U b hR hσ S) d z)

include hσ1 hC hchart hsmall hg hg0 hlaw in
theorem allocatedPhysicalDensityFamily_restricted
    (w : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides) :
    g w = restrictedChartDensity chart region 1 (rawDensity w) := by
  have h := allocatedPhysicalCoveredDensity_global B U b hb o hR hσ S (fun _ => 0) x
    (principalAxisJoin grid u w) rows fullPivot (fullPivot_det w) hσ1 C hC hchart
    (H := 1) le_rfl (allocatedPhysicalRootAllowance_zero B U b S).le hsmall bW d μ ν
    (g w) (hg w) (hg0 w) (hlaw w)
  apply restrictedChartDensity_eq_of_values chart region
    (mixedCoveredJetChart_injOn U o b hb bW d _ (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j)))
  · intro z hz
    exact h.1 z (mixedCoveredJetRegion_mono U o b d
      (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j)) hz)
  · intro y hy
    rw [mixedCoveredJetChart_image U o b hb bW d] at hy
    exact h.2 y hy

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]

include hσ1 hC hchart hsmall hg hg0 hlaw in
theorem allocatedPhysicalDensityFamily_residue_comparison
    (M : ℕ) (hM : 0 < M)
    (label : PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
      (fun a => layerSamplerDegree I n a.val) → Option α → ZMod M)
    (hsize : ∀ t, (Fintype.card α + 1) * M ≤ principalAxisLength (fun a => ¬grid a) sides t)
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    (hv₀ : principalResidueLabel M v₀ = label)
    (hperiod : ∀ j, integerScalarLattice (O j) (M : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod M))
    {ε : ℝ} (hpoint : ∀ z, |(allocatedLongResidueWeights B U b S M hM label hsize).mean
      (fun w => scale * allocatedLongJetDensity B U b hR hσ S x u w rows s hA hσ1 z) -
        allocatedLongJetProxy B U b S x u rows s hA M residue z| ≤ ε)
    (y : EuclideanJetLayers U O) :
    |(allocatedLongResidueWeights B U b S M hM label hsize).mean (fun w => g w y) -
      restrictedChartDensity chart region 1 (fun z : MixedCoveredJetSource I O E n d =>
        allocatedCoveredFixedFactor B U b hR hσ S x u v₀ rows E d z.1 z.2 *
          (allocatedLongJetProxy B U b S x u rows s hA M residue (fun a => axis z.1 a.val) / scale)) y| ≤
      restrictedChartDensity chart region 1 (fun z : MixedCoveredJetSource I O E n d =>
        allocatedCoveredFixedFactor B U b hR hσ S x u v₀ rows E d z.1 z.2 * (ε / scale)) y := by
  have hfamily := allocatedPhysicalDensityFamily_restricted B U b hR hσ S x u rows s hA
    hb o hσ1 C hC hchart hsmall bW d μ ν g hg hg0 hlaw
  have hinj := mixedCoveredJetChart_injOn (O := O) U o b hb bW d _
    (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))
  let weights := allocatedLongResidueWeights B U b S M hM label hsize
  apply restrictedChartDensity_mean_comparison chart region hinj weights g
  · intro z hz
    have hv (w) : g w (chart z) = rawDensity w z := by
      rw [hfamily w, restrictedChartDensity_apply chart region 1 _ hinj hz, one_mul]
    have he := weights.mean_congr_on_support (fun w _ => hv w)
    rw [he]
    exact allocatedPhysicalCoveredDensity_residue_comparison B U b hR hσ S x u rows E d
      M hM label hsize v₀ hv₀ s hA fullPivot fullPivot_det hσ1 hperiod residue hpoint z.1 z.2
  · intro w t ht
    rw [hfamily w]
    exact restrictedChartDensity_zero chart region 1 _ ht

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators Classical Matrix

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
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "rootAt" => (fun w => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u w))
local notation "dirsAt" => (fun w => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u w))
local notation "axis" => coefficientJetAxisEquiv O I n
local notation "scale" => (∏ a, allocatedLongJetOutputScale B U b S (O := O) a)

variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B α C 1 j)
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable (g : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S) → EuclideanJetLayers U O → ℝ)
variable (hg : ∀ w, Continuous (g w)) (hg0 : ∀ w z, 0 ≤ g w z)
variable (hlaw : ∀ w, (realDensityMeasure μ (fun z => allocatedCoefficientDensity B U b hb o hR hσ S
    (quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d z))).map
    (euclideanCoefficientJetMap U
      (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin (allocatedGridAxis (I := I) U b S.value) u w))
      (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin (allocatedGridAxis (I := I) U b S.value) u w)) rows) =
    realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) (g w))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (O := O) (E := E) U o b d
  (fun j _ => standardLatticeClosedQuarterBox (J j))
variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]

include hσ1 hC hchart hsmall hg hg0 hlaw in
theorem allocatedPhysicalDensityFamily_refined_comparison
    (M : ℕ) (hM : 0 < M)
    (label : PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
      (fun a => layerSamplerDegree I n a.val) → Option α → ZMod M)
    (hsize : ∀ t, (Fintype.card α + 1) * M ≤ principalAxisLength (fun a => ¬grid a) sides t)
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    (hv₀ : principalResidueLabel M v₀ = label)
    (period : ℕ) (hdiv : period ∣ M)
    (hperiod : ∀ j, integerScalarLattice (O j) (period : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod period))
    (hresidue : ∀ w, (allocatedLongResidueWeights B U b S M hM label hsize).weight w ≠ 0 → ∀ j,
      integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j w) period = residue j)
    {ε : ℝ} (hpoint : ∀ z, |(allocatedLongResidueWeights B U b S M hM label hsize).mean
      (fun w => scale * allocatedLongJetDensity B U b hR hσ S x u w rows s hA hσ1 z) -
        allocatedLongJetProxy B U b S x u rows s hA period residue z| ≤ ε)
    (y : EuclideanJetLayers U O) :
    |(allocatedLongResidueWeights B U b S M hM label hsize).mean (fun w => g w y) -
      restrictedChartDensity chart region 1 (fun z : MixedCoveredJetSource I O E n d =>
        allocatedCoveredFixedFactor B U b hR hσ S x u v₀ rows E d z.1 z.2 *
          (allocatedLongJetProxy B U b S x u rows s hA period residue (fun a => axis z.1 a.val) / scale)) y| ≤
      restrictedChartDensity chart region 1 (fun z : MixedCoveredJetSource I O E n d =>
        allocatedCoveredFixedFactor B U b hR hσ S x u v₀ rows E d z.1 z.2 * (ε / scale)) y := by
  let refinedResidue := fun j => integerResidueMatrix
    (allocatedNonkernelJetMatrix B U b S x u rows j v₀) M
  have hp : ∀ j, integerScalarLattice (O j) (M : ℤ) ≤
      (scalarKernelIntegerJet x (j.val+1) (rows j)).mulVecLin.range :=
    fun j => (integerScalarLattice_nat_refinement (O j) hdiv).trans (hperiod j)
  have href := allocatedLongResidueWeights_reference_matrix B U b S x rows u
    M hM label hsize v₀ hv₀ period hdiv residue hresidue
  have heq := allocatedLongJetProxy_eq_of_periods B U b S x rows u v₀ s hA
    period M residue refinedResidue hperiod hp href (fun _ => rfl)
  have hpoint' : ∀ z, |(allocatedLongResidueWeights B U b S M hM label hsize).mean
      (fun w => scale * allocatedLongJetDensity B U b hR hσ S x u w rows s hA hσ1 z) -
        allocatedLongJetProxy B U b S x u rows s hA M refinedResidue z| ≤ ε := by
    rw [← heq]
    exact hpoint
  have h := allocatedPhysicalDensityFamily_residue_comparison B U b hR hσ S x u rows s hA
    hb o hσ1 C hC hchart hsmall bW d μ ν g hg hg0 hlaw
    M hM label hsize v₀ hv₀ hp refinedResidue hpoint' y
  simpa only [← heq] using h

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {A : Type*} [Fintype A] (p : FiniteProbabilityWeights A)

theorem norm_spatial_density_product_error (w : A → ℂ) (q : ℂ)
    (f : A → ℝ) (g δ C e : ℝ) (hδ : 0 ≤ δ)
    (hw : ∀ a, p.weight a ≠ 0 → ‖w a - q‖ ≤ δ)
    (hf : ∀ a, p.weight a ≠ 0 → |f a| ≤ C)
    (he : |p.mean f - g| ≤ e) :
    ‖p.complexMean (fun a => w a * (f a : ℂ)) - q * (g : ℂ)‖ ≤ δ * C + ‖q‖ * e := by
  have hfirst := p.norm_complexMean_sub_le (fun a => w a * (f a : ℂ))
    (fun a => q * (f a : ℂ)) (fun _ => δ * C) (fun a ha => by
      rw [← sub_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul (hw a ha) (hf a ha) (abs_nonneg _) hδ)
  rw [p.mean_const, p.complexMean_mul_left, p.complexMean_ofReal] at hfirst
  have hsecond : ‖q * (p.mean f : ℂ) - q * (g : ℂ)‖ ≤ ‖q‖ * e := by
    rw [← mul_sub, ← Complex.ofReal_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left he (norm_nonneg _)
  exact (norm_sub_le_norm_sub_add_norm_sub _ (q * (p.mean f : ℂ)) _).trans
    (add_le_add hfirst hsecond)

theorem norm_spatial_density_sum_error {V : Type*} [Fintype V]
    (w : A → V → ℂ) (q : V → ℂ) (f : A → V → ℝ) (g : V → ℝ)
    (test : V → ℂ) (δ C e : V → ℝ) (hδ : ∀ v, 0 ≤ δ v)
    (htest : ∀ v, ‖test v‖ ≤ 1)
    (hw : ∀ a, p.weight a ≠ 0 → ∀ v, ‖w a v - q v‖ ≤ δ v)
    (hf : ∀ a, p.weight a ≠ 0 → ∀ v, |f a v| ≤ C v)
    (he : ∀ v, |p.mean (fun a => f a v) - g v| ≤ e v) :
    ‖p.complexMean (fun a => ∑ v, test v * (w a v * (f a v : ℂ))) -
      ∑ v, test v * (q v * (g v : ℂ))‖ ≤ ∑ v, (δ v * C v + ‖q v‖ * e v) := by
  rw [p.complexMean_sum]
  simp_rw [p.complexMean_mul_left]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro v _
  rw [norm_mul]
  have hstep := p.norm_spatial_density_product_error
    (fun a => w a v) (q v) (fun a => f a v) (g v) (δ v) (C v) (e v) (hδ v)
    (fun a ha => hw a ha v) (fun a ha => hf a ha v) (he v)
  exact (mul_le_mul_of_nonneg_right (htest v) (norm_nonneg _)).trans
    (by simpa only [one_mul] using hstep)

theorem norm_spatial_density_sum_error_normalized {V : Type*} [Fintype V]
    (w : A → V → ℂ) (q : V → ℂ) (f : A → V → ℝ) (g : V → ℝ)
    (test : V → ℂ) (δ C e : V → ℝ) (hδ : ∀ v, 0 ≤ δ v)
    (htest : ∀ v, ‖test v‖ ≤ 1)
    (hw : ∀ a, p.weight a ≠ 0 → ∀ v, ‖w a v - q v‖ ≤ δ v)
    (hf : ∀ a, p.weight a ≠ 0 → ∀ v, |f a v| ≤ C v)
    (he : ∀ v, |p.mean (fun a => f a v) - g v| ≤ e v)
    {Z : ℝ} (hZ : 0 < Z) :
    ‖p.complexMean (fun a => ∑ v, test v * (w a v * (f a v : ℂ))) / (Z : ℂ) -
      (∑ v, test v * (q v * (g v : ℂ))) / (Z : ℂ)‖ ≤
        (∑ v, (δ v * C v + ‖q v‖ * e v)) / Z := by
  rw [← sub_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZ]
  exact div_le_div_of_nonneg_right
    (p.norm_spatial_density_sum_error w q f g test δ C e hδ htest hw hf he) hZ.le

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators Classical Matrix

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
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "rootAt" => (fun w => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u w))
local notation "dirsAt" => (fun w => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u w))
local notation "axis" => coefficientJetAxisEquiv O I n
local notation "scale" => (∏ a, allocatedLongJetOutputScale B U b S (O := O) a)

variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B α C 1 j)
variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable (g : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S) → EuclideanJetLayers U O → ℝ)
variable (hg : ∀ w, Continuous (g w)) (hg0 : ∀ w z, 0 ≤ g w z)
variable (hlaw : ∀ w, (realDensityMeasure μ (fun z => allocatedCoefficientDensity B U b hb o hR hσ S
    (quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d z))).map
    (euclideanCoefficientJetMap U
      (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin (allocatedGridAxis (I := I) U b S.value) u w))
      (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin (allocatedGridAxis (I := I) U b S.value) u w)) rows) =
    realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) (g w))

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (O := O) (E := E) U o b d
  (fun j _ => standardLatticeClosedQuarterBox (J j))
variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]

open BooleanCubeKernel
variable [DecidableEq G]
local notation "vars" => LayerSamplerVariables G I n B
local notation "ker" => (fun a => (0 : ℤ) + (x a none : ℤ))

include hσ1 hC hchart hsmall hg hg0 hlaw in
theorem allocatedOriginal_refined_density_comparison
    (M : ℕ) (hM : 0 < M)
    (label : PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
      (fun a => layerSamplerDegree I n a.val) → Option α → ZMod M)
    (hsize : ∀ t, (Fintype.card α+1)*M ≤ principalAxisLength (fun a => ¬grid a) sides t)
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    (hv₀ : principalResidueLabel M v₀ = label)
    (period : ℕ) [NeZero period] (hdiv : period ∣ M)
    (hperiod : ∀ j, integerScalarLattice (O j) (period : ℤ) ≤
      (scalarKernelIntegerJet x (j.val+1) (rows j)).mulVecLin.range)
    (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod period))
    (hresidue : ∀ w, (allocatedLongResidueWeights B U b S M hM label hsize).weight w ≠ 0 → ∀ j,
      integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j w) period = residue j)
    {ε : ℝ} (hpoint : ∀ z, |(allocatedLongResidueWeights B U b S M hM label hsize).mean
      (fun w => scale * allocatedLongJetDensity B U b hR hσ S x u w rows s hA hσ1 z) -
        allocatedLongJetProxy B U b S x u rows s hA period residue z| ≤ ε)
    (selection : α ↪ G) {K : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (hx : GoodScalarKernelTuple selection κ K x)
    {X : Type*} [Fintype X] (N q : X → ℕ) (hN : ∀ t, 0 < N t) (hq : ∀ t, 0 < q t)
    {W τ C₀ ρ ξ δ mesh : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hρ : 0 < ρ)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hC₀ : 1 ≤ C₀) (hLC : (S.value : ℝ) ≤ C₀) (hWC : W ≤ C₀)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1)
    (hphysicalSize : ∀ t, 8*(1+W)*(q t : ℝ)*ρ ≤ (ξ*τ)*(N t : ℝ))
    (hmeshSize : anisotropicSpatialMeshThreshold selection (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ)
    (hρ8 : 8*(probabilityProfileLipschitz : ℝ) ≤ ρ)
    (hspatialPeriod : integerScalarLattice (Unit ⊕ α) (period : ℤ) ≤
      pivotFullImage (selectedSpatialPivot ker (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns ker (scalarCubeDifferenceMatrix x) selection))
    (hstride : ∀ t, q t * period ∣ M) (hδ : 0 ≤ δ)
    (hρshift : 2 * (Fintype.card (Option vars) *
      (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ)
    (hρmove : Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) *
      (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0)) ≤ δ*ρ)
    (hmesh : 0 < mesh) (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option vars) X q))
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
    (point : (X → (Unit ⊕ α) → ℤ) → EuclideanJetLayers U O)
    (test : (X → (Unit ⊕ α) → ℤ) → ℂ) (htest : ∀ v, ‖test v‖ ≤ 1)
    {Cg Z : ℝ} (hCg : 0 ≤ Cg) (hZ : 0 < Z)
    (hcap : ∀ w, (allocatedLongResidueWeights B U b S M hM label hsize).weight w ≠ 0 →
      ∀ v, g w (point v) ≤ Cg) :
    let H := trimmedSpatialRootScale τ N q
    let T := trimmedSpatialSlopeScale W τ N q
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let hV := narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
    let hp := goodScalarKernelTuple_spatial_det_ne_zero selection x ker hκ hx
    let f := canonicalSpatialSiteDensity selection ker (scalarCubeDifferenceMatrix x) hp W S.value
      hW (Nat.cast_pos.mpr S.positive)
    let ψ := fun v : X → (Unit ⊕ α) → ℤ => ∏ t,
      spatialSiteApprox (selectedSpatialPivot ker (scalarCubeDifferenceMatrix x) selection)
        (Matrix.fromCols (selectedSpatialFreeColumns ker (scalarCubeDifferenceMatrix x) selection)
          (liftResidueMatrix (integerResidueMatrix
            (principalSpatialColumns (fun _ => (0 : ℤ)) id (principalAxisJoin grid u v₀)) period)))
        period f (H t) 4 mesh (v t)
    let A := ∏ t, ∏ i, physicalSpatialOutputScale α (H t) (T t) S.value i
    let E₀ := anisotropicSpatialError selection (PrincipalTupleIndex B (layerSamplerDegree I n)) K κ C₀ ρ ξ
    let Γ := (period : ℝ)^Fintype.card (Unit ⊕ α)
    let E₁ := E₀ + Γ*(anisotropicSpatialDensityLip selection κ*(1+W))*δ
    let Esite := Fintype.card X*(E₁ + 4*Γ*(anisotropicSpatialDensityLip selection κ*(1+W))*mesh)*
      (1 + Γ*anisotropicSpatialDensityCap selection κ + E₁)^Fintype.card X
    let window := spatialWindow H 4
    let F := fun a : cells => physicalResidueReconstruction (rootAt v₀) (dirsAt v₀) base
      (boundedColumnResidueRepresentative q a.val) q
    let spatialBudget := fun w : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides =>
      Cg*(24*(probabilityProfileLipschitz : ℝ)*Fintype.card (Option vars × X)/ρ)/Z +
        (∑ a : cells, selectedResidueCellWeight q cells V a *
          ((Esite/A) * ∑ v ∈ window, ‖test (F a v)‖ * g w (point (F a v)))) / Z
    let factor := fun t : cells × window =>
      (selectedResidueCellWeight q cells V t.1 : ℂ) * (ψ t.2.val / (A : ℂ)) * test (F t.1 t.2.val)
    let proxy := restrictedChartDensity chart region 1 (fun z : MixedCoveredJetSource I O E n d =>
      allocatedCoveredFixedFactor B U b hR hσ S x u v₀ rows E d z.1 z.2 *
        (allocatedLongJetProxy B U b S x u rows s hA period residue (fun a => axis z.1 a.val) / scale))
    let error := restrictedChartDensity chart region 1 (fun z : MixedCoveredJetSource I O E n d =>
      allocatedCoveredFixedFactor B U b hR hσ S x u v₀ rows E d z.1 z.2 * (ε/scale))
    let source := fun w : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides =>
      ∑' z, ((selectedResidueSmoothPMF q cells V hV hmass z).toReal : ℂ) *
        (test (physicalCubeRootDifferences (rootAt w) (dirsAt w) base z) *
          (g w (point (physicalCubeRootDifferences (rootAt w) (dirsAt w) base z)) : ℂ))
    ‖(allocatedLongResidueWeights B U b S M hM label hsize).complexMean source / (Z : ℂ) -
      (∑ t : cells × window, factor t * (proxy (point (F t.1 t.2.val)) : ℂ)) / (Z : ℂ)‖ ≤
      (allocatedLongResidueWeights B U b S M hM label hsize).mean spatialBudget +
        (∑ t : cells × window, ‖factor t‖ * error (point (F t.1 t.2.val))) / Z := by
  intro H T V hV hp f ψ A E₀ Γ E₁ Esite window F spatialBudget factor proxy error source
  let weights := allocatedLongResidueWeights B U b S M hM label hsize
  have hfirst (w) (hw : weights.weight w ≠ 0) :
      ‖source w / (Z : ℂ) -
        (∑ t : cells × window, factor t * (g w (point (F t.1 t.2.val)) : ℂ)) / (Z : ℂ)‖ ≤
      spatialBudget w := by
    have hφ (v) : ‖test v * (g w (point v) : ℂ)‖ ≤ Cg := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg0 w (point v))]
      exact (mul_le_mul_of_nonneg_right (htest v) (hg0 w (point v))).trans
        (by simpa only [one_mul] using hcap w hw v)
    have hl := (allocatedLongResidueWeights_support_label B U b S M hM label hsize w hw).trans hv₀.symm
    have h := allocatedNarrowTrimmed_reference_mass_test B U b S (fun _ => 0) x u w v₀
      selection N q hN hq hW hτ hκ hρ hx hbudget hC₀ hLC hWC hξ hξ1
      hphysicalSize hmeshSize hρ8 period hspatialPeriod M hstride hl hδ hρshift hρmove hmesh base cells hmass
      (fun v => test v * (g w (point v) : ℂ)) hCg hφ hZ
    have hsum : (∑ t : cells × window, factor t * (g w (point (F t.1 t.2.val)) : ℂ)) =
        ∑ a : cells, (selectedResidueCellWeight q cells V a : ℂ) *
          ∑ v ∈ window, (ψ v / (A : ℂ)) * (test (F a v) * (g w (point (F a v)) : ℂ)) := by
      simp only [factor, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_coe_sort window (fun v => (selectedResidueCellWeight q cells V a : ℂ) *
        (ψ v / (A : ℂ) * (test (F a v) * (g w (point (F a v)) : ℂ))))
    have hn (v) : ‖test v * (g w (point v) : ℂ)‖ = ‖test v‖ * g w (point v) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hg0 w (point v))]
    simp_rw [hn] at h
    rw [hsum]
    exact h
  apply weights.norm_reference_density_variable_error_normalized source factor
    (fun w t => g w (point (F t.1 t.2.val)))
    (fun t => proxy (point (F t.1 t.2.val))) (fun t => error (point (F t.1 t.2.val))) spatialBudget hZ hfirst
  intro t
  exact allocatedPhysicalDensityFamily_refined_comparison B U b hR hσ S x u rows s hA
    hb o hσ1 C hC hchart hsmall bW d μ ν g hg hg0 hlaw
    M hM label hsize v₀ hv₀ period hdiv hperiod residue hresidue hpoint (point (F t.1 t.2.val))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory BooleanCubeKernel
open scoped BigOperators Matrix NNReal

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j : Fin m, DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [∀ j : Fin m, DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]
variable (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "lengths" => principalAxisLength (fun a => ¬grid a) sides

variable (X : Type*) [Fintype X]

theorem allocatedGoodKernel_prescribed_refined_density {M : ℕ} (hM : 0 < M)
    (selection : α ↪ G) (hx : GoodScalarKernelTuple selection (1/(M : ℝ)) M x)
    (hq : Fintype.card α ≤ m+1) (hinj : ∀ j, Function.Injective (rows j))
    (hrows : ∀ j o, (rows j o).card ≤ j.val+1) (hσ1 : ∀ j, σ j ≤ 1)
    {P E T η : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) (hT : 0 ≤ T) (hη : 0 < η) (hη1 : η ≤ 1)
    (hMP : (M : ℝ) ≤ Real.exp P) (hRP : ∀ j, R j ≤ Real.exp P)
    (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp P) (hσi : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) : ℝ)+1 ≤ Real.exp P)
    (hηE : η⁻¹ ≤ Real.exp E)
    (hlarge : Real.exp (allocatedRefinedJointLengthLog (G := G) B α O P E
      ((m+1 : ℕ)*P + Fintype.card X*T)) ≤ S.value) :
    ∃ (modulus : ℕ) (hm : 0 < modulus),
      let : NeZero modulus := ⟨hm.ne'⟩
      modulus ≤ M^(m+1) ∧
      (∀ root : G → ℤ, integerScalarLattice (Unit ⊕ α) (modulus : ℤ) ≤
        pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) selection)
          (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) selection)) ∧
      (∀ j, integerScalarLattice (O j) (modulus : ℤ) ≤
        (scalarKernelIntegerJet x (j.val+1) (rows j)).mulVecLin.range) ∧
      ∃ (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val+1))
        (hA : ∀ j, ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id (s j)).det ≠ 0),
      (∀ j : Fin m, fixedKernelInverseBound S.positive x (j.val+1) (rows j) (s j) (hA j) (1/(M : ℝ))) ∧
      ∀ (q : X → ℕ), (∀ d, 0 < q d) → (∀ d, (q d : ℝ) ≤ Real.exp T) →
      let refined := residueRefinedPeriod modulus q
      ∃ hRefined : 0 < refined,
      (∀ d, q d * modulus ∣ refined) ∧
      (refined : ℝ) ≤ Real.exp ((m+1 : ℕ)*P + Fintype.card X*T) ∧
      ∃ hsize : ∀ d, (Fintype.card α+1)*refined ≤ lengths d,
      ∀ (u : PrincipalAxisTuples (α := α) grid sides)
        (r : PrincipalTupleIndex (fun a : {a // ¬grid a} => B a.val)
          (fun a => layerSamplerDegree I n a.val) → Option α → ZMod refined),
      ∃ (reference : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
        (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)),
        principalResidueLabel refined reference = r ∧
        (∀ v, (allocatedLongResidueWeights B U b S refined hRefined r hsize).weight v ≠ 0 → ∀ j,
          integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x u rows j v) modulus = residue j) ∧
        ∀ [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
        [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
        [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
        [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
        (hb : ∀ j, Submodule.span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
        (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
        (C : Fin m → ℝ) (_hC : ∀ j, 0 ≤ C j)
        (_hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
        (_hsmall : ∀ j, R j ≤ allocatedPhysicalChartRadius (G := G) B α C 1 j)
        {Kcov : Fin m → Type*} [∀ j, Fintype (Kcov j)]
        (bW : ∀ j, Module.Basis (Kcov j) ℤ
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
        (d : ℕ) [NeZero d]
        (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
        [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
        (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
        [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
        (g : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides → EuclideanJetLayers U O → ℝ)
        (_hg : ∀ w, Continuous (g w)) (_hg0 : ∀ w z, 0 ≤ g w z)
        (_hlaw : ∀ w, (realDensityMeasure μ (fun z => allocatedCoefficientDensity B U b hb o hR hσ S
          (quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d z))).map
          (euclideanCoefficientJetMap U
            (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u w))
            (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u w)) rows) =
          realDensityMeasure (Measure.pi (fun j => Measure.pi (fun _ : O j => ν j))) (g w))
        (N : X → ℕ) (hN : ∀ t, 0 < N t)
    {W τ C₀ ρ ξ δ mesh : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (_hρ : 0 < ρ)
    (_hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (_hC₀ : 1 ≤ C₀) (_hLC : (S.value : ℝ) ≤ C₀) (_hWC : W ≤ C₀)
    (hξ : 0 < ξ) (_hξ1 : ξ ≤ 1)
    (_hphysicalSize : ∀ t, 8*(1+W)*(q t : ℝ)*ρ ≤ (ξ*τ)*(N t : ℝ))
    (_hmeshSize : anisotropicSpatialMeshThreshold selection (PrincipalTupleIndex B (layerSamplerDegree I n)) C₀ ≤ ρ)
    (_hρ8 : 8*(probabilityProfileLipschitz : ℝ) ≤ ρ)
    (_hδ : 0 ≤ δ)
    (_hρshift : 2 * (Fintype.card (Option (LayerSamplerVariables G I n B)) *
      (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0))) ≤ ρ)
    (_hρmove : Fintype.card (PrincipalTupleIndex B (layerSamplerDegree I n)) *
      (2 * allocatedPhysicalEntryBudget B U b S (fun _ => 0)) ≤ δ*ρ)
    (_hmesh : 0 < mesh) (base : X → ℤ)
    (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X q))
    (hmass : 0 < ∑' z, selectedResidueSmoothWeight q cells (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
    (point : (X → (Unit ⊕ α) → ℤ) → EuclideanJetLayers U O)
    (test : (X → (Unit ⊕ α) → ℤ) → ℂ) (_htest : ∀ v, ‖test v‖ ≤ 1)
    {Cg Z : ℝ} (_hCg : 0 ≤ Cg) (_hZ : 0 < Z)
    (_hcap : ∀ w, (allocatedLongResidueWeights B U b S refined hRefined r hsize).weight w ≠ 0 →
      ∀ v, g w (point v) ≤ Cg),
    let coefficientScale := ∏ a, allocatedLongJetOutputScale B U b S (O := O) a
    let chart := mixedCoveredJetChart U o b hb bW d
    let region := mixedCoveredJetRegion (O := O) (E := Kcov) U o b d
      (fun j _ => standardLatticeClosedQuarterBox (J j))
    let H := trimmedSpatialRootScale τ N q
    let T := trimmedSpatialSlopeScale W τ N q
    let V := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    let hV := narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
    let hp := goodScalarKernelTuple_spatial_det_ne_zero selection x (fun a => (0 : ℤ) + (x a none : ℤ))
      (one_div_pos.mpr (Nat.cast_pos.mpr hM)) hx
    let f := canonicalSpatialSiteDensity selection (fun a => (0 : ℤ) + (x a none : ℤ)) (scalarCubeDifferenceMatrix x) hp W S.value
      hW (Nat.cast_pos.mpr S.positive)
    let ψ := fun v : X → (Unit ⊕ α) → ℤ => ∏ t,
      spatialSiteApprox (selectedSpatialPivot (fun a => (0 : ℤ) + (x a none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
        (Matrix.fromCols (selectedSpatialFreeColumns (fun a => (0 : ℤ) + (x a none : ℤ)) (scalarCubeDifferenceMatrix x) selection)
          (liftResidueMatrix (integerResidueMatrix
            (principalSpatialColumns (fun _ => (0 : ℤ)) id (principalAxisJoin grid u reference)) modulus)))
        modulus f (H t) 4 mesh (v t)
    let A := ∏ t, ∏ i, physicalSpatialOutputScale α (H t) (T t) S.value i
    let E₀ := anisotropicSpatialError selection (PrincipalTupleIndex B (layerSamplerDegree I n)) M (1/(M : ℝ)) C₀ ρ ξ
    let Γ := (modulus : ℝ)^Fintype.card (Unit ⊕ α)
    let E₁ := E₀ + Γ*(anisotropicSpatialDensityLip selection (1/(M : ℝ))*(1+W))*δ
    let Esite := Fintype.card X*(E₁ + 4*Γ*(anisotropicSpatialDensityLip selection (1/(M : ℝ))*(1+W))*mesh)*
      (1 + Γ*anisotropicSpatialDensityCap selection (1/(M : ℝ)) + E₁)^Fintype.card X
    let window := spatialWindow H 4
    let F := fun a : cells => physicalResidueReconstruction (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u reference)) (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u reference)) base
      (boundedColumnResidueRepresentative q a.val) q
    let spatialBudget := fun w : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides =>
      Cg*(24*(probabilityProfileLipschitz : ℝ)*Fintype.card (Option (LayerSamplerVariables G I n B) × X)/ρ)/Z +
        (∑ a : cells, selectedResidueCellWeight q cells V a *
          ((Esite/A) * ∑ v ∈ window, ‖test (F a v)‖ * g w (point (F a v)))) / Z
    let factor := fun t : cells × window =>
      (selectedResidueCellWeight q cells V t.1 : ℂ) * (ψ t.2.val / (A : ℂ)) * test (F t.1 t.2.val)
    let proxy := restrictedChartDensity chart region 1 (fun z : MixedCoveredJetSource I O Kcov n d =>
      allocatedCoveredFixedFactor B U b hR hσ S x u reference rows Kcov d z.1 z.2 *
        (allocatedLongJetProxy B U b S x u rows s hA modulus residue (fun a => coefficientJetAxisEquiv O I n z.1 a.val) / coefficientScale))
    let error := restrictedChartDensity chart region 1 (fun z : MixedCoveredJetSource I O Kcov n d =>
      allocatedCoveredFixedFactor B U b hR hσ S x u reference rows Kcov d z.1 z.2 * (η/coefficientScale))
    let source := fun w : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides =>
      ∑' z, ((selectedResidueSmoothPMF q cells V hV hmass z).toReal : ℂ) *
        (test (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u w)) (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u w)) base z) *
          (g w (point (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u w)) (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u w)) base z)) : ℂ))
    ‖(allocatedLongResidueWeights B U b S refined hRefined r hsize).complexMean source / (Z : ℂ) -
      (∑ t : cells × window, factor t * (proxy (point (F t.1 t.2.val)) : ℂ)) / (Z : ℂ)‖ ≤
      (allocatedLongResidueWeights B U b S refined hRefined r hsize).mean spatialBudget +
        (∑ t : cells × window, ‖factor t‖ * error (point (F t.1 t.2.val))) / Z := by
  obtain ⟨modulus, hm, hmod, hspatial, hperiod, s, hA, hi, hstrideData⟩ :=
    allocatedGoodKernel_stride_refined_spatial_data B U b hR hσ S x rows X
      hM selection hx hq hinj hrows hσ1 hP hE hT hη hη1 hMP hRP hRi hσi hcount hηE hlarge
  let : NeZero modulus := ⟨hm.ne'⟩
  refine ⟨modulus, hm, hmod, hspatial, hperiod, s, hA, hi, ?_⟩
  intro q hqpos hqbound
  obtain ⟨hRefined, hstride, hbound, hsize, hdata⟩ := hstrideData q hqpos hqbound
  refine ⟨hRefined, hstride, hbound, hsize, ?_⟩
  intro u r
  obtain ⟨reference, residue, href, hresidue, hpoint⟩ := hdata u r
  refine ⟨reference, residue, href, hresidue, ?_⟩
  intro _ _ _ _ hb o C hC hchart hsmall Kcov _ bW d _ μ _ _ ν _ _ g hg hg0 hlaw
    N hN W τ C₀ ρ ξ δ mesh hW hτ hρ hbudget hC₀ hLC hWC hξ hξ1
    hphysicalSize hmeshSize hρ8 hδ hρshift hρmove hmesh base cells hmass point test htest Cg Z hCg hZ hcap
  have hdiv : modulus ∣ residueRefinedPeriod modulus q := ⟨∏ t, q t, rfl⟩
  exact allocatedOriginal_refined_density_comparison B U b hR hσ S x u rows s hA
    hb o hσ1 C hC hchart hsmall bW d μ ν g hg hg0 hlaw
    (residueRefinedPeriod modulus q) hRefined r hsize reference href modulus hdiv hperiod residue hresidue hpoint
    selection (one_div_pos.mpr (Nat.cast_pos.mpr hM)) hx N q hN hqpos
    hW hτ hρ hbudget hC₀ hLC hWC hξ hξ1 hphysicalSize hmeshSize hρ8
    (hspatial _) hstride hδ hρshift hρmove hmesh base cells hmass point test htest hCg hZ hcap

end Erdos3.VectorPolynomial

end

end OAI
