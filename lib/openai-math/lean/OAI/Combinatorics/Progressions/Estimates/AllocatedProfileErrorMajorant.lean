import OAI.Combinatorics.Progressions.Estimates.AllocatedCoveredSiteExpansion

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "output" => (Σ a : {a // ¬grid a}, O (Sigma.fst (Subtype.val a)))
local notation "scale" => (∏ a, allocatedLongJetOutputScale B U b S (O := O) a)

variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value) (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a) (allocatedPrincipalSides B U b S))
variable (rows : ∀ j, O j → Finset α)

local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)

noncomputable def allocatedProfileMajorantRawDensity (A : ℝ≥0) (f g : (output → ℝ) → ℝ)
    (z : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) : ℝ :=
  allocatedGridJetDensity B U b hR hσ S x u v rows (fun a => coefficientJetAxisEquiv O I n z a.val) *
    ((A : ℝ) * |f (allocatedLongJetRealCoordinates B U b S (fun a => coefficientJetAxisEquiv O I n z a.val)) -
      g (allocatedLongJetRealCoordinates B U b S (fun a => coefficientJetAxisEquiv O I n z a.val))| / scale) *
    smallBoxCutoff (mixedJetAmbientPoint U b o z)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

theorem allocatedProfileErrorAmbientKernel_point (A : ℝ≥0) (f g : (output → ℝ) → ℝ)
    (z : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) :
    allocatedProfileErrorAmbientKernel B U b S o hR hσ x u v rows A f g (mixedJetAmbientPoint U b o z) =
      allocatedProfileMajorantRawDensity B U b S o hR hσ x u v rows A f g z /
        coveredJetArrayScale (O := O) U := by
  rw [allocatedProfileErrorAmbientKernel, allocatedErrorAmbientKernel_mixed_point,
    allocatedLongAmbientCoordinates_point]
  unfold allocatedMajorantRawDensity allocatedProfileMajorantRawDensity
  simp only [NNReal.coe_one, one_mul]
  ring

variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable {Q : Fin m → Type*} [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]

local notation "chart" => mixedCoveredJetChart U o b hb bW d
local notation "region" => mixedCoveredJetRegion (O := O) (E := Q) U o b d
  (fun j _ => standardLatticeSmallBox (J j))
local notation "quarter" => mixedCoveredJetRegion (O := O) (E := Q) U o b d
  (fun j _ => standardLatticeClosedQuarterBox (J j))

theorem allocatedProfileErrorMajorant_chart (A : ℝ≥0) (f g : (output → ℝ) → ℝ) :
    allocatedProfileErrorMajorant B U b S o hR hσ x u v rows A f g d =
      restrictedChartDensity chart region 1 (fun z =>
        allocatedProfileMajorantRawDensity B U b S o hR hσ x u v rows A f g z.1 /
          coveredJetArrayScale (O := O) U) := by
  apply restrictedChartDensity_eq_of_values chart region
    (mixedCoveredJetChart_injOn U o b hb bW d _ (fun _ _ => Subset.rfl))
  · intro z hz
    change allocatedProfileErrorTorusKernel B U b S o hR hσ x u v rows A f g
      (coveredJetAmbientTorus U d (chart z)) = _
    rw [coveredJetAmbientTorus_chart, allocatedProfileErrorTorusKernel,
      smallBoxTorusKernel_local _ (allocatedProfileErrorAmbientKernel_support B U b S o hR hσ x u v rows A f g)]
    · exact allocatedProfileErrorAmbientKernel_point B U b S o hR hσ x u v rows A f g z.1
    · intro a
      exact (hz a.1 (mem_univ _) a.2.1 (mem_univ _)).1 a.2.2
  · intro y hy
    by_contra h
    obtain ⟨z, hz, hzn⟩ := smallBoxTorusKernel_recover
      (allocatedProfileErrorAmbientKernel B U b S o hR hσ x u v rows A f g)
      (coveredJetAmbientTorus U d y) h
    exact hy (coveredJetAmbientTorus_smallBox_mem_chart U b hb o bW d y z hz
      (allocatedProfileErrorAmbientKernel_support B U b S o hR hσ x u v rows A f g z hzn))

include hb bW in
theorem allocatedProfileErrorMajorant_nonneg (A : ℝ≥0) (f g : (output → ℝ) → ℝ)
    (y : EuclideanJetLayers U O) :
    0 ≤ allocatedProfileErrorMajorant B U b S o hR hσ x u v rows A f g d y := by
  rw [allocatedProfileErrorMajorant_chart B U b S o hR hσ x u v rows hb bW d]
  by_cases hy : y ∈ chart '' region
  · obtain ⟨z, hz, rfl⟩ := hy
    rw [restrictedChartDensity_apply _ _ _ _
      (mixedCoveredJetChart_injOn U o b hb bW d _ (fun _ _ => Subset.rfl)) hz, one_mul]
    apply div_nonneg _ (coveredJetArrayScale_pos U).le
    unfold allocatedProfileMajorantRawDensity
    exact mul_nonneg (mul_nonneg (allocatedGridJetDensity_mem_Icc B U b hR hσ S x u v rows _).1
      (div_nonneg (mul_nonneg A.coe_nonneg (abs_nonneg _))
        (Finset.prod_nonneg (fun a _ => (allocatedLongJetOutputScale_pos B U b S a).le))))
      (smallBoxCutoff_range _).1
  · rw [restrictedChartDensity_zero _ _ _ _ hy]

theorem allocatedProfileDifference_le_majorant
    (modulus : ℕ)
    (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (A : ℝ≥0)
    (hA : ∀ (z : AllocatedLongJetRows B U b S O) (r : ∀ j, O j → Q j → ZMod d),
      |∏ a, allocatedLongJetMask B U b S x rows modulus residue a (z a)| *
        coefficientDeckJetDensity root dirs rows d r ≤ A)
    (f g : (output → ℝ) → ℝ) (y : EuclideanJetLayers U O) :
    |allocatedCoveredProfileDensity B U b hR hσ S x u v rows hb o bW d
        (fun j _ => standardLatticeClosedQuarterBox (J j))
        (allocatedLongProfileDensity B U b S x rows modulus residue f) y -
      allocatedCoveredProfileDensity B U b hR hσ S x u v rows hb o bW d
        (fun j _ => standardLatticeClosedQuarterBox (J j))
        (allocatedLongProfileDensity B U b S x rows modulus residue g) y| ≤
      allocatedProfileErrorMajorant B U b S o hR hσ x u v rows A f g d y := by
  by_cases hy : y ∈ chart '' quarter
  · obtain ⟨z, hz, rfl⟩ := hy
    have hquarter : ∀ a, |mixedJetAmbientPoint U b o z.1 a| ≤ 1 / 4 := by
      intro a
      exact (hz a.1 (mem_univ _) a.2.1 (mem_univ _)).1 a.2.2
    have hinj := mixedCoveredJetChart_injOn (O := O) U o b hb bW d
      (fun j _ => standardLatticeClosedQuarterBox (J j))
      (fun j _ => standardLatticeClosedQuarterBox_subset_smallBox (J j))
    simp only [allocatedCoveredProfileDensity, restrictedChartDensity_apply _ _ 1 _ hinj hz, one_mul]
    change _ ≤ allocatedProfileErrorTorusKernel B U b S o hR hσ x u v rows A f g
      (coveredJetAmbientTorus U d (chart z))
    rw [coveredJetAmbientTorus_chart, allocatedProfileErrorTorusKernel,
      smallBoxTorusKernel_local _ (allocatedProfileErrorAmbientKernel_support B U b S o hR hσ x u v rows A f g)
        _ (fun a => lt_of_le_of_lt (hquarter a) (by norm_num)),
      allocatedProfileErrorAmbientKernel_point, allocatedProfileMajorantRawDensity,
      smallBoxCutoff_one _ hquarter, mul_one]
    have hs : 0 < scale := Finset.prod_pos (fun a _ => allocatedLongJetOutputScale_pos B U b S a)
    have hc := coveredJetArrayScale_pos (O := O) U
    have hfac := allocatedCoveredFixedFactor_nonneg B U b hR hσ S x u v rows Q d z.1 z.2
    unfold allocatedLongProfileDensity
    rw [← mul_sub, ← sub_div, ← mul_sub, abs_mul, abs_div, abs_mul,
      abs_of_nonneg hfac, abs_of_pos hs]
    calc
      _ = allocatedGridJetDensity B U b hR hσ S x u v rows
            (fun a => coefficientJetAxisEquiv O I n z.1 a.val) *
          ((|∏ a, allocatedLongJetMask B U b S x rows modulus residue a
              (coefficientJetAxisEquiv O I n z.1 a.val)| * coefficientDeckJetDensity root dirs rows d z.2) *
            |f (allocatedLongJetRealCoordinates B U b S (fun a => coefficientJetAxisEquiv O I n z.1 a.val)) -
              g (allocatedLongJetRealCoordinates B U b S (fun a => coefficientJetAxisEquiv O I n z.1 a.val))| / scale) /
          coveredJetArrayScale (O := O) U := by
        unfold allocatedCoveredFixedFactor
        rw [show ((coefficientJetAxisSplit O I n grid) z.1).2 =
          (fun a : {a // ¬grid a} => coefficientJetAxisEquiv O I n z.1 a.val) from rfl]
        ring
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hA _ _) (abs_nonneg _)) hs.le)
          (allocatedGridJetDensity_mem_Icc B U b hR hσ S x u v rows _).1) hc.le
  · simp only [allocatedCoveredProfileDensity, restrictedChartDensity_zero _ _ 1 _ hy, sub_self, abs_zero]
    exact allocatedProfileErrorMajorant_nonneg B U b S o hR hσ x u v rows hb bW d A f g y

theorem allocatedProfileDifference_le_period_majorant
    (period : ℕ) [NeZero period]
    (hperiod : ∀ j, integerScalarLattice (O j) (period : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (modulus : ℕ)
    (residue : ∀ j, Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (C : ℝ≥0) (hC : 1 ≤ (C : ℝ))
    (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x rows j modulus (residue j) z ∧
      allocatedIntegerKernelMask B U b S x rows j modulus (residue j) z ≤ C)
    (f g : (output → ℝ) → ℝ) (y : EuclideanJetLayers U O) :
    |allocatedCoveredProfileDensity B U b hR hσ S x u v rows hb o bW d
        (fun j _ => standardLatticeClosedQuarterBox (J j))
        (allocatedLongProfileDensity B U b S x rows modulus residue f) y -
      allocatedCoveredProfileDensity B U b hR hσ S x u v rows hb o bW d
        (fun j _ => standardLatticeClosedQuarterBox (J j))
        (allocatedLongProfileDensity B U b S x rows modulus residue g) y| ≤
      allocatedProfileErrorMajorant B U b S o hR hσ x u v rows
        (Real.toNNReal (coefficientDeckPeriodCap O Q period) * C ^ Fintype.card (LayerSamplerAxis I n))
        f g d y := by
  apply allocatedProfileDifference_le_majorant B U b S o hR hσ x u v rows hb bW d modulus residue _ ?_ f g y
  intro z r
  have hp (j) : integerScalarLattice (O j) (period : ℤ) ≤
      (boundedCoefficientJetMatrix root dirs (j.val + 1) (rows j)).mulVecLin.range := by
    rw [← allocatedPartitionedJetMatrix_eq_physical B U b S x u v rows j]
    exact (hperiod j).trans (allocatedPartitionedJetMatrix_kernel_range_le B U b S x u v rows j)
  have hd := coefficientDeckJetDensity_period_bound root dirs rows d period hp r
  have hmask := allocatedLongJetMask_product_bound B U b S x rows modulus residue hC hm z
  simp only [NNReal.coe_mul, NNReal.coe_pow,
    Real.coe_toNNReal _ (coefficientDeckPeriodCap_nonneg O Q period)]
  exact (mul_le_mul hmask hd (coefficientDeckJetDensity_nonneg root dirs rows d r)
    (pow_nonneg C.coe_nonneg _)).trans_eq (mul_comm _ _)

end Erdos3.VectorPolynomial

end

end OAI
