/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Geometry.SupportedComplexSelection
import OAI.Combinatorics.Progressions.Linear.AllocatedAveragedCoarseKernelComparison
import OAI.Combinatorics.Progressions.Linear.AllocatedOriginalDensityProjectionLaw
import OAI.Combinatorics.Progressions.Probability.PhysicalRowsDensityTransport

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {L H step : ℕ} (c : ℤ) (hL : 0 < L) (hH : 0 < H) (hstep : 0 < step)
variable (hsubset : integerProgressionSupport c (step : ℤ) H ⊆ Finset.Ico (0 : ℤ) (L : ℤ))

include hstep in
theorem containedProgressionCubeMap_injOn :
    Set.InjOn (containedProgressionCubeMap α L H step c hL hsubset) (integerScalarCubeSet α H) := by
  intro x hx y hy hxy
  have hx' := (mem_integerScalarCubeSet H x).mp hx
  have hy' := (mem_integerScalarCubeSet H y).mp hy
  funext i
  apply Subtype.ext
  have hi := congrArg (fun z : IntegerScalarCubeBox α L => (z i : ℤ)) hxy
  rw [containedProgressionCubeMap_value α L H step c hL hsubset x hx',
    containedProgressionCubeMap_value α L H step c hL hsubset y hy'] at hi
  have hs : (step : ℤ) ≠ 0 := by exact_mod_cast hstep.ne'
  exact mul_left_cancel₀ hs (add_left_cancel hi)

theorem integerScalarCubeWeights_mean_finset (L : ℕ) (hL : 0 < L)
    (f : IntegerScalarCubeBox α L → ℝ) :
    (integerScalarCubeWeights α L hL).mean f = 𝔼 x ∈ integerScalarCubeSet α L, f x := by
  let : Nonempty (IntegerScalarCubeBox α L) := ⟨integerScalarCubeBoxZero α L hL⟩
  have h := FiniteProbabilityWeights.uniform_condition_mean (integerScalarCubeSet α L)
    (integerScalarCubeReference_mass_pos α L hL) f
  simpa only [integerScalarCubeWeights, integerScalarCubeReference,
    Fintype.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card,
    Finset.sum_coe_sort, Finset.card_univ, Fintype.card_coe] using h

include hstep in
theorem containedScalarProgression_mean_le_card_ratio
    (f : IntegerScalarCubeBox α L → ℝ) (hf : ∀ y, 0 ≤ f y) :
    ((integerScalarCubeWeights α H hH).fiberLaw
      (containedProgressionCubeMap α L H step c hL hsubset)).mean f ≤
      ((integerScalarCubeSet α L).card : ℝ) / (integerScalarCubeSet α H).card *
        (integerScalarCubeWeights α L hL).mean f := by
  rw [FiniteProbabilityWeights.fiberLaw_mean,
    integerScalarCubeWeights_mean_finset, integerScalarCubeWeights_mean_finset]
  apply expect_injective_le_card_ratio _ _ (integerScalarCubeSet_nonempty α H hH)
    _ (containedProgressionCubeMap_injOn c hL hstep hsubset)
  · intro x _
    exact (mem_integerScalarCubeSet L _).mpr (containedProgressionCubeMap_cube α L H step c hL hsubset x)
  · intro y _
    exact hf y

include hstep in
theorem containedScalarProgression_weight_le_card_ratio (y : IntegerScalarCubeBox α L) :
    ((integerScalarCubeWeights α H hH).fiberLaw
      (containedProgressionCubeMap α L H step c hL hsubset)).weight y ≤
      ((integerScalarCubeSet α L).card : ℝ) / (integerScalarCubeSet α H).card *
        (integerScalarCubeWeights α L hL).weight y := by
  have h := containedScalarProgression_mean_le_card_ratio c hL hH hstep hsubset
    (fun z => if z = y then 1 else 0) (fun z => by split <;> norm_num)
  simpa only [FiniteProbabilityWeights.mean, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] using h

theorem integerScalarCubeSet_card_ratio_le {L H D : ℕ}
    (hH : 0 < H) (hsize : Fintype.card α + 1 ≤ H) (hLH : L ≤ D * H) :
    ((integerScalarCubeSet α L).card : ℝ) / (integerScalarCubeSet α H).card ≤
      scalarCubeResidueDensityCap α D := by
  let n := Fintype.card α + 1
  let h := H / n
  have hn : 0 < n := Nat.succ_pos _
  have hh : 0 < h := Nat.div_pos hsize hn
  have hlow := integerScalarCubeSet_card_lower α H h hh (Nat.mul_div_le H n)
  have hfloor : (H : ℝ) ≤ 2 * (n : ℝ) * h := by
    exact_mod_cast nat_div_half_lower hn hsize
  have hLH' : (L : ℝ) ≤ D * (H : ℝ) := by exact_mod_cast hLH
  have hscale : 2 * (L : ℝ) ≤ (4 * (n : ℝ) * D) * h := by
    nlinarith only [hLH', mul_le_mul_of_nonneg_left hfloor (Nat.cast_nonneg D)]
  have hpow := pow_le_pow_left₀ (mul_nonneg (by norm_num) (Nat.cast_nonneg L)) hscale n
  rw [mul_pow (4 * (n : ℝ) * D) (h : ℝ)] at hpow
  have hupper : ((integerScalarCubeSet α L).card : ℝ) ≤ (2 * (L : ℝ)) ^ n := by
    have h := Finset.card_le_univ (integerScalarCubeSet α L)
    rw [integerScalarCubeBox_card] at h
    exact_mod_cast h
  have hcard : 0 < ((integerScalarCubeSet α H).card : ℝ) := by
    exact_mod_cast (integerScalarCubeSet_nonempty α H hH).card_pos
  apply (div_le_iff₀ hcard).mpr
  apply (hupper.trans hpow).trans
  change (4 * (n : ℝ) * D) ^ n * (h : ℝ) ^ n ≤ _
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hlow)
    (pow_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n)) (Nat.cast_nonneg D)) n)

theorem containedProgressionCubeLaw_eventProbability_le
    {K : Type*} [Fintype K] [DecidableEq K]
    (L H step : K → ℕ) (c : K → ℤ) (hL : ∀ k, 0 < L k) (hH : ∀ k, 0 < H k)
    (hstep : ∀ k, 0 < step k)
    (hsubset : ∀ k, integerProgressionSupport (c k) (step k : ℤ) (H k) ⊆
      Finset.Ico (0 : ℤ) (L k : ℤ))
    (E : (∀ k, IntegerScalarCubeBox α (L k)) → Prop) :
    (containedProgressionCubeLaw (α := α) L H step c hL hH hsubset).eventProbability E ≤
      (∏ k, ((integerScalarCubeSet α (L k)).card : ℝ) / (integerScalarCubeSet α (H k)).card) *
        (FiniteProbabilityWeights.pi (fun k => integerScalarCubeWeights α (L k) (hL k))).eventProbability E := by
  let p := fun k => integerScalarCubeWeights α (H k) (hH k)
  let F := fun k => containedProgressionCubeMap α (L k) (H k) (step k) (c k) (hL k) (hsubset k)
  let q := fun k => (p k).fiberLaw (F k)
  have ht := FiniteProbabilityWeights.complexMean_pi_transport_fintype p q F (fun _ y => y)
    (fun k φ => ((p k).fiberLaw_complexMean (F k) φ).symm)
    (fun y => ((if E y then 1 else 0 : ℝ) : ℂ))
  have he := congrArg Complex.re ht
  simp only [FiniteProbabilityWeights.complexMean_re, Complex.ofReal_re] at he
  have hlaw : (containedProgressionCubeLaw (α := α) L H step c hL hH hsubset).eventProbability E =
      (FiniteProbabilityWeights.pi q).eventProbability E := by
    unfold FiniteProbabilityWeights.eventProbability containedProgressionCubeLaw
    rw [FiniteProbabilityWeights.fiberLaw_mean]
    exact he
  rw [hlaw]
  exact FiniteProbabilityWeights.pi_eventProbability_le q
    (fun k => integerScalarCubeWeights α (L k) (hL k)) _
    (fun k y => containedScalarProgression_weight_le_card_ratio
      (c k) (hL k) (hH k) (hstep k) (hsubset k) y) E

theorem containedProgressionKernel_explicit_probability_le
    {K : Type*} [Fintype K] [DecidableEq K] [Nonempty α]
    (hK : Fintype.card α * (Fintype.card α + 2) ≤ Fintype.card K) (selection : α ↪ K)
    {L D : ℕ} {η : ℝ} (hL : 0 < L) (hD : 0 < D) (hη : 0 < η)
    (hlarge : scalarKernelCutoff α K 1 D η ≤ L)
    (H step : K → ℕ) (c : K → ℤ) (hH : ∀ k, 0 < H k) (hstep : ∀ k, 0 < step k)
    (hLH : ∀ k, L ≤ D * H k)
    (hsubset : ∀ k, integerProgressionSupport (c k) (step k : ℤ) (H k) ⊆
      Finset.Ico (0 : ℤ) (L : ℤ)) :
    (containedProgressionCubeLaw (α := α) (fun _ => L) H step c (fun _ => hL) hH hsubset).eventProbability
      (fun x => ¬GoodScalarKernelTuple selection (1 / (scalarKernelCutoff α K 1 D η : ℝ))
        (scalarKernelCutoff α K 1 D η) x) ≤ η := by
  let C := scalarKernelConditioningConstant α K 1 D
  have hC : 0 < C := scalarKernelConditioningConstant_pos α K (by norm_num) hD
  have hsize (k) : Fintype.card α + 1 ≤ H k := by
    simpa only [Nat.mul_one] using scalarKernelCutoff_window_size α K
      (show 0 < 1 by norm_num) hD hη hlarge (hLH k)
  have hcap : (∏ k, ((integerScalarCubeSet α L).card : ℝ) / (integerScalarCubeSet α (H k)).card) ≤ C := by
    calc
      _ ≤ ∏ _k : K, scalarCubeResidueDensityCap α D := Finset.prod_le_prod₀
        (fun _ _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (fun k _ => integerScalarCubeSet_card_ratio_le (hH k) (hsize k) (hLH k))
      _ = C := by simp only [C, scalarKernelConditioningConstant, Nat.one_mul,
          Finset.prod_const, Finset.card_univ]
  have h := containedProgressionCubeLaw_eventProbability_le (fun _ => L) H step c
    (fun _ => hL) hH hstep hsubset
    (fun x => ¬GoodScalarKernelTuple selection (1 / (scalarKernelCutoff α K 1 D η : ℝ))
      (scalarKernelCutoff α K 1 D η) x)
  apply h.trans
  calc
    _ ≤ C * (FiniteProbabilityWeights.pi (fun _ : K => integerScalarCubeWeights α L hL)).eventProbability
        (fun x => ¬GoodScalarKernelTuple selection (1 / (scalarKernelCutoff α K 1 D η : ℝ))
          (scalarKernelCutoff α K 1 D η) x) := mul_le_mul_of_nonneg_right hcap
            (FiniteProbabilityWeights.eventProbability_nonneg _ _)
    _ ≤ C * scalarKernelAdjustedAccuracy α K 1 D η := mul_le_mul_of_nonneg_left
      (scalarKernel_explicit_probability_le_of_card_le α K hK selection (by norm_num) hD hη hL hlarge) hC.le
    _ = η := by
      change C * (η / C) = η
      exact mul_div_cancel₀ η hC.ne'

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel
open VectorPolynomial
open scoped Classical

variable {m q : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
local notation "Row" => (fun j : Fin m => {s : Finset (Fin q) // s ∈ boundedBooleanJetRows (Fin q) (Fin.val j + 1)})

theorem physicalRowsStandardEquiv_symm_sample {X : Type*}
    (d : ℕ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j) (v : X → (Unit ⊕ Fin q) → ℤ) :
    (physicalRowsStandardEquiv U).symm (physicalCubeEuclideanSample U d p hm v) =
      physicalCubeRowSample U d (fun j => (Subtype.val : Row j → Finset (Fin q))) p hm v := by
  rw [← physicalRowsToStandard_sample U d p hp hm]
  rfl

theorem physicalCubePositiveTest_rows {X : Type*}
    (d : ℕ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j e, coefficients (p j) e ∈ U j)
    (g : EuclideanJetLayers U Row → ℝ)
    (test : Finset (Fin q) → (X → ℝ) → ℂ) (v : X → (Unit ⊕ Fin q) → ℤ) :
    physicalCubePositiveTest U d p hm (fun z => g ((physicalRowsStandardEquiv U).symm z)) test v =
      physicalCubeSiteTest test v *
        (g (physicalCubeRowSample U d (fun j => (Subtype.val : Row j → Finset (Fin q))) p hm v) : ℂ) := by
  simp only [physicalCubePositiveTest, physicalRowsStandardEquiv_symm_sample U d p hp hm]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (X : Type*) [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))

local notation "widths" => narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
local notation "hwidths" => narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
local notation "baseDensity" => allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem
local notation "whole" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)

variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)
variable (htotal : 0 < selectedJointDensityMass bases stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)
  (allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem))

local notation "sides" => Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S)
local notation "hSides" => (Sum.rec (fun _ : G => S.positive) (allocatedPrincipalSides_pos B U b S))

variable (H : LayerSamplerVariables G I n B → ℕ) (hH : ∀ k, 0 < H k)
variable (c : LayerSamplerVariables G I n B → ℤ) (step : ℕ)
variable (hsubset : ∀ k : LayerSamplerVariables G I n B,
  integerProgressionSupport (c k) (step : ℤ) (H k) ⊆
  Finset.Ico (0 : ℤ)
    ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B U b S) k : ℕ) : ℤ))

local notation "kernelLaw" => containedProgressionCubeLaw (α := Fin dim)
  (fun _ : G => S.value) (fun g => H (Sum.inl g)) (fun _ => step) (fun g => c (Sum.inl g))
  (fun _ => S.positive) (fun g => hH (Sum.inl g)) (fun g => hsubset (Sum.inl g))
local notation "principalLaw" => containedProgressionCubeLaw (α := Fin dim)
  (allocatedPrincipalSides B U b S) (fun j => H (Sum.inr j)) (fun _ => step) (fun j => c (Sum.inr j))
  (allocatedPrincipalSides_pos B U b S) (fun j => hH (Sum.inr j)) (fun j => hsubset (Sum.inr j))

noncomputable def allocatedSlicedTupleValue
    (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
    (f : (X → ℤ) → ℂ) : ℂ :=
  (𝔼 base ∈ bases, ∑' z,
    ((selectedResidueSmoothPMF stride cells widths hwidths hmass z).toReal : ℂ) *
      (physicalCubeSiteTest (integerSelfSiteTest dim f)
        (physicalCubeRootDifferences
          (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
          (allocatedPhysicalCubeDirections B U b S x y) base z) *
        (baseDensity base z : ℂ))) /
    (selectedJointDensityMass bases stride cells widths baseDensity : ℂ)

omit [DecidableEq G] [∀ index, DecidableEq (I index)] [∀ axis, DecidableEq (B axis)]
    [∀ index, IsZLattice ℝ
      (latticeSection (standardEuclideanLattice (J index)) (euclideanSubspace (U index)))] in
private theorem allocatedSlicedTupleValue_coordinates
    (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
    (f : (X → ℤ) → ℂ) :
    allocatedSlicedTupleValue B U b hb o hR hσ S X poly hmem
      N hN hW hτ hξ stride cells hmass bases x y f =
    (𝔼 base ∈ bases, ∑' z,
      ((selectedResidueSmoothPMF stride cells widths hwidths hmass z).toReal : ℂ) *
        (physicalCubeSiteTest (integerSelfSiteTest dim f)
          (physicalCubeRootDifferences
            (fun k => ((Sum.rec x y k : IntegerScalarCubeBox (Fin dim) (sides k)) none : ℤ))
            (fun j k => ((Sum.rec x y k : IntegerScalarCubeBox (Fin dim) (sides k)) (some j) : ℤ)) base z) *
          (baseDensity base z : ℂ))) /
      (selectedJointDensityMass bases stride cells widths baseDensity : ℂ) := by
  have hroot : allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y =
      (fun k => ((Sum.rec x y k : IntegerScalarCubeBox (Fin dim) (sides k)) none : ℤ)) := by
    funext k
    cases k <;> exact zero_add _
  have hdirs : allocatedPhysicalCubeDirections B U b S x y =
      (fun j k => ((Sum.rec x y k : IntegerScalarCubeBox (Fin dim) (sides k)) (some j) : ℤ)) := by
    funext j k
    cases k <;> rfl
  unfold allocatedSlicedTupleValue
  rw [hroot, hdirs]

omit [∀ index, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J index)) (euclideanSubspace (U index)))] in
theorem allocatedSlicedCubeSource_disintegrate (f : (X → ℤ) → ℂ) :
    allocatedSlicedCubeSource (dim := dim) B U b hb o hR hσ S X poly hmem
      N hN hW hτ hξ stride cells hmass bases H hH c step f =
    (kernelLaw).complexMean (fun x => (principalLaw).complexMean (fun y =>
      allocatedSlicedTupleValue B U b hb o hR hσ S X poly hmem
        N hN hW hτ hξ stride cells hmass bases x y f)) := by
  let value := fun t : LayerSamplerVariables G I n B → Option (Fin dim) → ℤ =>
    (𝔼 base ∈ bases, ∑' z,
      ((selectedResidueSmoothPMF stride cells widths hwidths hmass z).toReal : ℂ) *
        (physicalCubeSiteTest (integerSelfSiteTest dim f)
          (physicalCubeRootDifferences (fun k => t k none) (fun j k => t k (some j)) base z) *
          (baseDensity base z : ℂ))) /
      (selectedJointDensityMass bases stride cells widths baseDensity : ℂ)
  have ht := containedProgressionCubeLaw_complexMean (α := Fin dim)
    sides H (fun _ => step) c hSides hH hsubset value
  have hsource : allocatedSlicedCubeSource (dim := dim) B U b hb o hR hσ S X poly hmem
      N hN hW hτ hξ stride cells hmass bases H hH c step f =
      (containedProgressionCubeLaw (α := Fin dim) sides H (fun _ => step) c hSides hH hsubset).complexMean
        (fun y => value (fun k i => (y k i : ℤ))) := by
    refine Eq.trans ?_ ht.symm
    unfold allocatedSlicedCubeSource
    apply congrArg (FiniteProbabilityWeights.pi
      (fun k => integerScalarCubeWeights (Fin dim) (H k) (hH k))).complexMean
    funext y
    dsimp only [value]
    have hroot : (fun k => (if (none : Option (Fin dim)) = none then c k else 0) +
        (step : ℤ) * (y k none : ℤ)) = commonStridePoint c step (fun k => (y k none : ℤ)) := rfl
    have hdir : (fun j k => (if some j = (none : Option (Fin dim)) then c k else 0) +
        (step : ℤ) * (y k (some j) : ℤ)) = (fun j k => (step : ℤ) * (y k (some j) : ℤ)) := by
      funext j k
      exact zero_add _
    rw [hroot, hdir]
  refine hsource.trans ((containedProgressionCubeLaw_sum sides H (fun _ => step) c hSides hH
    hsubset (fun y => value (fun k i => (y k i : ℤ)))).trans ?_)
  apply congrArg (kernelLaw).complexMean
  funext x
  apply congrArg (principalLaw).complexMean
  funext y
  exact (allocatedSlicedTupleValue_coordinates B U b hb o hR hσ S X poly hmem
    N hN hW hτ hξ stride cells hmass bases x y f).symm

include hbases htotal in
omit [DecidableEq G] [∀ index, DecidableEq (I index)] [∀ axis, DecidableEq (B axis)] in
theorem allocatedSlicedTupleValue_pathLaw
    (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
    (f : (X → ℤ) → ℂ) :
    allocatedSlicedTupleValue B U b hb o hR hσ S X poly hmem
      N hN hW hτ hξ stride cells hmass bases x y f =
    (allocatedOriginalPathLaw B U b hb o hR hσ S X poly hmem
      N hN hW hτ hξ stride cells hmass bases hbases htotal).complexMean (fun z =>
      physicalCubeSiteTest (integerSelfSiteTest dim f)
        (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
          (allocatedPhysicalCubeDirections B U b S x y) z.1.val z.2.val)) := by
  exact (selectedJointFiniteLaw_weighted_expectation bases hbases stride cells widths hwidths hmass
    baseDensity (allocatedJointBaseDensity_nonneg B U b hb o hR hσ S X poly hmem) htotal _).symm

include hbases htotal in
omit [DecidableEq G] [∀ index, DecidableEq (I index)] [∀ axis, DecidableEq (B axis)] in
theorem allocatedSlicedTupleValue_norm_le
    (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
    (f : (X → ℤ) → ℂ) (hf : ∀ u, ‖f u‖ ≤ 1) :
    ‖allocatedSlicedTupleValue B U b hb o hR hσ S X poly hmem
      N hN hW hτ hξ stride cells hmass bases x y f‖ ≤ 1 := by
  rw [allocatedSlicedTupleValue_pathLaw B U b hb o hR hσ S X poly hmem
    N hN hW hτ hξ stride cells hmass bases hbases htotal]
  let law := allocatedOriginalPathLaw B U b hb o hR hσ S X poly hmem
    N hN hW hτ hξ stride cells hmass bases hbases htotal
  apply (law.norm_complexMean_le_mean_norm _).trans
  exact (law.mean_mono (fun _ => physicalCubeSiteTest_norm_le _
    (integerSelfSiteTest_norm_le dim f hf) _)).trans_eq (law.mean_const 1)

include hbases htotal in

theorem allocatedSlicedCubeSource_good_residue_selection
    (f : (X → ℤ) → ℂ) (hf : ∀ u, ‖f u‖ ≤ 1)
    (Good : (G → IntegerScalarCubeBox (Fin dim) S.value) → Prop)
    {δ η : ℝ} (hδ : 0 < δ)
    (hbad : (kernelLaw).eventProbability (fun x => ¬Good x) ≤ η)
    (hlarge : δ + η ≤ (allocatedSlicedCubeSource (dim := dim) B U b hb o hR hσ S X poly hmem
      N hN hW hτ hξ stride cells hmass bases H hH c step f).re)
    (q : (G → IntegerScalarCubeBox (Fin dim) S.value) → ℕ) [∀ x, NeZero (q x)] :
    ∃ (x : G → IntegerScalarCubeBox (Fin dim) S.value),
      0 < (kernelLaw).weight x ∧ Good x ∧
    ∃ (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (q x))
      (hr : 0 < (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
        (fun j => H (Sum.inr j)) (fun j => hH (Sum.inr j))).mass
          (Finset.univ.filter (fun y => principalResidueLabel (q x) y = r))),
      δ ≤ ((containedSupportedProgressionLaw B (layerSamplerDegree I n)
        (allocatedPrincipalSides B U b S) (fun j => H (Sum.inr j)) (fun _ => step)
        (fun j => c (Sum.inr j)) (allocatedPrincipalSides_pos B U b S)
        (fun j => hH (Sum.inr j)) (fun j => hsubset (Sum.inr j)) (q x) r hr).complexMean
        (fun y => allocatedSlicedTupleValue B U b hb o hR hσ S X poly hmem
          N hN hW hτ hξ stride cells hmass bases x y f)).re := by
  let value := fun x y => allocatedSlicedTupleValue (dim := dim) B U b hb o hR hσ S X poly hmem
    N hN hW hτ hξ stride cells hmass bases x y f
  have hbound (x) : ‖(principalLaw).complexMean (value x)‖ ≤ 1 := by
    apply ((principalLaw).norm_complexMean_le_mean_norm _).trans
    exact ((principalLaw).mean_mono (fun y => allocatedSlicedTupleValue_norm_le B U b hb o hR hσ S
      X poly hmem N hN hW hτ hξ stride cells hmass bases hbases htotal x y f hf)).trans_eq
        ((principalLaw).mean_const 1)
  rw [allocatedSlicedCubeSource_disintegrate B U b hb o hR hσ S X poly hmem
    N hN hW hτ hξ stride cells hmass bases H hH c step hsubset] at hlarge
  obtain ⟨x, hx, hg, hv⟩ := (kernelLaw).exists_good_ge_complexMean_re_sub_bad Good
    (fun x => (principalLaw).complexMean (value x)) hbound hδ hbad hlarge
  let raw := principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
    (fun j => H (Sum.inr j)) (fun j => hH (Sum.inr j))
  let transport := containedProgressionTupleMap (α := Fin dim) B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U b S) (fun j => H (Sum.inr j)) (fun _ => step)
    (fun j => c (Sum.inr j)) (allocatedPrincipalSides_pos B U b S) (fun j => hsubset (Sum.inr j))
  have hraw : raw.complexMean (fun y => value x (transport y)) =
      (principalLaw).complexMean (value x) :=
    (raw.fiberLaw_complexMean transport (value x)).symm
  obtain ⟨r, hr, hc⟩ := raw.exists_positive_fiber_ge_complexMean_re
    (principalResidueLabel (q x)) (fun y => value x (transport y))
  refine ⟨x, hx, hg, r, hr, ?_⟩
  have hcond := (raw.condition (Finset.univ.filter (fun y => principalResidueLabel (q x) y = r)) hr).fiberLaw_complexMean
    transport (value x)
  exact ((hv.trans_eq (congrArg Complex.re hraw.symm)).trans hc).trans_eq
    (congrArg Complex.re hcond.symm)

include hbases htotal in

theorem allocatedSlicedCubeSource_good_kernel_residue
    [Nonempty (Fin dim)]
    (selection : Fin dim ↪ G) (hG : dim * (dim + 2) ≤ Fintype.card G)
    {D : ℕ} (hD : 0 < D) {δ η : ℝ} (hδ : 0 < δ) (hη : 0 < η)
    (hkernel : scalarKernelCutoff (Fin dim) G 1 D η ≤ S.value)
    (hstep : 0 < step) (hLH : ∀ g, S.value ≤ D * H (Sum.inl g))
    (f : (X → ℤ) → ℂ) (hf : ∀ u, ‖f u‖ ≤ 1)
    (hlarge : δ + η ≤ (allocatedSlicedCubeSource (dim := dim) B U b hb o hR hσ S X poly hmem
      N hN hW hτ hξ stride cells hmass bases H hH c step f).re)
    (q : (G → IntegerScalarCubeBox (Fin dim) S.value) → ℕ) [∀ x, NeZero (q x)] :
    let Mk := scalarKernelCutoff (Fin dim) G 1 D η
    ∃ (x : G → IntegerScalarCubeBox (Fin dim) S.value),
      0 < (kernelLaw).weight x ∧ GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x ∧
    ∃ (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod (q x))
      (hr : 0 < (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
        (fun j => H (Sum.inr j)) (fun j => hH (Sum.inr j))).mass
          (Finset.univ.filter (fun y => principalResidueLabel (q x) y = r))),
      δ ≤ ((containedSupportedProgressionLaw B (layerSamplerDegree I n)
        (allocatedPrincipalSides B U b S) (fun j => H (Sum.inr j)) (fun _ => step)
        (fun j => c (Sum.inr j)) (allocatedPrincipalSides_pos B U b S)
        (fun j => hH (Sum.inr j)) (fun j => hsubset (Sum.inr j)) (q x) r hr).complexMean
        (fun y => allocatedSlicedTupleValue B U b hb o hR hσ S X poly hmem
          N hN hW hτ hξ stride cells hmass bases x y f)).re := by
  intro Mk
  have hbad := containedProgressionKernel_explicit_probability_le
    (by simpa only [Fintype.card_fin] using hG) selection S.positive hD hη hkernel
    (fun g => H (Sum.inl g)) (fun _ => step) (fun g => c (Sum.inl g))
    (fun g => hH (Sum.inl g)) (fun _ => hstep) hLH (fun g => hsubset (Sum.inl g))
  exact allocatedSlicedCubeSource_good_residue_selection B U b hb o hR hσ S X poly hmem
    N hN hW hτ hξ stride cells hmass bases hbases htotal H hH c step hsubset f hf
    (GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk) hδ hbad hlarge q

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ} (X : Type*) [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)

variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]

variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))

local notation "widths" => narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
local notation "hwidths" => narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
local notation "baseDensity" => allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem
local notation "whole" => principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) (allocatedPrincipalSides_pos B U b S)

variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)
variable (htotal : 0 < selectedJointDensityMass bases stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)
  (allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem))

local notation "Z" => selectedJointDensityMass bases stride cells widths baseDensity

include hbases in
omit [DecidableEq G] [∀ index, IsZLattice ℝ
  (latticeSection (standardEuclideanLattice (J index)) (euclideanSubspace (U index)))] in
theorem allocatedSlicedTupleValue_select_base
    (x : G → IntegerScalarCubeBox (Fin dim) S.value)
    (law : FiniteProbabilityWeights (PrincipalIntegerTuples B (layerSamplerDegree I n)
      (Fin dim) (allocatedPrincipalSides B U b S)))
    (f : (X → ℤ) → ℂ) {κ : ℝ}
    (hsource : κ ≤ (law.complexMean (fun y => allocatedSlicedTupleValue B U b hb o hR hσ S X poly hmem
      N hN hW hτ hξ stride cells hmass bases x y f)).re) :
    ∃ base ∈ bases,
      κ ≤ (law.complexMean (fun y => ∑' z,
        ((selectedResidueSmoothPMF stride cells widths hwidths hmass z).toReal : ℂ) *
          (physicalCubeSiteTest (integerSelfSiteTest dim f)
            (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
              (allocatedPhysicalCubeDirections B U b S x y) base z) * (baseDensity base z : ℂ))) /
        (Z : ℂ)).re := by
  let value := fun base => law.complexMean (fun y => ∑' z,
    ((selectedResidueSmoothPMF stride cells widths hwidths hmass z).toReal : ℂ) *
      (physicalCubeSiteTest (integerSelfSiteTest dim f)
        (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x y)
          (allocatedPhysicalCubeDirections B U b S x y) base z) * (baseDensity base z : ℂ))) / (Z : ℂ)
  have hmean : law.complexMean (fun y => allocatedSlicedTupleValue B U b hb o hR hσ S X poly hmem
      N hN hW hτ hξ stride cells hmass bases x y f) = 𝔼 base ∈ bases, value base := by
    simp only [allocatedSlicedTupleValue, FiniteProbabilityWeights.complexMean_div,
      FiniteProbabilityWeights.complexMean_finset_expect, Finset.expect_div, value]
  rw [hmean, ← FiniteProbabilityWeights.uniformFinset_complexMean bases hbases value] at hsource
  obtain ⟨base, _, hbase⟩ := (FiniteProbabilityWeights.uniformFinset bases hbases).exists_positive_weight_ge_complexMean_re
    (fun base => value base.val)
  exact ⟨base.val, base.property, hsource.trans hbase⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

universe uX

theorem exists_allocated_sliced_projected_source (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    [DecidableEq (LayerSamplerVariables G I n B)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (x : G → IntegerScalarCubeBox (Fin q) S.value)
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (_hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P W : ℝ} (_hP : 0 ≤ P) (_hm : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hW : 0 ≤ W) (_hbudget : allocatedPhysicalRootBudget B U basis S (fun _ => 0) ≤ W)
    (_hWP : W ≤ Real.exp P) (_hL : (S.value : ℝ) ≤ Real.exp P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    {M : ℕ} (_hperiod : HasBoundedScalarPeriod (scalarCubeDifferenceMatrix x).mulVecLin.range M)
    {X : Type uX} [Fintype X] [DecidableEq X]
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {τ ξ : ℝ} (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (hN : ∀ i, 0 < N i) (_hsize : ∀ d, Real.exp ((P + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + A) ^ A) ≤ rank)
    (signal : (X → ℤ) → ℂ) (_hsignal : ∀ v, ‖signal v‖ ≤ 1)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty)
    (bases : Finset (X → ℤ)) (_hbases : bases.Nonempty)
    (D : ℕ)
    (f : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U basis S) →
      EuclideanJetLayers U (fun j : Fin m => BoundedBooleanJet (Fin q) (j.val + 1)) → ℝ),
    let density := allocatedCoefficientDensity B U basis hb o hR hσ S
    ∀ (_hproject : ∀ y, physicalDensityProjection.{_, _, uX, 0} U
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y) D density (f y)),
    let widths := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    ∀ (hwidths : ∀ z, 0 < widths z) (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z),
    ∀ law : FiniteProbabilityWeights (PrincipalIntegerTuples B (layerSamplerDegree I n)
      (Fin q) (allocatedPrincipalSides B U basis S)),
    let Z := selectedJointDensityMass bases stride T widths (allocatedJointBaseDensity B U basis hb o hR hσ S X p hm)
    ∀ (_hZ : 0 < Z) (_hZi : Z⁻¹ ≤ Real.exp P) {κ : ℝ},
    κ ≤ (law.complexMean (fun y => allocatedSlicedTupleValue B U basis hb o hR hσ S X p hm
      N hN _hW _hτ _hξ stride T hmass bases x y signal)).re →
    ∃ base ∈ bases,
      let projected := fun y => ∑' z,
        ((selectedResidueSmoothPMF stride T widths hwidths hmass z).toReal : ℂ) *
          physicalCubePositiveTest U D p hm (f y) (integerSelfSiteTest q signal) (physicalCubeRootDifferences
            (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
            (allocatedPhysicalCubeDirections B U basis S x y) base z)
      κ - Real.exp (-P) ≤ (law.complexMean projected / (Z : ℂ)).re := by
  obtain ⟨A, hA, hprojection⟩ := exists_allocated_original_density_projection_law m q
  refine ⟨A, hA, ?_⟩
  intro G _ _ I _ _ n B _ _ _ J _ U _ basis R σ S x hb o hR hσ C V hC hV
    hσ1 Cinv hCinv hchart hsmall P W hP hmSize hK hW hroot hWP hL hRP hσP hcount hI hn hJ
    hAP hCP hVP M hperiod X _ _ hX hdim p hp hm stride hs hsP τ ξ hτ hτP hξ hξ1 hξP
    N hN hsize rank hrank hRank signal hsignal T hT bases hbases D f density hproject widths hwidths hmass
    law Z hZ hZi κ hsource
  obtain ⟨base, hbase, hpositive⟩ := allocatedSlicedTupleValue_select_base B U basis hb o hR hσ S X p hm
    N hN hW hτ hξ stride T hmass bases hbases x law signal hsource
  have he := hprojection B U basis S (fun _ => 0) x hb o hR hσ C V hC hV hσ1
    Cinv hCinv hchart hsmall hP hmSize hK hW hroot hWP hL hRP hσP hcount hI hn hJ hAP hCP hVP
    hperiod hX hdim p hp hm base stride hs hsP hτ hτP hξ hξ1 hξP N hsize hrank hRank
    (integerSelfSiteTest q signal) (integerSelfSiteTest_norm_le q signal hsignal) T hT D f hproject
    hZ hZi hwidths hmass law
  refine ⟨base, hbase, ?_⟩
  dsimp only at he ⊢
  have hdiff := (Complex.re_le_norm _).trans he
  rw [Complex.sub_re] at hdiff
  change κ ≤ _ at hpositive
  dsimp only [allocatedJointBaseDensity] at hpositive
  linarith only [hpositive, hdiff]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel Module Submodule MeasureTheory
open scoped BigOperators Classical NNReal

universe uX

theorem exists_allocated_sliced_rows_projected_source (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {G : Type*} [Fintype G] [DecidableEq G]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
    [DecidableEq (LayerSamplerVariables G I n B)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (basis : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
    {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
    (x : G → IntegerScalarCubeBox (Fin q) S.value)
    (hb : ∀ j, span ℤ (Set.range (basis j)) = projectedIntegerLattice (euclideanSubspace (U j)))
    (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
    (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j) (C V : Fin m → ℝ≥0)
    (_hC : ∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j) z‖ ≤ C j * ‖z‖)
    (_hV : ∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ∧
      mixedDensityCovolumeRatio (euclideanSubspace (U j)) (basis j) ≤ V j)
    (_hσ1 : ∀ j, σ j ≤ 1) (Cinv : Fin m → ℝ) (_hCinv : ∀ j, 0 ≤ Cinv j)
    (_hchart : ∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (basis j)).symm z‖ ≤ Cinv j * ‖z‖)
    (_hsmall : ∀ j, Cinv j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)
    {P W : ℝ} (_hP : 0 ≤ P) (_hm : (m : ℝ) ≤ P)
    (_hK : (Fintype.card (LayerSamplerVariables G I n B) : ℝ) ≤ P)
    (_hW : 0 ≤ W) (_hbudget : allocatedPhysicalRootBudget B U basis S (fun _ => 0) ≤ W)
    (_hWP : W ≤ Real.exp P) (_hL : (S.value : ℝ) ≤ Real.exp P)
    (_hRP : ∀ j, (R j)⁻¹ ≤ Real.exp P) (_hσP : ∀ j, (σ j)⁻¹ ≤ Real.exp P)
    (_hcount : ∀ j : Fin m,
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ P)
    (_hI : ∀ j, (Fintype.card (I j) : ℝ) ≤ P) (_hn : ∀ j, (n j : ℝ) ≤ P)
    (_hJ : ∀ j, (Fintype.card (J j) : ℝ) ≤ P)
    (_hAP : (probabilityProfileLipschitz : ℝ) ≤ Real.exp P)
    (_hCP : ∀ j, (C j : ℝ) ≤ Real.exp P) (_hVP : ∀ j, (V j : ℝ) ≤ Real.exp P)
    {M : ℕ} (_hperiod : HasBoundedScalarPeriod (scalarCubeDifferenceMatrix x).mulVecLin.range M)
    {X : Type uX} [Fintype X] [DecidableEq X]
    (_hX : (Fintype.card X : ℝ) ≤ P)
    (_hdim : (Fintype.card (Option (LayerSamplerVariables G I n B) × X) : ℝ) ≤ P)
    (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : X → ℕ) (_hs : ∀ d, 0 < stride d) (_hsP : ∀ d, (stride d : ℝ) ≤ Real.exp P)
    {τ ξ : ℝ} (_hτ : 0 < τ) (_hτP : τ⁻¹ ≤ Real.exp P)
    (_hξ : 0 < ξ) (_hξ1 : ξ ≤ 1) (_hξP : ξ⁻¹ ≤ Real.exp P)
    (N : X → ℕ) (hN : ∀ i, 0 < N i) (_hsize : ∀ d, Real.exp ((P + A) ^ A) ≤ (N d : ℝ))
    {rank : ℝ} (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) (fun d => (N d : ℝ)) rank (U j) (p j))
    (_hRank : Real.exp ((P + A) ^ A) ≤ rank)
    (signal : (X → ℤ) → ℂ) (_hsignal : ∀ v, ‖signal v‖ ≤ 1)
    (T : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)) (_hT : T.Nonempty)
    (bases : Finset (X → ℤ)) (_hbases : bases.Nonempty)
    (D : ℕ)
    (f : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin q) (allocatedPrincipalSides B U basis S) →
      EuclideanJetLayers U (fun j : Fin m => {s : Finset (Fin q) // s ∈ boundedBooleanJetRows (Fin q) (j.val + 1)}) → ℝ),
    let density := allocatedCoefficientDensity B U basis hb o hR hσ S
    ∀ (_hproject : ∀ y, physicalDensityProjection.{_, _, uX, 0} U
      (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
      (allocatedPhysicalCubeDirections B U basis S x y) D density (fun z => f y ((physicalRowsStandardEquiv U).symm z))),
    let widths := narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
    ∀ (hwidths : ∀ z, 0 < widths z) (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride T widths z),
    ∀ law : FiniteProbabilityWeights (PrincipalIntegerTuples B (layerSamplerDegree I n)
      (Fin q) (allocatedPrincipalSides B U basis S)),
    let Z := selectedJointDensityMass bases stride T widths (allocatedJointBaseDensity B U basis hb o hR hσ S X p hm)
    ∀ (_hZ : 0 < Z) (_hZi : Z⁻¹ ≤ Real.exp P) {κ : ℝ},
    κ ≤ (law.complexMean (fun y => allocatedSlicedTupleValue B U basis hb o hR hσ S X p hm
      N hN _hW _hτ _hξ stride T hmass bases x y signal)).re →
    ∃ base ∈ bases,
      let projected := fun y => ∑' z,
        ((selectedResidueSmoothPMF stride T widths hwidths hmass z).toReal : ℂ) *
          (physicalCubeSiteTest (integerSelfSiteTest q signal) (physicalCubeRootDifferences
            (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
            (allocatedPhysicalCubeDirections B U basis S x y) base z) *
          (f y (physicalCubeRowSample U D (fun j =>
            (Subtype.val : {s : Finset (Fin q) // s ∈ boundedBooleanJetRows (Fin q) (j.val + 1)} → Finset (Fin q))) p hm
            (physicalCubeRootDifferences (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y)
              (allocatedPhysicalCubeDirections B U basis S x y) base z)) : ℂ))
      κ - Real.exp (-P) ≤ (law.complexMean projected / (Z : ℂ)).re := by
  obtain ⟨A, hA, hprojection⟩ := exists_allocated_sliced_projected_source.{uX} m q
  refine ⟨A, hA, ?_⟩
  intro G _ _ I _ _ n B _ _ _ J _ U _ basis R σ S x hb o hR hσ C V hC hV
    hσ1 Cinv hCinv hchart hsmall P W hP hmSize hK hW hroot hWP hL hRP hσP hcount hI hn hJ
    hAP hCP hVP M hperiod X _ _ hX hdim p hp hm stride hs hsP τ ξ hτ hτP hξ hξ1 hξP
    N hN hsize rank hrank hRank signal hsignal T hT bases hbases D f density hproject widths hwidths hmass
    law Z hZ hZi κ hsource
  obtain ⟨base, hbase, he⟩ := hprojection B U basis S x hb o hR hσ C V hC hV hσ1 Cinv hCinv hchart hsmall
    hP hmSize hK hW hroot hWP hL hRP hσP hcount hI hn hJ hAP hCP hVP hperiod hX hdim p hp hm
    stride hs hsP hτ hτP hξ hξ1 hξP N hN hsize hrank hRank signal hsignal T hT bases hbases D
    (fun y z => f y ((physicalRowsStandardEquiv U).symm z)) hproject hwidths hmass law hZ hZi hsource
  refine ⟨base, hbase, ?_⟩
  simpa only [physicalCubePositiveTest_rows U D p hp hm] using he

end Erdos3.VectorPolynomial

end

end OAI
