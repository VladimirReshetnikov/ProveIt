/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Sampling.AllocatedFrozenGridLaw
import OAI.Combinatorics.Progressions.Sampling.CoveredSamplerHaarDensity

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical NNReal

theorem integerMatrixRealDensity_affine_continuous {O J : Type*}
    [Fintype O] [DecidableEq O] [Fintype J] [DecidableEq J]
    (A : Matrix O J ℤ) (s : O ↪ J) (hA : (A.submatrix id s).det ≠ 0)
    (c w : J → ℝ) (hw : ∀ j, 0 < w j) :
    Continuous (integerMatrixRealDensity A s hA (affineProductProfile c w)) := by
  let D := (∑ j, (w j)⁻¹) + 1
  have hD : 0 < D := by
    have h := Finset.sum_nonneg (s := Finset.univ) (fun j _ => (inv_pos.mpr (hw j)).le)
    dsimp [D]
    linarith
  let δ : ℝ≥0 := ⟨D⁻¹, (inv_pos.mpr hD).le⟩
  have hδ : 0 < δ := inv_pos.mpr hD
  have hwidth (j) : (δ : ℝ) ≤ w j := by
    have hj : (w j)⁻¹ ≤ D :=
      (Finset.single_le_sum (fun k _ => (inv_pos.mpr (hw k)).le) (Finset.mem_univ j)).trans
        (le_add_of_nonneg_right zero_le_one)
    change D⁻¹ ≤ w j
    simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr (hw j)) hj
  let R : ℝ≥0 := ⟨∑ j, (|c j| + w j),
    Finset.sum_nonneg (fun j _ => add_nonneg (abs_nonneg _) (hw j).le)⟩
  have hR (j) : |c j| + w j ≤ (R : ℝ) :=
    Finset.single_le_sum (fun k _ => add_nonneg (abs_nonneg _) (hw k).le) (Finset.mem_univ j)
  exact (pivotOutputDensity_lipschitz _ _ R _
    (selectedCoefficientProfile_lipschitz s (affineProductProfile_lipschitz c w hδ hwidth))
    (selectedCoefficientProfile_zero_outside s
      (affineProductProfile_zero_outside c w hw R.coe_nonneg hR))).continuous

theorem mixedArrayImageDensity_continuous {I Z O J : Type*}
    [Fintype I] [Fintype Z] [Fintype O] [DecidableEq O] [Fintype J] [DecidableEq J]
    (A : Matrix O J ℤ) (s : O ↪ J) (hA : (A.submatrix id s).det ≠ 0)
    (c w : I → J → ℝ) (hw : ∀ i j, 0 < w i j) (p : Z → J → PMF ℤ) :
    Continuous (mixedArrayImageDensity A s hA c w p) := by
  apply Continuous.mul
  · apply continuous_finsetProd
    intro i _
    exact (integerMatrixRealDensity_affine_continuous A s hA (c i) (w i) (hw i)).comp
      ((continuous_apply i).comp continuous_fst)
  · exact (continuous_of_discreteTopology (f := fun z : Z → O → ℤ =>
      ∏ i, (integerMatrixImagePMF A (p i) (z i)).toReal)).comp continuous_snd

namespace VectorPolynomial

variable {α K : Type*} [DecidableEq α] [Fintype K]
variable {m : ℕ} {O J I B : Fin m → Type*}
variable [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable [∀ j, Fintype (J j)] [∀ j, Fintype (I j)] [∀ j, Fintype (B j)] {n : Fin m → ℕ}
variable (root : K → ℤ) (A : Matrix α K ℤ) (rows : ∀ j, O j → Finset α)
variable (pivot : ∀ j, O j ↪ BoundedCoefficientExponent K (j.val + 1))
variable (hpivot : ∀ j, ((boundedCoefficientJetMatrix root A (j.val + 1) (rows j)).submatrix
  id (pivot j)).det ≠ 0)
variable (c w : ∀ j, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
variable (hw : ∀ j i e, 0 < w j i e)
variable (p : ∀ j, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)

include hw in
theorem canonicalCoefficientJetImageDensity_continuous :
    Continuous (canonicalCoefficientJetImageDensity root A rows pivot hpivot c w p) := by
  apply continuous_finsetProd
  intro j _
  exact (mixedArrayImageDensity_continuous _ (pivot j) (hpivot j) (c j) (w j) (hw j) (p j)).comp
    (continuous_apply j)

include hw in
theorem canonicalCoveredArrayDensity_continuous
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (d : ℕ) [NeZero d] :
    Continuous (canonicalCoveredArrayDensity (B := B) U root A rows pivot hpivot c w p d) := by
  apply Continuous.div_const
  exact ((canonicalCoefficientJetImageDensity_continuous root A rows pivot hpivot c w hw p).comp
    continuous_fst).mul ((continuous_of_discreteTopology (f := coefficientDeckJetDensity
      (B := B) root A rows d)).comp continuous_snd)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical Matrix NNReal

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

include hR hσ in
theorem allocatedContinuousKernelDensity_output_continuous (j : Fin m) (i : I j)
    (s : O j ↪ BoundedIntegerExponent G (j.val + 1))
    (hA : ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id s).det ≠ 0)
    (hσ1 : σ j ≤ 1)
    (y : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℝ) :
    Continuous (allocatedContinuousKernelDensity B U b S j i x u (rows j) s hA y) := by
  let reindex := allocatedKernelCoefficientEquiv (G := G) B j
  let δ : ℝ≥0 := ⟨allocatedUnitProfileWidth (R j) (σ j)
    (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1))),
    (allocatedUnitProfileWidth_pos (hR j) (hσ j) _).le⟩
  have hδ : 0 < δ := allocatedUnitProfileWidth_pos (hR j) (hσ j) _
  unfold allocatedContinuousKernelDensity
  exact (affineSelectedJetDensity_output_lipschitz s _ _ _ _ _ _ _ _
    (fun t => allocatedContinuousProfileWidths_pos B hR hσ j i (reindex t)) hδ
    (fun t => allocatedContinuousProfileWidths_floor B hR j i (reindex (.inl t)))
    ⟨R j, (hR j).le⟩
    (fun t => allocatedContinuousProfile_bound B hR hσ j i hσ1 (reindex t)) y).continuous

include hR hσ in
theorem allocatedPhysicalRealJetDensity_eq (j : Fin m) (i : I j)
    (s : O j ↪ BoundedIntegerExponent G (j.val + 1))
    (hA : ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id s).det ≠ 0)
    (pivot : O j ↪ BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1))
    (hpivot : ((boundedCoefficientJetMatrix root dirs (j.val + 1) (rows j)).submatrix id pivot).det ≠ 0)
    (hσ1 : σ j ≤ 1) :
    integerMatrixRealDensity (boundedCoefficientJetMatrix root dirs (j.val + 1) (rows j)) pivot hpivot
      (affineProductProfile (allocatedLayerCenters B U b S j i) (allocatedLayerWidths B U b S j i)) =
    allocatedContinuousKernelDensity B U b S j i x u (rows j) s hA
      (principalTupleNormalized (principalAxisLength (fun a => ¬grid a) sides) v) := by
  have hw := allocatedLayerWidths_pos B U b hR hσ S j i
  apply continuousDensity_eq_of_measure_eq
    (integerMatrixRealDensity_affine_continuous _ pivot hpivot _ _ hw)
    (allocatedContinuousKernelDensity_output_continuous B U b hR hσ S x u rows j i s hA hσ1 _)
    (integerMatrixRealDensity_nonneg _ pivot hpivot (affineProductProfile_nonneg _ _ hw))
    (allocatedContinuousKernelDensity_probability_data B U b hR hσ S j i x u (rows j) s hA hσ1 _).1
  have hfull := integerMatrixRealDensity_affine_law
    (boundedCoefficientJetMatrix root dirs (j.val + 1) (rows j)) pivot hpivot
    (allocatedLayerCenters B U b S j i) (allocatedLayerWidths B U b S j i) hw
  change (allocatedCoefficientAxisLaw B U b hR hσ S ⟨j, Sum.inl i⟩).map
    (fun a => (boundedCoefficientJetMatrix root dirs (j.val + 1) (rows j)).map (Int.cast : ℤ → ℝ) *ᵥ a) = _ at hfull
  have hpart := allocatedContinuousKernel_image_law B U b hR hσ S j i x u (rows j) s hA hσ1 v
  change (allocatedCoefficientAxisLaw B U b hR hσ S ⟨j, Sum.inl i⟩).map
    (fun a => (allocatedPartitionedJetMatrix B U b S x u v rows j).map (Int.cast : ℤ → ℝ) *ᵥ a) = _ at hpart
  rw [allocatedPartitionedJetMatrix_eq_physical B U b S x u v rows j] at hpart
  exact hfull.symm.trans hpart

omit [Fintype α] [∀ j, DecidableEq (O j)] in
theorem allocatedPhysicalIntegerJetPMF_eq (j : Fin m) (i : Fin (n j))
    (hσ1 : σ j ≤ 1) (hlong : S.value ^ (layerTailDegree m + 1) < basisAxisScale (b j) i) :
    integerMatrixImagePMF (boundedCoefficientJetMatrix root dirs (j.val + 1) (rows j))
      (allocatedLayerIntegerPMFs B U b hR hσ S j i) =
    allocatedIntegerKernelPMF B U b hR hσ S x u v rows j i hσ1 hlong := by
  apply PMF.toMeasure_injective
  rw [← integerMatrixImagePMF_law]
  change (allocatedCoefficientAxisLaw B U b hR hσ S ⟨j, Sum.inr i⟩).map
    (fun a => boundedCoefficientJetMatrix root dirs (j.val + 1) (rows j) *ᵥ a) = _
  rw [← allocatedPartitionedJetMatrix_eq_physical B U b S x u v rows j]
  exact allocatedIntegerKernelPMF_law B U b hR hσ S x u v rows j i hσ1 hlong

omit [Fintype α] [∀ j, DecidableEq (O j)] in
theorem allocatedPhysicalGridJetPMF_eq
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    (j : Fin m) (i : Fin (n j)) (hgrid : grid ⟨j, Sum.inr i⟩) :
    integerMatrixImagePMF (boundedCoefficientJetMatrix root dirs (j.val + 1) (rows j))
      (allocatedLayerIntegerPMFs B U b hR hσ S j i) =
    integerMatrixImagePMF (boundedCoefficientJetMatrix
      (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v₀))
      (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v₀)) (j.val + 1) (rows j))
      (allocatedLayerIntegerPMFs B U b hR hσ S j i) := by
  apply PMF.toMeasure_injective
  rw [← integerMatrixImagePMF_law, ← integerMatrixImagePMF_law,
    ← allocatedPartitionedJetMatrix_eq_physical B U b S x u v rows j,
    ← allocatedPartitionedJetMatrix_eq_physical B U b S x u v₀ rows j]
  apply Measure.map_congr
  have hs : ∀ᵐ a ∂Measure.pi (fun d => (allocatedLayerIntegerPMFs B U b hR hσ S j i d).toMeasure),
      ∀ d, a d ∈ (allocatedLayerIntegerPMFs B U b hR hσ S j i d).support :=
    ae_all_iff.mpr (fun d => (Measure.quasiMeasurePreserving_eval _ d).ae (pmf_support_ae _))
  filter_upwards [hs] with a ha
  exact allocatedGridAxis_jet_frozen B U b S hR hσ j i hgrid a ha (fun g t => (g, t))
    (Sum.elim (fun gt : G × Option α => (x gt.1 gt.2 : ℤ)) (principalTupleIntegers u))
    (principalTupleIntegers v) (principalTupleIntegers v₀) (rows j)

end Erdos3.VectorPolynomial

end

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

noncomputable def allocatedGridJetFactor :
    ∀ a : {a // grid a}, CoefficientJetAxisRow O a.val → ℝ
  | ⟨⟨_, .inl _⟩, ha⟩ => False.elim ha
  | ⟨⟨j, .inr i⟩, _⟩ => fun z =>
      (integerMatrixImagePMF (boundedCoefficientJetMatrix root dirs (j.val + 1) (rows j))
        (allocatedLayerIntegerPMFs B U b hR hσ S j i) z).toReal

noncomputable def allocatedGridJetDensity (z : AllocatedFrozenJetRows B U b S O) : ℝ :=
  ∏ a, allocatedGridJetFactor B U b hR hσ S x u v rows a (z a)

omit [Fintype α] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
theorem allocatedGridJetFactor_mem_Icc (a : {a // grid a}) (z : CoefficientJetAxisRow O a.val) :
    allocatedGridJetFactor B U b hR hσ S x u v rows a z ∈ Set.Icc (0 : ℝ) 1 := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · refine ⟨ENNReal.toReal_nonneg, ?_⟩
    exact (ENNReal.toReal_mono ENNReal.one_ne_top ((integerMatrixImagePMF
      (boundedCoefficientJetMatrix root dirs (j.val + 1) (rows j))
      (allocatedLayerIntegerPMFs B U b hR hσ S j i)).coe_le_one z)).trans_eq ENNReal.toReal_one

omit [Fintype α] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
theorem allocatedGridJetDensity_mem_Icc (z : AllocatedFrozenJetRows B U b S O) :
    allocatedGridJetDensity B U b hR hσ S x u v rows z ∈ Set.Icc (0 : ℝ) 1 := by
  have h := allocatedGridJetFactor_mem_Icc B U b hR hσ S x u v rows
  exact ⟨Finset.prod_nonneg (fun a _ => (h a (z a)).1),
    Finset.prod_le_one₀ (fun a _ => (h a (z a)).1) (fun a _ => (h a (z a)).2)⟩

omit [Fintype α] in
theorem allocatedPhysicalGridDensityFactor_eq
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    (pivot : ∀ j, O j ↪ BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1))
    (hpivot : ∀ j, ((boundedCoefficientJetMatrix root dirs (j.val + 1) (rows j)).submatrix id (pivot j)).det ≠ 0)
    (a : {a // grid a}) (z : CoefficientJetAxisRow O a.val) :
    coefficientJetDensityFactor (fun j => boundedCoefficientJetMatrix root dirs (j.val + 1) (rows j))
      pivot hpivot (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
      (allocatedLayerIntegerPMFs B U b hR hσ S) a.val z =
    allocatedGridJetFactor B U b hR hσ S x u v₀ rows a z := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · simp only [coefficientJetDensityFactor, allocatedGridJetFactor]
    exact congrArg (fun p : PMF (O j → ℤ) => (p z).toReal)
      (allocatedPhysicalGridJetPMF_eq B U b hR hσ S x u v rows v₀ j i ha)

theorem allocatedPhysicalLongDensityFactor_eq
    (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
    (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
    (pivot : ∀ j, O j ↪ BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1))
    (hpivot : ∀ j, ((boundedCoefficientJetMatrix root dirs (j.val + 1) (rows j)).submatrix id (pivot j)).det ≠ 0)
    (hσ1 : ∀ j, σ j ≤ 1) (a : {a // ¬grid a}) :
    coefficientJetDensityFactor (fun j => boundedCoefficientJetMatrix root dirs (j.val + 1) (rows j))
      pivot hpivot (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
      (allocatedLayerIntegerPMFs B U b hR hσ S) a.val =
    allocatedLongJetFactor B U b hR hσ S x u v rows s hA hσ1 a := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · dsimp only [coefficientJetDensityFactor, allocatedLongJetFactor, CoefficientJetAxisRow]
    have heq := allocatedPhysicalRealJetDensity_eq B U b hR hσ S x u v rows j i
      (s j) (hA j) (pivot j) (hpivot j) (hσ1 j)
    convert heq using 3
  · funext z
    simp only [coefficientJetDensityFactor, allocatedLongJetFactor]
    exact congrArg (fun p : PMF (O j → ℤ) => (p z).toReal)
      (allocatedPhysicalIntegerJetPMF_eq B U b hR hσ S x u v rows j i (hσ1 j) (Nat.lt_of_not_ge ha))

theorem allocatedPhysicalMixedDensity_factorization
    (v₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
    (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
    (pivot : ∀ j, O j ↪ BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1))
    (hpivot : ∀ j, ((boundedCoefficientJetMatrix root dirs (j.val + 1) (rows j)).submatrix id (pivot j)).det ≠ 0)
    (hσ1 : ∀ j, σ j ≤ 1)
    (z : ∀ j, (I j → O j → ℝ) × (Fin (n j) → O j → ℤ)) :
    canonicalCoefficientJetImageDensity root dirs rows pivot hpivot
      (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
      (allocatedLayerIntegerPMFs B U b hR hσ S) z =
    allocatedGridJetDensity B U b hR hσ S x u v₀ rows (fun a => axis z a.val) *
      allocatedLongJetDensity B U b hR hσ S x u v rows s hA hσ1 (fun a => axis z a.val) := by
  rw [canonicalCoefficientJetImageDensity_axis_product]
  rw [← Fintype.prod_subtype_mul_prod_subtype grid]
  apply congrArg₂ (fun a b : ℝ => a * b)
  · exact Finset.prod_congr rfl (fun a _ =>
      allocatedPhysicalGridDensityFactor_eq B U b hR hσ S x u v rows v₀ pivot hpivot a _)
  · exact Finset.prod_congr rfl (fun a _ =>
      congrFun (allocatedPhysicalLongDensityFactor_eq B U b hR hσ S x u v rows s hA pivot hpivot hσ1 a) _)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module
open scoped BigOperators Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (O : Fin m → Type*) [∀ j, Fintype (O j)]

noncomputable def allocatedFrozenJetReference : Measure (AllocatedFrozenJetRows B U b S O) :=
  Measure.pi (fun a : {a // allocatedGridAxis (I := I) U b S.value a} =>
    coefficientJetAxisReference O a.val)

instance allocatedFrozenJetReference_sigmaFinite : SigmaFinite (allocatedFrozenJetReference B U b S O) := by
  unfold allocatedFrozenJetReference
  infer_instance

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable (rows : ∀ j, O j → Finset α)

theorem allocatedGridJetFactor_probability_data
    (a : {a // allocatedGridAxis (I := I) U b S.value a}) :
    Integrable (allocatedGridJetFactor B U b hR hσ S x u v rows a)
      (coefficientJetAxisReference O a.val) ∧
    (∫ z, allocatedGridJetFactor B U b hR hσ S x u v rows a z
      ∂coefficientJetAxisReference O a.val) = 1 := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · change Integrable _ (Measure.count : Measure (O j → ℤ)) ∧
      (∫ z : O j → ℤ, _ ∂Measure.count) = 1
    exact ⟨pmf_real_integrable _, pmf_real_integral_count _⟩

theorem allocatedGridJetFactor_law
    (a : {a // allocatedGridAxis (I := I) U b S.value a}) :
    (allocatedCoefficientAxisLaw B U b hR hσ S a.val).map
      (coefficientJetAxisMap (allocatedPartitionedJetMatrix B U b S x u v rows) a.val) =
      realDensityMeasure (coefficientJetAxisReference O a.val)
        (allocatedGridJetFactor B U b hR hσ S x u v rows a) := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · change (Measure.pi (fun e => (allocatedLayerIntegerPMFs B U b hR hσ S j i e).toMeasure)).map
        (fun c => allocatedPartitionedJetMatrix B U b S x u v rows j *ᵥ c) =
      realDensityMeasure Measure.count (fun z =>
        (integerMatrixImagePMF _ (allocatedLayerIntegerPMFs B U b hR hσ S j i) z).toReal)
    rw [← pmf_realDensity_count, allocatedPartitionedJetMatrix_eq_physical]
    exact integerMatrixImagePMF_law _ _

theorem allocatedGridJetDensity_probability_data :
    Integrable (allocatedGridJetDensity B U b hR hσ S x u v rows)
      (allocatedFrozenJetReference B U b S O) ∧
    (∫ z, allocatedGridJetDensity B U b hR hσ S x u v rows z
      ∂allocatedFrozenJetReference B U b S O) = 1 := by
  have hp := allocatedGridJetFactor_probability_data B U b S O hR hσ x u v rows
  refine ⟨Integrable.fintype_prod_dep (fun a => (hp a).1), ?_⟩
  change (∫ z, (∏ a, allocatedGridJetFactor B U b hR hσ S x u v rows a (z a))
    ∂Measure.pi (fun a : {a // allocatedGridAxis (I := I) U b S.value a} =>
      coefficientJetAxisReference O a.val)) = 1
  rw [integral_fintype_prod_eq_prod]
  exact Finset.prod_eq_one (fun a _ => (hp a).2)

theorem allocatedGridJetDensity_law :
    (allocatedFrozenCoefficientSource B U b hR hσ S).map
      (allocatedFrozenJetMap B U b S x u v rows) =
      realDensityMeasure (allocatedFrozenJetReference B U b S O)
        (allocatedGridJetDensity B U b hR hσ S x u v rows) := by
  let : ∀ a : {a // allocatedGridAxis (I := I) U b S.value a},
      IsProbabilityMeasure (allocatedCoefficientAxisLaw B U b hR hσ S a.val) :=
    fun a => allocatedCoefficientAxisLaw_probability B U b hR hσ S a.val
  unfold allocatedFrozenCoefficientSource allocatedFrozenJetMap
  rw [Measure.pi_map_pi (fun a =>
    (coefficientJetAxisMap_measurable (allocatedPartitionedJetMatrix B U b S x u v rows) a.val).aemeasurable)]
  simp_rw [allocatedGridJetFactor_law B U b S O hR hσ x u v rows]
  exact realDensityMeasure_pi _ _
    (fun a => (allocatedGridJetFactor_probability_data B U b S O hR hσ x u v rows a).1)
    (fun a z => (allocatedGridJetFactor_mem_Icc B U b hR hσ S x u v rows a z).1)

end Erdos3.VectorPolynomial

end

end OAI
