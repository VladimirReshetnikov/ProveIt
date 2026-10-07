/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Measurable
import OAI.Combinatorics.Progressions.Linear.AllocatedFixedKernelCover
import OAI.Combinatorics.Progressions.Probability.AllocatedLongJetMixture

namespace OAI

section

namespace Erdos3

theorem integerMappedJetMatrix_eq_boundedCoefficient {Z X K α O : Type*}
    [DecidableEq α] [Fintype K] (h : ℕ) (input : K → Option α → Z ⊕ X)
    (z : Z → ℤ) (rows : O → Finset α) (x : X → ℤ) :
    integerMappedJetMatrix (fun e : VectorPolynomial.BoundedCoefficientExponent K h => e.val)
      input z rows x =
      boundedCoefficientJetMatrix (fun k => Sum.elim z x (input k none))
        (fun i k => Sum.elim z x (input k (some i))) h rows := rfl

noncomputable def translatedIntegerMappedJetMatrix {Z X K α O N : Type*} [DecidableEq α]
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℤ)
    (rows : O → Finset α) (x : X → ℤ) (c : K → ℤ) : Matrix O N ℤ :=
  integerJetMatrix (fun n => MvPolynomial.monomial (e n) 1)
    (fun t k => c k + integerMappedCubeTuple input z x t k) rows

theorem translatedIntegerMappedJetMatrix_zero {Z X K α O N : Type*} [DecidableEq α]
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℤ)
    (rows : O → Finset α) (x : X → ℤ) :
    translatedIntegerMappedJetMatrix e input z rows x (fun _ => 0) =
      integerMappedJetMatrix e input z rows x := by
  simp only [translatedIntegerMappedJetMatrix, zero_add, integerMappedJetMatrix]

theorem translatedIntegerMappedJetMatrix_eq_boundedCoefficient {Z X K α O : Type*}
    [DecidableEq α] [Fintype K] (h : ℕ) (input : K → Option α → Z ⊕ X)
    (z : Z → ℤ) (rows : O → Finset α) (x : X → ℤ) (c : K → ℤ) :
    translatedIntegerMappedJetMatrix (fun e : VectorPolynomial.BoundedCoefficientExponent K h => e.val)
      input z rows x c =
      boundedCoefficientJetMatrix (fun k => c k + Sum.elim z x (input k none))
        (fun i k => Sum.elim z x (input k (some i))) h rows := by
  have hv : (fun t k => c k + integerMappedCubeTuple input z x t k) =
      integerAffineCube (fun k => c k + Sum.elim z x (input k none))
        (fun i k => Sum.elim z x (input k (some i))) := by
    funext t k
    simp only [integerMappedCubeTuple, integerAffineCube, add_assoc]
  change integerJetMatrix
      (fun e : VectorPolynomial.BoundedCoefficientExponent K h => MvPolynomial.monomial e.val 1)
      (fun t k => c k + integerMappedCubeTuple input z x t k) rows =
    integerJetMatrix
      (fun e : VectorPolynomial.BoundedCoefficientExponent K h => MvPolynomial.monomial e.val 1)
      (integerAffineCube (fun k => c k + Sum.elim z x (input k none))
        (fun i k => Sum.elim z x (input k (some i)))) rows
  rw [hv]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S

variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} (rows : ∀ j, O j → Finset α)

omit [DecidableEq α] in
theorem allocatedPhysicalCube_mapped_root (c : LayerSamplerVariables G I n B → ℤ) :
    (fun k => c k + Sum.elim (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) (principalTupleIntegers u)) (principalTupleIntegers v) ((partitionedPrincipalInput grid (fun g a => (g, a))) k none)) =
      allocatedPhysicalCubeRoot B U b S c x (principalAxisJoin grid u v) := by
  funext k
  rw [partitionedPrincipalInput_value]
  cases k <;> rfl

omit [DecidableEq α] in
theorem allocatedPhysicalCube_mapped_directions :
    (fun i k => Sum.elim (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) (principalTupleIntegers u)) (principalTupleIntegers v) ((partitionedPrincipalInput grid (fun g a => (g, a))) k (some i))) = (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)) := by
  funext i k
  rw [partitionedPrincipalInput_value]
  cases k <;> rfl

noncomputable def allocatedTranslatedPartitionedJetMatrix
    (c : LayerSamplerVariables G I n B → ℤ) (j : Fin m) :
    Matrix (O j) (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) ℤ :=
  translatedIntegerMappedJetMatrix Subtype.val (partitionedPrincipalInput grid (fun g a => (g, a))) (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) (principalTupleIntegers u)) (rows j) (principalTupleIntegers v) c

theorem allocatedTranslatedPartitionedJetMatrix_eq_physical
    (c : LayerSamplerVariables G I n B → ℤ) (j : Fin m) :
    allocatedTranslatedPartitionedJetMatrix B U b S x u v rows c j =
      boundedCoefficientJetMatrix (allocatedPhysicalCubeRoot B U b S c x (principalAxisJoin grid u v)) (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)) (j.val + 1) (rows j) := by
  unfold allocatedTranslatedPartitionedJetMatrix
  rw [translatedIntegerMappedJetMatrix_eq_boundedCoefficient,
    allocatedPhysicalCube_mapped_root, allocatedPhysicalCube_mapped_directions]

theorem allocatedPartitionedJetMatrix_eq_physical (j : Fin m) :
    allocatedPartitionedJetMatrix B U b S x u v rows j =
      boundedCoefficientJetMatrix (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v))
        (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)) (j.val + 1) (rows j) := by
  rw [← allocatedTranslatedPartitionedJetMatrix_eq_physical B U b S x u v rows (fun _ => 0) j]
  exact (translatedIntegerMappedJetMatrix_zero _ (partitionedPrincipalInput grid (fun g a => (g, a))) (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) (principalTupleIntegers u)) (rows j) (principalTupleIntegers v)).symm

theorem allocatedPhysicalJetMatrix_kernel (j : Fin m) :
    (boundedCoefficientJetMatrix (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v))
      (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)) (j.val + 1) (rows j)).submatrix id
      (kernelExponentEmbedding G (PrincipalTupleIndex B (layerSamplerDegree I n)) (j.val + 1)) =
      scalarKernelIntegerJet x (j.val + 1) (rows j) := by
  rw [← allocatedPartitionedJetMatrix_eq_physical B U b S x u v rows j]
  exact integerMappedJetMatrix_kernel _ (partitionedPrincipalInput grid (fun g a => (g, a))) (Sum.elim (fun ga : G × Option α => (x ga.1 ga.2 : ℤ)) (principalTupleIntegers u)) (principalTupleIntegers v) x (fun _ _ => rfl) (rows j)

theorem allocatedPhysicalJetMatrix_pivot (j : Fin m)
    (s : O j ↪ BoundedIntegerExponent G (j.val + 1)) :
    (boundedCoefficientJetMatrix (allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v))
      (allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)) (j.val + 1) (rows j)).submatrix id
      (s.trans (kernelExponentEmbedding G (PrincipalTupleIndex B (layerSamplerDegree I n)) (j.val + 1))) =
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id s := by
  rw [← allocatedPhysicalJetMatrix_kernel B U b S x u v rows j]
  rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "split" => allocatedCoefficientSplit B U b S
local notation "source" => allocatedCoefficientSource B U b hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U b hR hσ S
local notation "longSource" => allocatedLongCoefficientSource B U b hR hσ S

variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

local notation "joined" => principalAxisJoin grid u v
local notation "root" => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x joined
local notation "dirs" => allocatedPhysicalCubeDirections B U b S x joined

noncomputable def allocatedPhysicalLongJetMap
    (a : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n) :
    AllocatedLongJetRows B U b S O :=
  fun i => coefficientJetAxisEquiv O I n (canonicalCoefficientJetArrays root dirs rows a) i.val

omit [Fintype α] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
theorem allocatedPhysicalLongJetMap_measurable :
    Measurable (allocatedPhysicalLongJetMap B U b S x u v rows) :=
  Measurable.of_eval (fun i => (measurable_pi_apply i.val).comp
    ((coefficientJetAxisEquiv O I n).measurable.comp
      (canonicalCoefficientJetArrays_measurable root dirs rows)))

omit [Fintype α] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
theorem allocatedPhysicalLongJetMap_reconstruct
    (a₀ : AllocatedFrozenCoefficients B U b S) (a₁ : AllocatedLongCoefficients B U b S) :
    allocatedPhysicalLongJetMap B U b S x u v rows ((split).symm (a₀, a₁)) =
      allocatedLongJetMap B U b S x u v rows a₁ := by
  have hmatrix : (fun j => boundedCoefficientJetMatrix root dirs (j.val + 1) (rows j)) =
      allocatedPartitionedJetMatrix B U b S x u v rows :=
    funext (fun j => (allocatedPartitionedJetMatrix_eq_physical B U b S x u v rows j).symm)
  funext i
  change coefficientJetAxisEquiv O I n (canonicalCoefficientJetArrays root dirs rows _) i.val = _
  rw [canonicalCoefficientJetArrays_axis, hmatrix, allocatedCoefficientReconstruct_long]
  rfl

omit [Fintype α] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
theorem allocatedPhysicalLongJetMap_split
    (a : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n) :
    allocatedPhysicalLongJetMap B U b S x u v rows a =
      allocatedLongJetMap B U b S x u v rows (split a).2 := by
  simpa only [Prod.mk.eta, MeasurableEquiv.symm_apply_apply] using
    allocatedPhysicalLongJetMap_reconstruct B U b S x u v rows (split a).1 (split a).2

variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)

theorem allocatedPhysicalLongJetMap_joint_law :
    (source).map (fun a => ((split a).1, allocatedPhysicalLongJetMap B U b S x u v rows a)) =
      (frozenSource).prod
        (realDensityMeasure (allocatedLongJetReference B U b S O)
          (allocatedLongJetDensity B U b hR hσ S x u v rows s hA hσ1)) := by
  let : IsProbabilityMeasure frozenSource := allocatedFrozenCoefficientSource_probability B U b hR hσ S
  let : IsProbabilityMeasure longSource := allocatedLongCoefficientSource_probability B U b hR hσ S
  have he : (fun a => ((split a).1, allocatedPhysicalLongJetMap B U b S x u v rows a)) =
      (Prod.map id (allocatedLongJetMap B U b S x u v rows)) ∘ split := by
    funext a
    exact congrArg (fun z => ((split a).1, z)) (allocatedPhysicalLongJetMap_split B U b S x u v rows a)
  rw [he, ← Measure.map_map (measurable_id.prodMap (allocatedLongJetMap_measurable B U b S x u v rows))
    (split).measurable, (allocatedCoefficientSplit_measurePreserving B U b hR hσ S).map_eq]
  rw [← Measure.map_prod_map _ _ measurable_id (allocatedLongJetMap_measurable B U b S x u v rows),
    Measure.map_id, allocatedLongJetDensity_law B U b hR hσ S x u v rows s hA hσ1]

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]

theorem allocatedPhysicalLongJet_variable_test_mean
    (w : FiniteProbabilityWeights (PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides))
    (φ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides →
      AllocatedFrozenCoefficients B U b S → AllocatedLongJetRows B U b S O → ℂ)
    (hφ : ∀ v, Measurable (fun p : AllocatedFrozenCoefficients B U b S × AllocatedLongJetRows B U b S O =>
      φ v p.1 p.2)) {C : ℝ} (hbound : ∀ v a z, ‖φ v a z‖ ≤ C) :
    (∫ a, w.complexMean (fun v => φ v (split a).1
      (allocatedPhysicalLongJetMap B U b S x u v rows a)) ∂source) =
      ∫ a₀, ∫ z, w.complexMean (fun v =>
        (allocatedLongJetDensity B U b hR hσ S x u v rows s hA hσ1 z : ℂ) * φ v a₀ z)
        ∂allocatedLongJetReference B U b S O ∂frozenSource := by
  classical
  let : IsProbabilityMeasure frozenSource := allocatedFrozenCoefficientSource_probability B U b hR hσ S
  let : IsProbabilityMeasure longSource := allocatedLongCoefficientSource_probability B U b hR hσ S
  have hi : Integrable (fun a : AllocatedFrozenCoefficients B U b S × AllocatedLongCoefficients B U b S =>
      w.complexMean (fun v => φ v a.1 (allocatedLongJetMap B U b S x u v rows a.2)))
      ((frozenSource).prod longSource) := by
    apply w.complexMean_integrable
    intro v
    exact (integrable_const C).mono'
      ((hφ v).comp (measurable_fst.prodMk
        ((allocatedLongJetMap_measurable B U b S x u v rows).comp measurable_snd))).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun a => hbound v a.1 _))
  calc
    _ = ∫ a, w.complexMean (fun v => φ v (split ((split).symm a)).1
        (allocatedPhysicalLongJetMap B U b S x u v rows ((split).symm a))) ∂((frozenSource).prod longSource) :=
      (allocatedCoefficientReconstruct_measurePreserving B U b hR hσ S).integral_comp' _ |>.symm
    _ = ∫ a₀, ∫ a₁, w.complexMean (fun v => φ v a₀
        (allocatedLongJetMap B U b S x u v rows a₁)) ∂longSource ∂frozenSource := by
      simp only [allocatedPhysicalLongJetMap_split, MeasurableEquiv.apply_symm_apply]
      exact integral_prod _ hi
    _ = _ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro a₀
      exact allocatedLongJet_variable_test_mean B U b hR hσ S x u rows s hA hσ1 w
        (fun v => φ v a₀) (fun v => (hφ v).comp (measurable_const.prodMk measurable_id))
        (fun v z => hbound v a₀ z)

end Erdos3.VectorPolynomial

end

end OAI
