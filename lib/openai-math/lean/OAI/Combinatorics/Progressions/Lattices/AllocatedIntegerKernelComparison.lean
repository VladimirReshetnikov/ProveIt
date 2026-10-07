import OAI.Combinatorics.Progressions.Estimates.JointPrincipalCoefficientComparison
import OAI.Combinatorics.Progressions.Linear.AllocatedKernelScaleWithCutoff

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U basis S.value a)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))
local notation "fixedInteger" => Sum.elim
  (fun ga : G × Option α => (x (Prod.fst ga) (Prod.snd ga) : ℤ)) (principalTupleIntegers u)

noncomputable def allocatedPartitionedJetMatrix (j : Fin m) :
    Matrix (O j) (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)) ℤ :=
  integerMappedJetMatrix Subtype.val input fixedInteger (rows j) (principalTupleIntegers v)

noncomputable def allocatedIntegerKernelPMF (j : Fin m) (i : Fin (n j)) (hσ1 : σ j ≤ 1)
    (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i) : PMF (O j → ℤ) :=
  (allocatedEnormousProfilePMF B U basis hR hσ S j i hσ1 henormous).map
    (fun a => allocatedPartitionedJetMatrix B U basis S x u v rows j *ᵥ a)

theorem allocatedIntegerKernelPMF_law [∀ j, Fintype (O j)]
    (j : Fin m) (i : Fin (n j)) (hσ1 : σ j ≤ 1)
    (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i) :
    (allocatedCoefficientAxisLaw B U basis hR hσ S ⟨j, Sum.inr i⟩).map
      (fun a => allocatedPartitionedJetMatrix B U basis S x u v rows j *ᵥ a) =
      (allocatedIntegerKernelPMF B U basis hR hσ S x u v rows j i hσ1 henormous).toMeasure :=
  allocatedEnormous_image_law B U basis hR hσ S j i hσ1 henormous
    (allocatedPartitionedJetMatrix B U basis S x u v rows j)

variable (j : Fin m) (i : Fin (n j)) (hσ1 : σ j ≤ 1)
variable (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i)

local notation "centers" => allocatedIntegerProfileCenters (G := G) B R j i
local notation "widths" => allocatedIntegerProfileWidths (G := G) B R σ j i
local notation "scales" => allocatedIntegerProfileScales B U basis S j i
local notation "reindex" => allocatedKernelCoefficientEquiv (G := G) B j

theorem allocatedIntegerKernelPMF_reindexed :
    allocatedIntegerKernelPMF B U basis hR hσ S x u v rows j i hσ1 henormous =
      coefficientImagePMF
        (Matrix.fromCols (scalarKernelIntegerJet x (j.val+1) (rows j))
          (integerMappedJetMatrix (allocatedNonkernelExponent B j) input fixedInteger (rows j)
            (principalTupleIntegers v)))
        (affineProductProfile (centers ∘ reindex) (widths ∘ reindex))
        (affineProductProfile_nonneg _ _ (fun d => allocatedIntegerProfileWidths_pos B hR hσ j i (reindex d)))
        (scales ∘ reindex) (fun d => allocatedIntegerProfileScales_pos B U basis S j i (reindex d))
        (affineProductProfile_zero_outside _ _
          (fun d => allocatedIntegerProfileWidths_pos B hR hσ j i (reindex d)) (hR j).le
          (fun d => allocatedKernelProfile_bound B hR hσ j i hσ1 (reindex d)))
        (allocatedKernelProfile_sum_pos B U basis hR hσ S j i hσ1 henormous) := by
  have he := coefficientImagePMF_affine_reindex (allocatedPartitionedJetMatrix B U basis S x u v rows j)
    reindex centers widths scales (allocatedIntegerProfileWidths_pos B hR hσ j i)
    (allocatedIntegerProfileScales_pos B U basis S j i) (hR j).le
    (allocatedKernelProfile_bound B hR hσ j i hσ1)
    (allocatedEnormous_profile_sum_pos B U basis hR hσ S j i hσ1 henormous)
  change coefficientImagePMF ((integerMappedJetMatrix _ _ _ _ _).submatrix id reindex) _ _ _ _ _ _ = _ at he
  rw [allocatedKernelJet_split B U basis S j x (principalTupleIntegers u) (principalTupleIntegers v) (rows j)] at he
  exact he.symm

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable (j : Fin m) (i : Fin (n j))

local notation "unitWidth" => allocatedUnitProfileWidth (R j) (σ j)
  (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)))

include hR in
theorem allocatedIntegerProfileWidths_floor (d) :
    unitWidth ≤ allocatedIntegerProfileWidths (G := G) B R σ j i d :=
  allocatedUnitProfileWidth_le _ _ (hR j) d

local notation "centers" => allocatedIntegerProfileCenters (G := G) B R j i
local notation "widths" => allocatedIntegerProfileWidths (G := G) B R σ j i
local notation "reindex" => allocatedKernelCoefficientEquiv (G := G) B j
local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S

variable {α O : Type*} [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (rows : O → Finset α) (s : O ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ((scalarKernelIntegerJet x (j.val+1) rows).submatrix id s).det ≠ 0)

local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))
local notation "fixedReal" => Sum.elim
  (fun ga : G × Option α => ((x (Prod.fst ga) (Prod.snd ga) : ℤ) : ℝ) / (S.value : ℝ))
  (principalTupleNormalized (principalAxisLength grid sides) u)
local notation "height" => (basisAxisScale (basis j) i : ℝ)
local notation "heightPos" => Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i)
local notation "kernelScale" => kernelJetCoefficientScale G (j.val+1) (S.value : ℝ) height
local notation "pivot" => normalizedPivotEquiv (Matrix.submatrix (scalarKernelIntegerJet x (j.val+1) rows) id s) hA
  (fun o => kernelScale (s o)) (fun _ => height)
  (fun o => kernelJetCoefficientScale_pos G (j.val+1)
    (Nat.cast_pos.mpr (LayerSamplerScale.positive S)) heightPos (s o))
  (fun _ => heightPos)
local notation "free" => matrixSupCLM (normalizedIntegerColumns
  (remainingMatrixColumns (scalarKernelIntegerJet x (j.val+1) rows) s)
  (fun d => kernelScale (Subtype.val d)) (fun _ => height))
local notation "radius" => NNReal.mk (R j) (le_of_lt (hR j))
local notation "delta" => NNReal.mk unitWidth (le_of_lt (allocatedUnitProfileWidth_pos (hR j) (hσ j) _))

noncomputable def allocatedIntegerKernelDensity
    (y : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℝ) :
    (O → ℝ) → ℝ :=
  affineSelectedJetDensity s pivot free (allocatedNonkernelExponent B j) input fixedReal rows
    (centers ∘ reindex) (widths ∘ reindex) y

include hR hσ in
theorem allocatedIntegerKernelDensity_measurable (hσ1 : σ j ≤ 1) :
    Measurable (Function.uncurry (allocatedIntegerKernelDensity B U basis S j i x u rows s hA)) := by
  have hw (d) := allocatedIntegerProfileWidths_pos B hR hσ j i (reindex d)
  have hb (d) := allocatedKernelProfile_bound B hR hσ j i hσ1 (reindex d)
  exact normalizedJetDensity_measurable pivot free (allocatedNonkernelExponent B j) input fixedReal rows
    ((affineProductProfile_contDiff _ _).continuous.comp (selectedCoefficientEquiv_lipschitz s).continuous)
    (affineProductProfile_contDiff _ _).continuous
    (selectedCoefficientProfile_zero_outside s
      (affineProductProfile_zero_outside _ _ (fun d => hw (.inl d)) (hR j).le (fun d => hb (.inl d))))
    (affineProductProfile_zero_outside _ _ (fun d => hw (.inr d)) (hR j).le (fun d => hb (.inr d)))

include hR hσ in
theorem allocatedIntegerKernelDensity_probability_data (hσ1 : σ j ≤ 1)
    (y : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℝ) :
    (∀ z, 0 ≤ allocatedIntegerKernelDensity B U basis S j i x u rows s hA y z) ∧
      Integrable (allocatedIntegerKernelDensity B U basis S j i x u rows s hA y) ∧
      (∫ z, allocatedIntegerKernelDensity B U basis S j i x u rows s hA y z) = 1 :=
  affineSelectedJetDensity_probability_data s pivot free (allocatedNonkernelExponent B j) input fixedReal rows
    (centers ∘ reindex) (widths ∘ reindex)
    (fun d => allocatedIntegerProfileWidths_pos B hR hσ j i (reindex d)) radius
    (fun d => allocatedKernelProfile_bound B hR hσ j i hσ1 (reindex d)) y

include hR hσ in
theorem allocatedIntegerKernelDensity_bounds (hσ1 : σ j ≤ 1) (z : O → ℝ) :
    (∀ y, |allocatedIntegerKernelDensity B U basis S j i x u rows s hA y z| ≤
      pivotKernelCap (UnselectedColumn s) pivot radius
        (delta⁻¹^Fintype.card (BoundedIntegerExponent G (j.val+1)))) ∧
      LipschitzOnWith
        (pivotKernelLip (UnselectedColumn s) pivot radius
          (affineProductProfileLip (BoundedIntegerExponent G (j.val+1)) delta) *
          (Fintype.card (AllocatedNonkernelCoefficient (G := G) B j) *
            polynomialBoxLip
              (Fintype.card (PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
                (α := α) (fun a => ¬grid a))) (j.val+1) (normalizedJetMass α (j.val+1))) * radius)
        (fun y => allocatedIntegerKernelDensity B U basis S j i x u rows s hA y z)
        (Metric.closedBall 0 1) := by
  have hδ : 0 < delta := allocatedUnitProfileWidth_pos (hR j) (hσ j) _
  have he := affineSelectedJetDensity_bounds s pivot free (allocatedNonkernelExponent B j)
    input fixedReal (allocatedPartitionedInput_frozen_bound B U basis S x u) rows
    (allocatedNonkernelExponent_degree B j) (centers ∘ reindex) (widths ∘ reindex)
    (fun d => allocatedIntegerProfileWidths_pos B hR hσ j i (reindex d)) hδ
    (fun d => allocatedIntegerProfileWidths_floor B hR j i (reindex (.inl d))) radius
    (fun d => allocatedKernelProfile_bound B hR hσ j i hσ1 (reindex d)) z
  simpa only [allocatedIntegerKernelDensity, Real.norm_eq_abs] using he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

theorem coefficientImagePMF_congr_scale {I J : Type*} [Fintype J]
    (A : Matrix I J ℤ) (f : (J → ℝ) → ℝ) (hf : ∀ x, 0 ≤ f x)
    {S T : J → ℝ} (hST : S = T) (hS : ∀ j, 0 < S j) (hT : ∀ j, 0 < T j)
    {R : ℝ} (hsupport : ∀ x, R < ‖x‖ → f x = 0)
    (hZS : 0 < coefficientWeightSum f S) (hZT : 0 < coefficientWeightSum f T) :
    coefficientImagePMF A f hf S hS hsupport hZS = coefficientImagePMF A f hf T hT hsupport hZT := by
  subst T
  rfl

end Erdos3

namespace Erdos3.VectorPolynomial

open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α) (j : Fin m)

local notation "grid" => allocatedGridAxis (I := I) U basis (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))
local notation "fixedInteger" => Sum.elim
  (fun ga : G × Option α => (x (Prod.fst ga) (Prod.snd ga) : ℤ)) (principalTupleIntegers u)
local notation "fixedReal" => Sum.elim
  (fun ga : G × Option α => ((x (Prod.fst ga) (Prod.snd ga) : ℤ) : ℝ) / (S.value : ℝ))
  (principalTupleNormalized (principalAxisLength grid sides) u)

noncomputable def allocatedNonkernelJetMatrix
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides) :
    Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) ℤ :=
  integerMappedJetMatrix (allocatedNonkernelExponent B j) input fixedInteger (rows j)
    (principalTupleIntegers v)

noncomputable def allocatedIntegerKernelMask (modulus : ℕ)
    (residue : Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus)) :
    (O j → ℤ) → ℝ :=
  coefficientResidueMultiplier (scalarKernelIntegerJet x (j.val+1) (rows j)) residue

variable (i : Fin (n j)) (s : O j ↪ BoundedIntegerExponent G (j.val+1))
variable (hA : ((scalarKernelIntegerJet x (j.val+1) (rows j)).submatrix id s).det ≠ 0)
variable (hσ1 : σ j ≤ 1) (henormous : S.value^(layerTailDegree m+1) < basisAxisScale (basis j) i)

local notation "height" => (basisAxisScale (basis j) i : ℝ)
local notation "heightPos" => Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i)
local notation "kernelScale" => kernelJetCoefficientScale G (j.val+1) (S.value : ℝ) height
local notation "nonkernelScale" => fun d => height / monomialScale (layerSamplerBox B U basis S)
  (allocatedNonkernelExponent B j d)
local notation "centers" => allocatedIntegerProfileCenters (G := G) B R j i
local notation "widths" => allocatedIntegerProfileWidths (G := G) B R σ j i
local notation "reindex" => allocatedKernelCoefficientEquiv (G := G) B j
local notation "unitWidth" => allocatedUnitProfileWidth (R j) (σ j)
  (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val+1)))
local notation "radius" => NNReal.mk (R j) (le_of_lt (hR j))
local notation "delta" => NNReal.mk unitWidth (le_of_lt (allocatedUnitProfileWidth_pos (hR j) (hσ j) _))

omit [Fintype α] [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)] in
theorem allocatedIntegerKernelPMF_split_scale
    (hZ : 0 < coefficientWeightSum (affineProductProfile (centers ∘ reindex) (widths ∘ reindex))
      (Sum.elim kernelScale nonkernelScale))
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides) :
    allocatedIntegerKernelPMF B U basis hR hσ S x u v rows j i hσ1 henormous =
      coefficientImagePMF
        (Matrix.fromCols (scalarKernelIntegerJet x (j.val+1) (rows j))
          (allocatedNonkernelJetMatrix B U basis S x u rows j v))
        (affineProductProfile (centers ∘ reindex) (widths ∘ reindex))
        (affineProductProfile_nonneg _ _ (fun d => allocatedIntegerProfileWidths_pos B hR hσ j i (reindex d)))
        (Sum.elim kernelScale nonkernelScale)
        (Sum.rec (kernelJetCoefficientScale_pos G (j.val+1) (Nat.cast_pos.mpr S.positive) heightPos)
          (fun _d => div_pos heightPos (monomialScale_pos _
            (fun k => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U basis S k)) _)))
        (affineProductProfile_zero_outside _ _
          (fun d => allocatedIntegerProfileWidths_pos B hR hσ j i (reindex d)) (hR j).le
          (fun d => allocatedKernelProfile_bound B hR hσ j i hσ1 (reindex d))) hZ := by
  apply (allocatedIntegerKernelPMF_reindexed B U basis hR hσ S x u v rows j i hσ1 henormous).trans
  exact coefficientImagePMF_congr_scale _ _ _ (allocatedKernelCoefficientScales_split B U basis S j i) _ _ _ _ _

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]
variable [DecidableEq (BoundedIntegerExponent G (j.val+1))]
variable [DecidableEq (AllocatedNonkernelCoefficient (G := G) B j)]

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedIntegerKernelDensity_of_matrix
    (v : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides) :
    kernelCoefficientDensity (scalarKernelIntegerJet x (j.val+1) (rows j)) s hA
      kernelScale (fun _ => height)
      (kernelJetCoefficientScale_pos G (j.val+1) (Nat.cast_pos.mpr S.positive) heightPos)
      (fun _ => heightPos) (allocatedNonkernelJetMatrix B U basis S x u rows j v) nonkernelScale
      (centers ∘ reindex) (widths ∘ reindex) =
    allocatedIntegerKernelDensity B U basis S j i x u (rows j) s hA
      (principalTupleNormalized (principalAxisLength (fun a => ¬grid a) sides) v) := by
  have hn := integerMappedCubeTuple_normalized input fixedInteger (principalTupleIntegers v) fixedReal
    (principalTupleNormalized (principalAxisLength (fun a => ¬grid a) sides) v)
    (layerSamplerBox B U basis S) (allocatedPartitionedInput_normalized B U basis S x u v)
  have he := kernelCoefficientDensity_eq_jet (scalarKernelIntegerJet x (j.val+1) (rows j)) s hA
    kernelScale (kernelJetCoefficientScale_pos G (j.val+1) (Nat.cast_pos.mpr S.positive) heightPos)
    heightPos (allocatedNonkernelExponent B j) input fixedReal (rows j)
    (principalTupleNormalized (principalAxisLength (fun a => ¬grid a) sides) v)
    (integerMappedCubeTuple input fixedInteger (principalTupleIntegers v)) (layerSamplerBox B U basis S)
    hn (centers ∘ reindex) (widths ∘ reindex)
  refine he.trans ?_
  unfold allocatedIntegerKernelDensity
  congr 3
  exact Subsingleton.elim _ _

theorem allocatedIntegerKernel_residue_family
    (p : FiniteProbabilityWeights (PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides))
    (modulus : ℕ)
    (residue : Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (hperiod : integerScalarLattice (O j) (modulus : ℤ) ≤
      (scalarKernelIntegerJet x (j.val+1) (rows j)).mulVecLin.range)
    (hresidue : ∀ v, p.weight v ≠ 0 →
      integerResidueMatrix (allocatedNonkernelJetMatrix B U basis S x u rows j v) modulus = residue)
    {C V M b t ε : ℝ} (hC0 : 0 ≤ C) (hV0 : 0 ≤ V) (hM0 : 0 ≤ M)
    (ctrl : ∀ v, p.weight v ≠ 0 → CoefficientFiberControl
      (Matrix.fromCols (scalarKernelIntegerJet x (j.val+1) (rows j))
        (allocatedNonkernelJetMatrix B U basis S x u rows j v))
      (s.trans Function.Embedding.inl) (Sum.elim kernelScale nonkernelScale)
      height S.value (j.val+1) C V M)
    (hb : 0 ≤ b) (ht : 0 ≤ t) (hε : 0 < ε)
    (hM : M ≤ Real.exp b) (hV : V ≤ Real.exp b) (hC : C ≤ Real.exp b)
    (hRb : R j ≤ Real.exp b) (hwidth : unitWidth⁻¹ ≤ Real.exp t)
    (hlarge : coefficientReplacementScale
      (J := BoundedIntegerExponent G (j.val+1) ⊕ AllocatedNonkernelCoefficient (G := G) B j)
      (s.trans Function.Embedding.inl) b t ε S.value (j.val+1) ≤ height) :
    (∀ z, 0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus residue z ∧
      allocatedIntegerKernelMask B U basis S x rows j modulus residue z ≤ M) ∧
    ∀ v, p.weight v ≠ 0 → ∀ z,
      |height^Fintype.card (O j) *
          (allocatedIntegerKernelPMF B U basis hR hσ S x u v rows j i hσ1 henormous z).toReal -
        allocatedIntegerKernelMask B U basis S x rows j modulus residue z *
          allocatedIntegerKernelDensity B U basis S j i x u (rows j) s hA
            (principalTupleNormalized (principalAxisLength (fun a => ¬grid a) sides) v)
            (fun o => (z o : ℝ)/height)| ≤ ε := by
  have hscale := kernelJetCoefficientScale_pos G (j.val+1) (Nat.cast_pos.mpr S.positive) heightPos
  have hT d : 0 < nonkernelScale d := div_pos heightPos
    (monomialScale_pos _ (fun k => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U basis S k)) _)
  obtain ⟨hZ, hm, he⟩ := affineCoefficientImage_residue_family p
    (scalarKernelIntegerJet x (j.val+1) (rows j)) s hA
    (allocatedNonkernelJetMatrix B U basis S x u rows j) kernelScale nonkernelScale hscale hT
    (j.val+1) ctrl (Nat.cast_pos.mpr S.positive) heightPos hC0 hV0 hM0
    (centers ∘ reindex) (widths ∘ reindex)
    (fun d => allocatedIntegerProfileWidths_pos B hR hσ j i (reindex d))
    (show 0 < delta from allocatedUnitProfileWidth_pos (hR j) (hσ j) _)
    (fun d => allocatedIntegerProfileWidths_floor B hR j i (reindex d)) radius
    (fun d => allocatedKernelProfile_bound B hR hσ j i hσ1 (reindex d))
    hb ht hε hM hV hC hRb hwidth hlarge modulus residue hperiod hresidue
  refine ⟨hm, ?_⟩
  intro v hv z
  rw [allocatedIntegerKernelPMF_split_scale B U basis hR hσ S x u rows j i hσ1 henormous hZ v,
    ← allocatedIntegerKernelDensity_of_matrix B U basis S x u rows j i s hA v]
  exact he v hv z

end Erdos3.VectorPolynomial

end

end OAI
