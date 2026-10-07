import OAI.Combinatorics.Progressions.Estimates.AllocatedPhysicalLongImage
import OAI.Combinatorics.Progressions.Lattices.AllocatedWholeResidueShift

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical Matrix

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v w : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "root" v => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x (principalAxisJoin grid u v)
local notation "dirs" v => allocatedPhysicalCubeDirections B U b S x (principalAxisJoin grid u v)

omit [∀ j, Fintype (O j)] in
theorem allocatedPartitionedJetMatrix_kernel_range_le (j : Fin m) :
    (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range ≤
      (allocatedPartitionedJetMatrix B U b S x u v rows j).mulVecLin.range := by
  have he := allocatedKernelJet_full_image B U b S j x
    (principalTupleIntegers u) (principalTupleIntegers v) (rows j)
  change _ = (allocatedPartitionedJetMatrix B U b S x u v rows j).mulVecLin.range at he
  rw [← he, integerMatrix_fromCols_range]
  exact le_sup_left

theorem allocatedPartitionedJetMatrix_image_eq_of_residue (M : ℕ)
    (hperiod : ∀ j, integerScalarLattice (O j) (M : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (hvw : principalResidueLabel M v = principalResidueLabel M w) (j : Fin m) :
    (allocatedPartitionedJetMatrix B U b S x u v rows j).mulVecLin.range =
      (allocatedPartitionedJetMatrix B U b S x u w rows j).mulVecLin.range := by
  apply integerMatrixImage_eq_of_residueMatrix _ _ M
  · exact (hperiod j).trans (allocatedPartitionedJetMatrix_kernel_range_le B U b S x u v rows j)
  · exact (hperiod j).trans (allocatedPartitionedJetMatrix_kernel_range_le B U b S x u w rows j)
  · apply integerMappedJetMatrix_residue
    exact congrArg principalTupleResidues hvw

theorem allocatedPhysicalDeckJet_law_eq_of_residue
    (Q : Fin m → Type*) [∀ j, Fintype (Q j)] (M : ℕ)
    (hperiod : ∀ j, integerScalarLattice (O j) (M : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (hvw : principalResidueLabel M v = principalResidueLabel M w) (d : ℕ) [NeZero d] :
    (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)).map
      (coefficientDeckJetMap (root v) (dirs v) rows d) =
      (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)).map
        (coefficientDeckJetMap (root w) (dirs w) rows d) := by
  have hr (j : Fin m) :
      (boundedCoefficientJetMatrix (root v) (dirs v) (j.val + 1) (rows j)).mulVecLin.range =
        (boundedCoefficientJetMatrix (root w) (dirs w) (j.val + 1) (rows j)).mulVecLin.range := by
    rw [← allocatedPartitionedJetMatrix_eq_physical B U b S x u v rows j,
      ← allocatedPartitionedJetMatrix_eq_physical B U b S x u w rows j]
    exact allocatedPartitionedJetMatrix_image_eq_of_residue B U b S x u v w rows M hperiod hvw j
  exact uniformPMF_map_hom_eq_of_range_eq _ _
    (coefficientDeckJetMap_range_eq_of_integer_range_eq
      (α := α) (K := LayerSamplerVariables G I n B) (O := O) (B := Q)
      (root v) (dirs v) rows (root w) (dirs w) hr d)

theorem allocatedPhysicalDeckJet_joint_law_eq_of_residue
    (Q : Fin m → Type*) [∀ j, Fintype (Q j)] (M : ℕ)
    (hperiod : ∀ j, integerScalarLattice (O j) (M : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (hvw : principalResidueLabel M v = principalResidueLabel M w) (d : ℕ) [NeZero d]
    {X : Type*} [MeasurableSpace X] (ρ : Measure X) [SFinite ρ] :
    (ρ.prod (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)).toMeasure).map
      (fun p => (p.1, coefficientDeckJetMap (root v) (dirs v) rows d p.2)) =
      (ρ.prod (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)).toMeasure).map
        (fun p => (p.1, coefficientDeckJetMap (root w) (dirs w) rows d p.2)) := by
  calc
    _ = ρ.prod ((PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)).map
        (coefficientDeckJetMap (root v) (dirs v) rows d)).toMeasure :=
      uniformPMF_product_image ρ (coefficientDeckJetMap (root v) (dirs v) rows d)
    _ = ρ.prod ((PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)).map
        (coefficientDeckJetMap (root w) (dirs w) rows d)).toMeasure :=
      congrArg (fun p : PMF (∀ j, O j → Q j → ZMod d) => ρ.prod p.toMeasure)
        (allocatedPhysicalDeckJet_law_eq_of_residue B U b S x u v w rows Q M hperiod hvw d)
    _ = _ := (uniformPMF_product_image ρ (coefficientDeckJetMap (root w) (dirs w) rows d)).symm

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped Matrix Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable (y y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] (rows : ∀ j, O j → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U b S.value
local notation "root" z => allocatedPhysicalCubeRoot B U b S (fun _ => 0) x z
local notation "dirs" z => allocatedPhysicalCubeDirections B U b S x z

omit [∀ j, Fintype (O j)] in
theorem allocatedWholeJetMatrix_kernel_range_le (j : Fin m) :
    (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range ≤
      (boundedCoefficientJetMatrix (root y) (dirs y) (j.val + 1) (rows j)).mulVecLin.range := by
  have h := allocatedPartitionedJetMatrix_kernel_range_le B U b S x
    (principalAxisRestrict grid y) (principalAxisRestrict (fun a => ¬grid a) y) rows j
  rw [allocatedPartitionedJetMatrix_eq_physical, principalAxisJoin_restrict] at h
  exact h

omit [∀ j, Fintype (O j)] in
theorem allocatedWholeJetMatrix_residue (M : ℕ)
    (hlabel : principalResidueLabel M y = principalResidueLabel M y₀) (j : Fin m) :
    integerResidueMatrix (boundedCoefficientJetMatrix (root y) (dirs y) (j.val + 1) (rows j)) M =
      integerResidueMatrix (boundedCoefficientJetMatrix (root y₀) (dirs y₀) (j.val + 1) (rows j)) M := by
  have h := allocatedPhysicalCube_residue_of_whole_label B U b S (fun _ => 0) x y y₀ M hlabel
  have hroot : integerResidueMap _ M (root y) = integerResidueMap _ M (root y₀) := by
    funext k
    exact congrFun (congrFun h (.inl ())) (some k)
  have hdirs : integerResidueMatrix (dirs y) M = integerResidueMatrix (dirs y₀) M := by
    funext i k
    exact congrFun (congrFun h (.inr i)) (some k)
  apply integerJetMatrix_residue_eq
  intro _ t _
  exact integerAffineCube_residue_eq _ _ _ _ M hroot hdirs t

theorem allocatedWholeJetMatrix_image_eq (M : ℕ)
    (hperiod : ∀ j, integerScalarLattice (O j) (M : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (hlabel : principalResidueLabel M y = principalResidueLabel M y₀) (j : Fin m) :
    (boundedCoefficientJetMatrix (root y) (dirs y) (j.val + 1) (rows j)).mulVecLin.range =
      (boundedCoefficientJetMatrix (root y₀) (dirs y₀) (j.val + 1) (rows j)).mulVecLin.range := by
  exact integerMatrixImage_eq_of_residueMatrix _ _ M
    ((hperiod j).trans (allocatedWholeJetMatrix_kernel_range_le B U b S x y rows j))
    ((hperiod j).trans (allocatedWholeJetMatrix_kernel_range_le B U b S x y₀ rows j))
    (allocatedWholeJetMatrix_residue B U b S x y y₀ rows M hlabel j)

omit [∀ j, Fintype (O j)] in
theorem allocatedWholeNonkernelJetMatrix_eq (j : Fin m) :
    allocatedNonkernelJetMatrix B U b S x (principalAxisRestrict grid y) rows j
      (principalAxisRestrict (fun a => ¬grid a) y) =
    (boundedCoefficientJetMatrix (root y) (dirs y) (j.val + 1) (rows j)).submatrix id Subtype.val := by
  have he := allocatedPartitionedJetMatrix_eq_physical B U b S x
    (principalAxisRestrict grid y) (principalAxisRestrict (fun a => ¬grid a) y) rows j
  rw [principalAxisJoin_restrict] at he
  rw [← he]
  rfl

omit [∀ j, Fintype (O j)] in
theorem allocatedWholeNonkernelJetMatrix_residue (M : ℕ)
    (hlabel : principalResidueLabel M y = principalResidueLabel M y₀) (j : Fin m) :
    integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x (principalAxisRestrict grid y)
      rows j (principalAxisRestrict (fun a => ¬grid a) y)) M =
    integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x (principalAxisRestrict grid y₀)
      rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) M := by
  rw [allocatedWholeNonkernelJetMatrix_eq, allocatedWholeNonkernelJetMatrix_eq]
  have h := allocatedWholeJetMatrix_residue B U b S x y y₀ rows M hlabel j
  funext o k
  exact congrFun (congrFun h o) k.val

theorem allocatedWholeDeckJet_law_eq (Q : Fin m → Type*) [∀ j, Fintype (Q j)] (M : ℕ)
    (hperiod : ∀ j, integerScalarLattice (O j) (M : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range)
    (hlabel : principalResidueLabel M y = principalResidueLabel M y₀) (d : ℕ) [NeZero d] :
    (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)).map
      (coefficientDeckJetMap (root y) (dirs y) rows d) =
    (PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)).map
      (coefficientDeckJetMap (root y₀) (dirs y₀) rows d) := by
  exact uniformPMF_map_hom_eq_of_range_eq _ _
    (coefficientDeckJetMap_range_eq_of_integer_range_eq
      (α := α) (K := LayerSamplerVariables G I n B) (O := O) (B := Q)
      (root y) (dirs y) rows (root y₀) (dirs y₀)
      (allocatedWholeJetMatrix_image_eq B U b S x y y₀ rows M hperiod hlabel) d)

end Erdos3.VectorPolynomial

end

end OAI
