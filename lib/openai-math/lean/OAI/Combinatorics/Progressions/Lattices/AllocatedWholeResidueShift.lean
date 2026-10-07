import OAI.Combinatorics.Progressions.Estimates.AllocatedTrimmedVectorSite

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)

local notation "vars" => LayerSamplerVariables G I n B
local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S

omit [Fintype α] [DecidableEq α] in
theorem allocatedPhysicalCube_coefficient_entry_bound
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) α sides)
    (i : Unit ⊕ α) (k : Option vars) :
    |(physicalCubeCoefficient (allocatedPhysicalCubeRoot B U basis S c x y)
      (allocatedPhysicalCubeDirections B U basis S x y) i k : ℝ)| ≤
        allocatedPhysicalEntryBudget B U basis S c := by
  cases k with
  | none =>
    cases i with
    | inl i =>
      simpa only [physicalCubeCoefficient, Int.cast_one, abs_one] using
        allocatedPhysicalEntryBudget_one_le B U basis S c
    | inr i =>
      simpa only [physicalCubeCoefficient, Int.cast_zero, abs_zero] using
        zero_le_one.trans (allocatedPhysicalEntryBudget_one_le B U basis S c)
  | some k =>
    cases i with
    | inl i => exact allocatedPhysicalCube_root_entry_bound B U basis S c x y k
    | inr i => exact allocatedPhysicalCube_direction_entry_bound B U basis S c x y i k

omit [Fintype α] [DecidableEq α] in
theorem allocatedPhysicalCube_residue_of_principal_label
    (u : PrincipalAxisTuples (α := α) grid sides)
    (w w₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    (modulus : ℕ) (hlabel : principalResidueLabel modulus w = principalResidueLabel modulus w₀) :
    integerResidueMatrix (physicalCubeCoefficient
      (allocatedPhysicalCubeRoot B U basis S c x (principalAxisJoin grid u w))
      (allocatedPhysicalCubeDirections B U basis S x (principalAxisJoin grid u w))) modulus =
    integerResidueMatrix (physicalCubeCoefficient
      (allocatedPhysicalCubeRoot B U basis S c x (principalAxisJoin grid u w₀))
      (allocatedPhysicalCubeDirections B U basis S x (principalAxisJoin grid u w₀))) modulus := by
  have hc : integerResidueMatrix (principalSpatialColumns (fun j => c (Sum.inr j)) id
      (principalAxisJoin grid u w)) modulus =
    integerResidueMatrix (principalSpatialColumns (fun j => c (Sum.inr j)) id
      (principalAxisJoin grid u w₀)) modulus := by
    rw [principalSpatialColumns_join_residue, principalSpatialColumns_join_residue, hlabel]
  ext i k
  cases k with
  | none => cases i <;> rfl
  | some k =>
    cases k with
    | inl g => cases i <;> rfl
    | inr j =>
      cases i with
      | inl i => exact congrFun (congrFun hc (.inl i)) j
      | inr i => exact congrFun (congrFun hc (.inr i)) j

omit [Fintype α] [DecidableEq α] in
theorem allocatedPhysicalResidue_shift_principal
    (y y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α sides)
    {X : Type*} (r : Option vars × X → ℤ) (q : X → ℕ) :
    physicalResidueOffsetShift (allocatedPhysicalCubeRoot B U basis S c x y)
      (allocatedPhysicalCubeRoot B U basis S c x y₀)
      (allocatedPhysicalCubeDirections B U basis S x y)
      (allocatedPhysicalCubeDirections B U basis S x y₀) r q =
    fun d => residueMatrixShift (principalSpatialColumns (fun j => c (Sum.inr j)) id y)
      (principalSpatialColumns (fun j => c (Sum.inr j)) id y₀) (q d)
      (fun j => r (some (Sum.inr j), d)) := by
  funext d i
  unfold physicalResidueOffsetShift residueMatrixShift
  congr 1
  simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, Fintype.sum_option,
    Fintype.sum_sum_type, allocatedPhysicalCube_principal_columns]
  cases i <;> simp [physicalCubeCoefficient, allocatedPhysicalCubeRoot, allocatedPhysicalCubeDirections]

omit [DecidableEq α] in
theorem allocatedPhysicalResidue_offset_shift
    (u : PrincipalAxisTuples (α := α) grid sides)
    (w w₀ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides)
    {X : Type*} (base : X → ℤ) (r : Option vars × X → ℤ)
    (q : X → ℕ) (hq : ∀ d, 0 < q d) (period modulus : ℕ)
    (hdiv : ∀ d, q d * period ∣ modulus)
    (hlabel : principalResidueLabel modulus w = principalResidueLabel modulus w₀)
    (hr : ∀ k d, |(r (k, d) : ℝ)| ≤ q d) :
    let root := allocatedPhysicalCubeRoot B U basis S c x (principalAxisJoin grid u w)
    let root₀ := allocatedPhysicalCubeRoot B U basis S c x (principalAxisJoin grid u w₀)
    let dirs := allocatedPhysicalCubeDirections B U basis S x (principalAxisJoin grid u w)
    let dirs₀ := allocatedPhysicalCubeDirections B U basis S x (principalAxisJoin grid u w₀)
    let shift := physicalResidueOffsetShift root root₀ dirs dirs₀ r q
    (∀ d, shift d ∈ integerScalarLattice (Unit ⊕ α) (period : ℤ)) ∧
    (∀ v, physicalResidueReconstruction root dirs base r q v =
      physicalResidueReconstruction root₀ dirs₀ base r q (v + shift)) ∧
    (∀ d i, |(shift d i : ℝ)| ≤
      Fintype.card (Option vars) * (2 * allocatedPhysicalEntryBudget B U basis S c)) := by
  intro root root₀ dirs dirs₀ shift
  have hres (d) : integerResidueMatrix (physicalCubeCoefficient root dirs) (q d * period) =
      integerResidueMatrix (physicalCubeCoefficient root₀ dirs₀) (q d * period) :=
    integerResidueMatrix_reduce _ _ (hdiv d)
      (allocatedPhysicalCube_residue_of_principal_label B U basis S c x u w w₀ modulus hlabel)
  refine ⟨fun d => physicalResidueOffsetShift_mem root root₀ dirs dirs₀ r q hq period hres d,
    fun v => physicalResidueReconstruction_offset_shift root root₀ dirs dirs₀ base r q hq period hres v, ?_⟩
  intro d i
  apply (physicalResidueOffsetShift_bound root root₀ dirs dirs₀ r q hq period hres hr d i).trans
  calc
    _ ≤ ∑ _k : Option vars, 2 * allocatedPhysicalEntryBudget B U basis S c := by
      apply Finset.sum_le_sum
      intro k _
      rw [Int.cast_sub]
      apply (abs_sub _ _).trans
      have h₁ := allocatedPhysicalCube_coefficient_entry_bound B U basis S c x (principalAxisJoin grid u w) i k
      have h₂ := allocatedPhysicalCube_coefficient_entry_bound B U basis S c x (principalAxisJoin grid u w₀) i k
      linarith
    _ = _ := by simp

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (c : LayerSamplerVariables G I n B → ℤ) (x : G → IntegerScalarCubeBox α S.value)

local notation "vars" => LayerSamplerVariables G I n B
local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S

omit [Fintype α] [DecidableEq α] in
theorem allocatedPhysicalCube_residue_of_whole_label
    (y y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α sides)
    (modulus : ℕ) (hlabel : principalResidueLabel modulus y = principalResidueLabel modulus y₀) :
    integerResidueMatrix (physicalCubeCoefficient
      (allocatedPhysicalCubeRoot B U basis S c x y)
      (allocatedPhysicalCubeDirections B U basis S x y)) modulus =
    integerResidueMatrix (physicalCubeCoefficient
      (allocatedPhysicalCubeRoot B U basis S c x y₀)
      (allocatedPhysicalCubeDirections B U basis S x y₀)) modulus := by
  have hc : integerResidueMatrix (principalSpatialColumns (fun j => c (Sum.inr j)) id
      y) modulus =
    integerResidueMatrix (principalSpatialColumns (fun j => c (Sum.inr j)) id
      y₀) modulus := by
    rw [principalSpatialColumns_residue, principalSpatialColumns_residue, hlabel]
  ext i k
  cases k with
  | none => cases i <;> rfl
  | some k =>
    cases k with
    | inl g => cases i <;> rfl
    | inr j =>
      cases i with
      | inl i => exact congrFun (congrFun hc (.inl i)) j
      | inr i => exact congrFun (congrFun hc (.inr i)) j

omit [DecidableEq α] in
theorem allocatedPhysicalResidue_whole_offset_shift
    (y y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α sides)
    {X : Type*} (base : X → ℤ) (r : Option vars × X → ℤ)
    (q : X → ℕ) (hq : ∀ d, 0 < q d) (period modulus : ℕ)
    (hdiv : ∀ d, q d * period ∣ modulus)
    (hlabel : principalResidueLabel modulus y = principalResidueLabel modulus y₀)
    (hr : ∀ k d, |(r (k, d) : ℝ)| ≤ q d) :
    let root := allocatedPhysicalCubeRoot B U basis S c x y
    let root₀ := allocatedPhysicalCubeRoot B U basis S c x y₀
    let dirs := allocatedPhysicalCubeDirections B U basis S x y
    let dirs₀ := allocatedPhysicalCubeDirections B U basis S x y₀
    let shift := physicalResidueOffsetShift root root₀ dirs dirs₀ r q
    (∀ d, shift d ∈ integerScalarLattice (Unit ⊕ α) (period : ℤ)) ∧
    (∀ v, physicalResidueReconstruction root dirs base r q v =
      physicalResidueReconstruction root₀ dirs₀ base r q (v + shift)) ∧
    (∀ d i, |(shift d i : ℝ)| ≤
      Fintype.card (Option vars) * (2 * allocatedPhysicalEntryBudget B U basis S c)) := by
  intro root root₀ dirs dirs₀ shift
  have hres (d) : integerResidueMatrix (physicalCubeCoefficient root dirs) (q d * period) =
      integerResidueMatrix (physicalCubeCoefficient root₀ dirs₀) (q d * period) :=
    integerResidueMatrix_reduce _ _ (hdiv d)
      (allocatedPhysicalCube_residue_of_whole_label B U basis S c x y y₀ modulus hlabel)
  refine ⟨fun d => physicalResidueOffsetShift_mem root root₀ dirs dirs₀ r q hq period hres d,
    fun v => physicalResidueReconstruction_offset_shift root root₀ dirs dirs₀ base r q hq period hres v, ?_⟩
  intro d i
  apply (physicalResidueOffsetShift_bound root root₀ dirs dirs₀ r q hq period hres hr d i).trans
  calc
    _ ≤ ∑ _k : Option vars, 2 * allocatedPhysicalEntryBudget B U basis S c := by
      apply Finset.sum_le_sum
      intro k _
      rw [Int.cast_sub]
      apply (abs_sub _ _).trans
      have h₁ := allocatedPhysicalCube_coefficient_entry_bound B U basis S c x y i k
      have h₂ := allocatedPhysicalCube_coefficient_entry_bound B U basis S c x y₀ i k
      linarith
    _ = _ := by simp

end Erdos3.VectorPolynomial

end

end OAI
