import OAI.Combinatorics.Progressions.Lattices.ResidueAffineProfileLaw

namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem shiftedUnitProfile_eq_translate {J : Type*} [Fintype J] (a S : J → ℝ) :
    shiftedUnitProfile a S = fun x => smoothProductProfile J (x - fun j => a j / S j) := by
  funext x
  simp only [shiftedUnitProfile, affineProductProfile_eq, profileWidthFactor,
    inv_one, Finset.prod_const_one, one_mul, div_one]
  rfl

theorem selectedCoefficientDensity_shifted {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (M : Matrix I J ℤ) (s : I ↪ J) (hM : (M.submatrix id s).det ≠ 0)
    (S : J → ℝ) (P : I → ℝ) (hS : ∀ j, 0 < S j) (hP : ∀ i, 0 < P i)
    (a : J → ℝ) (v : I → ℝ) :
    selectedCoefficientDensity M s hM S P hS hP (shiftedUnitProfile a S) v =
      selectedCoefficientDensity M s hM S P hS hP (smoothProductProfile J)
        (v - normalizedIntegerColumns M S P *ᵥ (fun j => a j / S j)) := by
  rw [shiftedUnitProfile_eq_translate, selectedCoefficientDensity_input_translate]

theorem normalizedIntegerColumns_real_mulVec {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (M : Matrix I J ℤ) (S : J → ℝ) (P : I → ℝ)
    (hS : ∀ j, S j ≠ 0) (a : J → ℝ) :
    normalizedIntegerColumns M S P *ᵥ (fun j => a j / S j) =
      fun i => (∑ j, (M i j : ℝ) * a j) / P i := by
  funext i
  simp only [Matrix.mulVec, dotProduct, normalizedIntegerColumns_entry_div, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  field_simp [hS j]

theorem normalizedIntegerColumns_residue_center {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (M : Matrix I J ℤ) (S : J → ℝ) (P : I → ℝ)
    (hS : ∀ j, S j ≠ 0) (r : J → ℤ) (q : ℝ) :
    normalizedIntegerColumns M S P *ᵥ (fun j => (-(r j : ℝ) / q) / S j) =
      fun i => -((M *ᵥ r) i : ℝ) / (q * P i) := by
  rw [normalizedIntegerColumns_real_mulVec M S P hS]
  funext i
  have hs : (∑ j, (M i j : ℝ) * (-(r j : ℝ) / q)) =
      (∑ j, (M i j : ℝ) * (r j : ℝ)) * (-q⁻¹) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hs]
  simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul, div_eq_mul_inv, mul_inv_rev]
  ring

theorem selectedCoefficientDensity_residue_recenter {I J : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (M : Matrix I J ℤ) (s : I ↪ J) (hM : (M.submatrix id s).det ≠ 0)
    (S : J → ℝ) (P : I → ℝ) (hS : ∀ j, 0 < S j) (hP : ∀ i, 0 < P i)
    (r : J → ℤ) (q : ℝ) (v : I → ℝ) :
    selectedCoefficientDensity M s hM S P hS hP
        (shiftedUnitProfile (fun j => -(r j : ℝ) / q) S)
        (fun i => (v i - ((M *ᵥ r) i : ℝ)) / (q * P i)) =
      selectedCoefficientDensity M s hM S P hS hP (smoothProductProfile J)
        (fun i => v i / (q * P i)) := by
  rw [selectedCoefficientDensity_shifted,
    normalizedIntegerColumns_residue_center M S P (fun j => (hS j).ne') r q]
  congr 1
  funext i
  simp only [Pi.sub_apply]
  ring

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open scoped Matrix

variable {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K] [DecidableEq K]

theorem physicalCube_normalized_scale_independent (root : K → ℤ) (D : Matrix α K ℤ)
    {W A R L : ℝ} (hW : 0 ≤ W) (hR : R ≠ 0) (hL : L ≠ 0) (hA : A = (1 + W) * R) :
    normalizedIntegerColumns (physicalCubeCoefficient root D)
        (physicalSpatialInputScale K A R) (physicalSpatialOutputScale α A R L) =
      normalizedIntegerColumns (physicalCubeCoefficient root D)
        (physicalSpatialInputScale K (1 + W) 1) (physicalSpatialOutputScale α (1 + W) 1 L) := by
  have hW' : 1 + W ≠ 0 := ne_of_gt (by linarith)
  have hA' : A ≠ 0 := by rw [hA]; exact mul_ne_zero hW' hR
  rw [physicalCube_normalized_columns root D hA' hR hL,
    physicalCube_normalized_columns root D hW' one_ne_zero hL]
  ext i k
  cases i <;> cases k <;> simp only
  rw [hA]
  field_simp

noncomputable def fixedPhysicalSpatialDensity (root : K → ℤ) (D : Matrix α K ℤ) (s : α ↪ K)
    (hp : ((physicalCubeCoefficient root D).submatrix id (physicalCubePivotIndex s)).det ≠ 0)
    {W L : ℝ} (hW : 0 ≤ W) (hL : 0 < L) : ((Unit ⊕ α) → ℝ) → ℝ :=
  selectedCoefficientDensity (physicalCubeCoefficient root D) (physicalCubePivotIndex s) hp
    (physicalSpatialInputScale K (1 + W) 1) (physicalSpatialOutputScale α (1 + W) 1 L)
    (physicalSpatialInputScale_pos K (by linarith) zero_lt_one)
    (physicalSpatialOutputScale_pos α (by linarith) zero_lt_one hL) (smoothProductProfile (Option K))

theorem trimmedSpatialDensity_eq_fixed (root : K → ℤ) (D : Matrix α K ℤ) (s : α ↪ K)
    (hp : ((physicalCubeCoefficient root D).submatrix id (physicalCubePivotIndex s)).det ≠ 0)
    {X : Type*} {W τ L : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hL : 0 < L)
    (N q : X → ℕ) (d : X) (hN : 0 < N d) (hq : 0 < q d)
    (hi : ∀ k, 0 < physicalSpatialInputScale K (trimmedSpatialRootScale τ N q d)
      (trimmedSpatialSlopeScale W τ N q d) k)
    (ho : ∀ i, 0 < physicalSpatialOutputScale α (trimmedSpatialRootScale τ N q d)
      (trimmedSpatialSlopeScale W τ N q d) L i) :
    selectedCoefficientDensity (physicalCubeCoefficient root D) (physicalCubePivotIndex s) hp
        (physicalSpatialInputScale K (trimmedSpatialRootScale τ N q d) (trimmedSpatialSlopeScale W τ N q d))
        (physicalSpatialOutputScale α (trimmedSpatialRootScale τ N q d) (trimmedSpatialSlopeScale W τ N q d) L)
        hi ho (smoothProductProfile (Option K)) = fixedPhysicalSpatialDensity root D s hp hW hL := by
  apply selectedCoefficientDensity_normalized_congr
  exact physicalCube_normalized_scale_independent root D hW
    (trimmedSpatial_scales_pos hW hτ N q d hN hq).2.ne' hL.ne' (trimmedSpatial_scale_ratio hW N q d)

omit [Fintype α] [DecidableEq α] in
theorem trimmedSpatialOutputScale_residue_cancel {X : Type*} {W τ L : ℝ}
    (N q : X → ℕ) (d : X) (hq : 0 < q d) (i : Unit ⊕ α) :
    (q d : ℝ) * physicalSpatialOutputScale α (trimmedSpatialRootScale τ N q d)
        (trimmedSpatialSlopeScale W τ N q d) L i =
      physicalSpatialOutputScale α (τ * (N d : ℝ) / 8)
        (τ * (N d : ℝ) / (8 * (1 + W))) L i := by
  have hq' : (q d : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hq)
  cases i <;> simp only [physicalSpatialOutputScale, Sum.elim_inl, Sum.elim_inr,
    trimmedSpatialRootScale, trimmedSpatialSlopeScale] <;> field_simp

theorem trimmedSpatialDensity_residue_fixed (root : K → ℤ) (D : Matrix α K ℤ) (s : α ↪ K)
    (hp : ((physicalCubeCoefficient root D).submatrix id (physicalCubePivotIndex s)).det ≠ 0)
    {X : Type*} {W τ L : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hL : 0 < L)
    (N q : X → ℕ) (d : X) (hN : 0 < N d) (hq : 0 < q d)
    (hi : ∀ k, 0 < physicalSpatialInputScale K (trimmedSpatialRootScale τ N q d)
      (trimmedSpatialSlopeScale W τ N q d) k)
    (ho : ∀ i, 0 < physicalSpatialOutputScale α (trimmedSpatialRootScale τ N q d)
      (trimmedSpatialSlopeScale W τ N q d) L i)
    (r : Option K → ℤ) (v : (Unit ⊕ α) → ℝ) :
    selectedCoefficientDensity (physicalCubeCoefficient root D) (physicalCubePivotIndex s) hp
        (physicalSpatialInputScale K (trimmedSpatialRootScale τ N q d) (trimmedSpatialSlopeScale W τ N q d))
        (physicalSpatialOutputScale α (trimmedSpatialRootScale τ N q d) (trimmedSpatialSlopeScale W τ N q d) L)
        hi ho (shiftedUnitProfile (fun k => -(r k : ℝ) / q d)
          (physicalSpatialInputScale K (trimmedSpatialRootScale τ N q d) (trimmedSpatialSlopeScale W τ N q d)))
        (fun i => (v i - ((physicalCubeCoefficient root D *ᵥ r) i : ℝ)) /
          ((q d : ℝ) * physicalSpatialOutputScale α (trimmedSpatialRootScale τ N q d)
            (trimmedSpatialSlopeScale W τ N q d) L i)) =
      fixedPhysicalSpatialDensity root D s hp hW hL
        (fun i => v i / physicalSpatialOutputScale α (τ * (N d : ℝ) / 8)
          (τ * (N d : ℝ) / (8 * (1 + W))) L i) := by
  rw [selectedCoefficientDensity_residue_recenter,
    trimmedSpatialDensity_eq_fixed root D s hp hW hτ hL N q d hN hq hi ho]
  congr 1
  funext i
  rw [trimmedSpatialOutputScale_residue_cancel N q d hq]

end Erdos3.BooleanCubeKernel

end

end OAI
