import OAI.Combinatorics.Progressions.Linear.PhysicalCubeMatrix

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

def physicalCubeOptionEquiv (K : Type*) : (Unit ⊕ K) ≃ Option K where
  toFun := Sum.elim (fun _ => none) some
  invFun := Option.elim' (.inl ()) Sum.inr
  left_inv x := by cases x with | inl x => cases x; rfl | inr x => rfl
  right_inv x := by cases x <;> rfl

def physicalCubePivotIndex {α K : Type*} (s : α ↪ K) : (Unit ⊕ α) ↪ Option K where
  toFun := Sum.elim (fun _ => none) (fun i => some (s i))
  inj' := by
    intro i j h
    cases i with
    | inl i => cases j with
      | inl j => cases i; cases j; rfl
      | inr j => cases h
    | inr i => cases j with
      | inl j => cases h
      | inr j => exact congrArg Sum.inr (s.injective (Option.some.inj h))

theorem physicalCubePivotIndex_inl {α K : Type*} (s : α ↪ K) (i : Unit) :
    physicalCubePivotIndex s (.inl i) = none := rfl

theorem physicalCubePivotIndex_inr {α K : Type*} (s : α ↪ K) (i : α) :
    physicalCubePivotIndex s (.inr i) = some (s i) := rfl

theorem physicalCubeCoefficient_reindex {α K : Type*}
    (root : K → ℤ) (D : Matrix α K ℤ) :
    (physicalCubeCoefficient root D).submatrix id (physicalCubeOptionEquiv K) =
      rootDifferenceMatrix root D := by
  ext i j
  cases i <;> cases j <;> rfl

theorem physicalCubeCoefficient_pivot {α K : Type*}
    (root : K → ℤ) (D : Matrix α K ℤ) (s : α ↪ K) :
    (physicalCubeCoefficient root D).submatrix id (physicalCubePivotIndex s) =
      selectedSpatialPivot root D s := by
  ext i j
  cases i <;> cases j <;> rfl

noncomputable def physicalSpatialInputScale (K : Type*) (A R : ℝ) : Option K → ℝ :=
  Option.elim' A (fun _ => R)

noncomputable def physicalSpatialOutputScale (α : Type*) (A R L : ℝ) : (Unit ⊕ α) → ℝ :=
  Sum.elim (fun _ => A) (fun _ => L * R)

theorem physicalSpatialInputScale_pos (K : Type*) {A R : ℝ} (hA : 0 < A) (hR : 0 < R) :
    ∀ k, 0 < physicalSpatialInputScale K A R k := by
  intro k
  cases k
  · exact hA
  · exact hR

theorem physicalSpatialOutputScale_pos (α : Type*) {A R L : ℝ}
    (hA : 0 < A) (hR : 0 < R) (hL : 0 < L) :
    ∀ i, 0 < physicalSpatialOutputScale α A R L i := by
  intro i
  cases i
  · exact hA
  · exact mul_pos hL hR

theorem physicalCube_normalized_columns {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [DecidableEq K]
    (root : K → ℤ) (D : Matrix α K ℤ) {A R L : ℝ}
    (hA : A ≠ 0) (hR : R ≠ 0) (hL : L ≠ 0) :
    normalizedIntegerColumns (physicalCubeCoefficient root D)
        (physicalSpatialInputScale K A R) (physicalSpatialOutputScale α A R L) =
      fun i k => match i, k with
      | .inl _, none => 1
      | .inl _, some k => (root k : ℝ) * R / A
      | .inr _, none => 0
      | .inr i, some k => (D i k : ℝ) / L := by
  ext i k
  rw [normalizedIntegerColumns_entry_div]
  cases i <;> cases k <;>
    simp [physicalCubeCoefficient, physicalSpatialInputScale, physicalSpatialOutputScale, hA]
  field_simp

theorem physicalCube_normalized_pivot {α K : Type*}
    [Fintype α] [DecidableEq α]
    (root : K → ℤ) (D : Matrix α K ℤ) (s : α ↪ K) {A R L : ℝ}
    (hA : A ≠ 0) (hR : R ≠ 0) (hL : L ≠ 0) :
    normalizedIntegerPivot ((physicalCubeCoefficient root D).submatrix id (physicalCubePivotIndex s))
        (fun i => physicalSpatialInputScale K A R (physicalCubePivotIndex s i))
        (physicalSpatialOutputScale α A R L) =
      rootDifferenceMatrix (fun i => (root (s i) : ℝ) * R / A)
        (Matrix.of (fun i j => (D i (s j) : ℝ) / L)) := by
  ext i j
  rw [normalizedIntegerPivot_entry]
  cases i <;> cases j <;>
    simp [physicalCubePivotIndex_inl, physicalCubePivotIndex_inr,
      physicalCubeCoefficient, physicalSpatialInputScale,
      physicalSpatialOutputScale, rootDifferenceMatrix, Matrix.fromBlocks, hA]
  field_simp

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

theorem physicalCube_coefficient_bound {α K : Type*}
    (root : K → ℤ) (D : Matrix α K ℤ) {C : ℝ} (hC : 1 ≤ C)
    (hr : ∀ k, |(root k : ℝ)| ≤ C) (hD : ∀ i k, |(D i k : ℝ)| ≤ C) :
    ∀ i k, |(physicalCubeCoefficient root D i k : ℝ)| ≤ C := by
  rintro (i | i) (k | k)
  · simpa [physicalCubeCoefficient] using hC
  · exact hr k
  · simpa [physicalCubeCoefficient] using (zero_le_one.trans hC)
  · exact hD i k

theorem physicalCube_normalized_entry_bound {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [DecidableEq K]
    (root : K → ℤ) (D : Matrix α K ℤ) {A R L : ℝ}
    (hA : 0 < A) (hR : 0 < R) (hL : 0 < L)
    (hr : ∀ k, |(root k : ℝ)| * R ≤ A) (hD : ∀ i k, |(D i k : ℝ)| ≤ L) :
    ∀ i k, |normalizedIntegerColumns (physicalCubeCoefficient root D)
      (physicalSpatialInputScale K A R) (physicalSpatialOutputScale α A R L) i k| ≤ 1 := by
  rw [physicalCube_normalized_columns root D hA.ne' hR.ne' hL.ne']
  rintro (i | i) (k | k)
  · norm_num
  · dsimp
    rw [abs_div, abs_mul, abs_of_pos hA, abs_of_pos hR]
    exact (div_le_one hA).mpr (hr k)
  · norm_num
  · dsimp
    rw [abs_div, abs_of_pos hL]
    exact (div_le_one hL).mpr (hD i k)

theorem physicalCube_pivot_control {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [DecidableEq K]
    (root : K → ℤ) (D : Matrix α K ℤ) (s : α ↪ K) {A R L κ : ℝ}
    (hA : 0 < A) (hR : 0 < R) (hL : 0 < L) (hκ : 0 < κ)
    (hr : ∀ k, |(root k : ℝ)| * R ≤ A) (hD : ∀ i k, |(D i k : ℝ)| ≤ L)
    (hminor : κ ≤ |(Matrix.of (fun i j => (D i (s j) : ℝ) / L)).det|) :
    ((physicalCubeCoefficient root D).submatrix id (physicalCubePivotIndex s)).det ≠ 0 ∧
      ‖(matrixSupCLM (normalizedIntegerPivot
        ((physicalCubeCoefficient root D).submatrix id (physicalCubePivotIndex s))
        (fun i => physicalSpatialInputScale K A R (physicalCubePivotIndex s i))
        (physicalSpatialOutputScale α A R L))).inverse‖ ≤
        (Fintype.card (Unit ⊕ α) : ℝ) * (Fintype.card (Unit ⊕ α)).factorial / κ := by
  let M := (physicalCubeCoefficient root D).submatrix id (physicalCubePivotIndex s)
  let S := fun i => physicalSpatialInputScale K A R (physicalCubePivotIndex s i)
  let P := physicalSpatialOutputScale α A R L
  have hS : ∀ i, 0 < S i := fun i => physicalSpatialInputScale_pos K hA hR _
  have hP : ∀ i, 0 < P i := physicalSpatialOutputScale_pos α hA hR hL
  have he : normalizedIntegerPivot M S P =
      rootDifferenceMatrix (fun i => (root (s i) : ℝ) * R / A)
        (Matrix.of (fun i j => (D i (s j) : ℝ) / L)) :=
    physicalCube_normalized_pivot root D s hA.ne' hR.ne' hL.ne'
  have hd : κ ≤ |(normalizedIntegerPivot M S P).det| := by
    rw [he, rootDifferenceMatrix_det (fun i => (root (s i) : ℝ) * R / A)
      (Matrix.of (fun i j => (D i (s j) : ℝ) / L))]
    exact hminor
  have hb : ∀ i j, |normalizedIntegerPivot M S P i j| ≤ 1 := by
    intro i j
    have h := physicalCube_normalized_entry_bound root D hA hR hL hr hD i (physicalCubePivotIndex s j)
    simpa only [M, S, P, normalizedIntegerPivot_entry, normalizedIntegerColumns_entry_div,
      Matrix.submatrix_apply, id_eq] using h
  have hn : M.det ≠ 0 := by
    intro hz
    have hdet := normalizedIntegerPivot_abs_det M S P hS hP
    rw [hz, Int.natAbs_zero, Nat.cast_zero, zero_mul, zero_div] at hdet
    rw [hdet] at hd
    exact (not_le_of_gt hκ) hd
  refine ⟨hn, ?_⟩
  have h := (matrixSupCLM_inverse_norm_le (normalizedIntegerPivot M S P) zero_le_one hb hκ hd).2
  simpa only [one_pow, mul_one, mul_div_assoc] using h

theorem physicalCubeCoefficient_range {α K : Type*} [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) :
    (physicalCubeCoefficient root D).mulVecLin.range = (rootDifferenceMatrix root D).mulVecLin.range := by
  rw [← integerColumnEquiv_range (physicalCubeCoefficient root D) (physicalCubeOptionEquiv K),
    physicalCubeCoefficient_reindex]

theorem physicalCubeCoefficient_index {α K : Type*} [Fintype α] [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) {B : ℕ}
    (hperiod : HasBoundedScalarPeriod D.mulVecLin.range B) :
    (physicalCubeCoefficient root D).mulVecLin.range.toAddSubgroup.index ≤ B ^ (Fintype.card α + 1) := by
  rw [physicalCubeCoefficient_range]
  exact rootDifferenceMatrix_index_le root D hperiod

theorem physicalCube_remaining_norm {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [DecidableEq K]
    (root : K → ℤ) (D : Matrix α K ℤ) (s : α ↪ K) {A R L : ℝ}
    (hA : 0 < A) (hR : 0 < R) (hL : 0 < L)
    (hr : ∀ k, |(root k : ℝ)| * R ≤ A) (hD : ∀ i k, |(D i k : ℝ)| ≤ L) :
    ‖matrixSupCLM (normalizedIntegerColumns
      (remainingMatrixColumns (physicalCubeCoefficient root D) (physicalCubePivotIndex s))
      (fun j => physicalSpatialInputScale K A R j.val) (physicalSpatialOutputScale α A R L))‖ ≤
      Fintype.card (UnselectedColumn (physicalCubePivotIndex s)) := by
  simpa only [mul_one] using normalized_remainingMatrixColumns_norm
    (physicalCubeCoefficient root D) (physicalCubePivotIndex s)
    (physicalSpatialInputScale K A R) (physicalSpatialOutputScale α A R L) zero_le_one
    (physicalCube_normalized_entry_bound root D hA hR hL hr hD)

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory
open scoped BigOperators NNReal

noncomputable def physicalSpatialInverseBound (α : Type*) [Fintype α] (κ : ℝ) : ℝ :=
  (Fintype.card (Unit ⊕ α) : ℝ) * (Fintype.card (Unit ⊕ α)).factorial / κ

noncomputable def physicalSpatialMeshCost {α K : Type*} [Fintype α] [Fintype K]
    (s : α ↪ K) (C r : ℝ) (lip : ℝ≥0) : ℝ :=
  2 * (1 + (2 * r + 2) ^ (Fintype.card (Unit ⊕ α) +
    Fintype.card (UnselectedColumn (physicalCubePivotIndex s))) * lip) *
      ((Fintype.card (Unit ⊕ α)).factorial * C ^ Fintype.card (Unit ⊕ α))

noncomputable def physicalSpatialErrorConstant {α K : Type*} [Fintype α] [Fintype K]
    (s : α ↪ K) (B : ℕ) (κ C r cap : ℝ) (lip : ℝ≥0) : ℝ :=
  normalizedFiberErrorConstant (Fintype.card (Unit ⊕ α))
    (Fintype.card (UnselectedColumn (physicalCubePivotIndex s)))
    ((B : ℝ) ^ (Fintype.card α + 1)) (physicalSpatialInverseBound α κ)
    (Fintype.card (UnselectedColumn (physicalCubePivotIndex s))) r cap lip *
      ((Fintype.card (Unit ⊕ α)).factorial * C ^ Fintype.card (Unit ⊕ α))

theorem physicalCube_full_comparison {α K : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [DecidableEq K]
    (root : K → ℤ) (D : Matrix α K ℤ) (s : α ↪ K) {A R L κ ρ C : ℝ} {B : ℕ}
    (hA : 0 < A) (hR : 0 < R) (hL : 0 < L) (hκ : 0 < κ) (hρ : 0 < ρ)
    (hC : 1 ≤ C) (hρA : ρ ≤ A) (hρR : ρ ≤ R)
    (hr : ∀ k, |(root k : ℝ)| * R ≤ A) (hD : ∀ i k, |(D i k : ℝ)| ≤ L)
    (hrC : ∀ k, |(root k : ℝ)| ≤ C) (hDC : ∀ i k, |(D i k : ℝ)| ≤ C)
    (hminor : κ ≤ |(Matrix.of (fun i j => (D i (s j) : ℝ) / L)).det|)
    (hperiod : HasBoundedScalarPeriod D.mulVecLin.range B)
    (f : (Option K → ℝ) → ℝ) (hf0 : ∀ x, 0 ≤ f x) {lip : ℝ≥0} (hf : LipschitzWith lip f)
    {r cap : ℝ} (hr0 : 0 ≤ r) (hcap : 0 ≤ cap)
    (hsupport : ∀ x, r < ‖x‖ → f x = 0) (hmass : (∫ x, f x) = 1)
    (hbound : ∀ x, ‖f x‖ ≤ cap) (hmesh : physicalSpatialMeshCost s C r lip ≤ ρ) :
    let hp := (physicalCube_pivot_control root D s hA hR hL hκ hr hD hminor).1
    ∃ hZ : 0 < coefficientWeightSum f (physicalSpatialInputScale K A R), ∀ v,
      |(∏ i, physicalSpatialOutputScale α A R L i) *
          (coefficientImagePMF (physicalCubeCoefficient root D) f hf0
            (physicalSpatialInputScale K A R) (physicalSpatialInputScale_pos K hA hR) hsupport hZ v).toReal -
        coefficientImageMask (physicalCubeCoefficient root D) (physicalSpatialOutputScale α A R L)
          (selectedCoefficientDensity (physicalCubeCoefficient root D) (physicalCubePivotIndex s) hp
            (physicalSpatialInputScale K A R) (physicalSpatialOutputScale α A R L)
            (physicalSpatialInputScale_pos K hA hR) (physicalSpatialOutputScale_pos α hA hR hL) f) v| ≤
        physicalSpatialErrorConstant s B κ C r cap lip / ρ := by
  let M := physicalCubeCoefficient root D
  let sel := physicalCubePivotIndex s
  let S := physicalSpatialInputScale K A R
  let P := physicalSpatialOutputScale α A R L
  have hctrl := physicalCube_pivot_control root D s hA hR hL hκ hr hD hminor
  have hc : ∀ i j, |(M i (sel j) : ℝ)| ≤ C * (1 : ℝ) ^ 0 := by
    intro i j
    simpa only [pow_zero, mul_one] using physicalCube_coefficient_bound root D hC hrC hDC i (sel j)
  have hdet : (((M.submatrix id sel).det.natAbs : ℝ)) ≤
      (Fintype.card (Unit ⊕ α)).factorial * C ^ Fintype.card (Unit ⊕ α) := by
    simpa only [one_pow, mul_one] using integerPivot_polynomial_period_bound (M.submatrix id sel) 0 hc
  have hm := enormousCoefficient_mesh_conditions (j := Fintype.card (Unit ⊕ α)) (h := 0)
    (D := (Fintype.card (Unit ⊕ α)).factorial * C ^ Fintype.card (Unit ⊕ α))
    (Z := (2 * r + 2) ^ (Fintype.card (Unit ⊕ α) + Fintype.card (UnselectedColumn sel)) * lip)
    (L := 1) (H := ρ) (by positivity) (by positivity) (by norm_num) hρ
    (by simpa only [physicalSpatialMeshCost, one_pow, mul_one] using hmesh)
  simp only [one_pow, mul_one, div_one] at hm
  have hsmall : (2 * r + 2) ^ (Fintype.card (Unit ⊕ α) + Fintype.card (UnselectedColumn sel)) * lip *
      (((M.submatrix id sel).det.natAbs : ℝ) / ρ) ≤ 1 / 2 := by
    apply le_trans _ hm.2
    exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hdet hρ.le) (by positivity)
  have hindex : (M.mulVecLin.range.toAddSubgroup.index : ℝ) ≤ (B : ℝ) ^ (Fintype.card α + 1) := by
    exact_mod_cast physicalCubeCoefficient_index root D hperiod
  have hscale : ∀ k, ρ ≤ S k := by
    intro k
    cases k
    · exact hρA
    · exact hρR
  have he := coefficientImage_polynomial_error M sel hctrl.1 S P
    (physicalSpatialInputScale_pos K hA hR) (physicalSpatialOutputScale_pos α hA hR hL)
    f hf0 hf 0 hr0 hρ hcap hscale (hdet.trans hm.1) hc hsupport hmass hsmall hbound hindex hctrl.2
    (physicalCube_remaining_norm root D s hA hR hL hr hD)
  simpa only [physicalSpatialErrorConstant, physicalSpatialInverseBound, one_pow, mul_one] using he

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

noncomputable def physicalSpatialCommonBudget (j d n : ℕ) (b : ℝ) : ℝ :=
  (j : ℝ) * b + (j : ℝ) ^ 2 + j + b + d + affineProfileLogBound n 0 + 2

theorem physicalSpatialCommonBudget_bounds (j d n : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    b ≤ physicalSpatialCommonBudget j d n b ∧
    (j : ℝ) * b ≤ physicalSpatialCommonBudget j d n b ∧
    (j : ℝ) ^ 2 + j + b ≤ physicalSpatialCommonBudget j d n b ∧
    (d : ℝ) ≤ physicalSpatialCommonBudget j d n b ∧
    affineProfileLogBound n 0 ≤ physicalSpatialCommonBudget j d n b ∧
    2 ≤ physicalSpatialCommonBudget j d n b := by
  have hj := Nat.cast_nonneg (α := ℝ) j
  have hd := Nat.cast_nonneg (α := ℝ) d
  have hf := affineProfileLogBound_nonneg n (by norm_num : (0 : ℝ) ≤ 0)
  have hm := mul_nonneg hj hb
  have hs := sq_nonneg (j : ℝ)
  unfold physicalSpatialCommonBudget
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

noncomputable def physicalSpatialLogAllowance {α K : Type*} [Fintype α] [Fintype K]
    (s : α ↪ K) (b : ℝ) : ℝ :=
  let j := Fintype.card (Unit ⊕ α)
  let d := Fintype.card (UnselectedColumn (physicalCubePivotIndex s))
  coefficientLogAllowance j d (physicalSpatialCommonBudget j d (Fintype.card (Option K)) b)

theorem physicalSpatialLogAllowance_nonneg {α K : Type*} [Fintype α] [Fintype K]
    (s : α ↪ K) {b : ℝ} (hb : 0 ≤ b) : 0 ≤ physicalSpatialLogAllowance s b := by
  have hc := hb.trans (physicalSpatialCommonBudget_bounds (Fintype.card (Unit ⊕ α))
    (Fintype.card (UnselectedColumn (physicalCubePivotIndex s))) (Fintype.card (Option K)) hb).1
  unfold physicalSpatialLogAllowance coefficientLogAllowance
  positivity

theorem physicalSpatialInverseBound_le_exp (α : Type*) [Fintype α] {κ b : ℝ}
    (hκ : 0 < κ) (hi : κ⁻¹ ≤ Real.exp b) :
    physicalSpatialInverseBound α κ ≤
      Real.exp ((Fintype.card (Unit ⊕ α) : ℝ) ^ 2 + Fintype.card (Unit ⊕ α) + b) := by
  let j := Fintype.card (Unit ⊕ α)
  have hj : (j : ℝ) ≤ Real.exp (j : ℝ) := by linarith [Real.add_one_le_exp (j : ℝ)]
  change (j : ℝ) * j.factorial / κ ≤ _
  calc
    _ ≤ Real.exp (j : ℝ) * Real.exp ((j : ℝ) ^ 2) * Real.exp b := by
      rw [div_eq_mul_inv]
      gcongr
      exact factorial_le_exp_sq j
    _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring

theorem physicalSpatial_constants_le_exp {α K : Type*} [Fintype α] [Fintype K]
    (s : α ↪ K) {M : ℕ} {κ C b : ℝ} (hb : 0 ≤ b) (hκ : 0 < κ) (hC0 : 0 ≤ C)
    (hM : (M : ℝ) ≤ Real.exp b) (hi : κ⁻¹ ≤ Real.exp b) (hC : C ≤ Real.exp b) :
    physicalSpatialMeshCost s C 2 (affineProductProfileLip (Option K) 1) ≤
        Real.exp (physicalSpatialLogAllowance s b) ∧
    physicalSpatialErrorConstant s M κ C 2 1 (affineProductProfileLip (Option K) 1) ≤
        Real.exp (physicalSpatialLogAllowance s b) := by
  let j := Fintype.card (Unit ⊕ α)
  let d := Fintype.card (UnselectedColumn (physicalCubePivotIndex s))
  let B := physicalSpatialCommonBudget j d (Fintype.card (Option K)) b
  have hs := physicalSpatialCommonBudget_bounds j d (Fintype.card (Option K)) hb
  have hB : 0 ≤ B := hb.trans hs.1
  have hC' : C ≤ Real.exp B := hC.trans (Real.exp_le_exp.mpr hs.1)
  have hM' : (M : ℝ) ^ (Fintype.card α + 1) ≤ Real.exp B := by
    have hj : Fintype.card α + 1 = j := by simp [j, Nat.add_comm]
    calc
      _ ≤ (Real.exp b) ^ (Fintype.card α + 1) := by gcongr
      _ = Real.exp ((j : ℝ) * b) := by rw [← Real.exp_nat_mul, hj]
      _ ≤ _ := Real.exp_le_exp.mpr hs.2.1
  have hU : physicalSpatialInverseBound α κ ≤ Real.exp B :=
    (physicalSpatialInverseBound_le_exp α hκ hi).trans (Real.exp_le_exp.mpr hs.2.2.1)
  have hd : (d : ℝ) ≤ Real.exp B := by
    have : (d : ℝ) ≤ Real.exp (d : ℝ) := by linarith [Real.add_one_le_exp (d : ℝ)]
    exact this.trans (Real.exp_le_exp.mpr hs.2.2.2.1)
  have hR : (2 : ℝ) ≤ Real.exp B := by
    have : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    exact this.trans (Real.exp_le_exp.mpr hs.2.2.2.2.2)
  have hH : (1 : ℝ) ≤ Real.exp B := Real.one_le_exp hB
  have hK : (affineProductProfileLip (Option K) 1 : ℝ) ≤ Real.exp B :=
    (affineProductProfileLip_le_exp (Option K) (δ := 1) (t := 0) (by norm_num)).trans
      (Real.exp_le_exp.mpr hs.2.2.2.2.1)
  constructor
  · exact coefficientMeshConstant_le_exp j d _ hB (by norm_num) hC0 hR hC' hK
  · exact coefficientComparisonConstant_le_exp j d _ hB (by positivity)
      (by unfold physicalSpatialInverseBound; positivity) (by positivity)
      (by norm_num) (by norm_num) hC0 hM' hU hd hR hH hK hC'

theorem physicalSpatial_tolerance_numerics {b E W q τ N ε : ℝ}
    (hb : 0 ≤ b) (hE : 0 ≤ E) (hW : 0 ≤ W) (hq : 0 ≤ q)
    (hτ : 0 < τ)
    (hWexp : W ≤ Real.exp b) (hqexp : q ≤ Real.exp b)
    (hτexp : τ⁻¹ ≤ Real.exp b) (hεexp : ε⁻¹ ≤ Real.exp b)
    (hN : Real.exp (E + 4 * b + 12) ≤ N) :
    let ρ := Real.exp (E + b + 2)
    1 ≤ ρ ∧ Real.exp E * (1 + ε⁻¹) ≤ ρ ∧ 8 * (1 + W) * q * ρ ≤ τ * N := by
  have hplus (a : ℝ) (ha : a ≤ Real.exp b) : 1 + a ≤ Real.exp (b + 2) := by
    have htwo : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    calc
      _ ≤ Real.exp b * 2 := by linarith [Real.one_le_exp hb]
      _ ≤ Real.exp b * Real.exp 2 := mul_le_mul_of_nonneg_left htwo (Real.exp_nonneg b)
      _ = _ := (Real.exp_add _ _).symm
  dsimp only
  refine ⟨Real.one_le_exp (by linarith), ?_, ?_⟩
  · calc
      _ ≤ Real.exp E * Real.exp (b + 2) :=
        mul_le_mul_of_nonneg_left (hplus ε⁻¹ hεexp) (Real.exp_nonneg E)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  · have hside : 8 * (1 + W) * q * Real.exp (E + b + 2) * τ⁻¹ ≤ N := by
      calc
        _ ≤ Real.exp 8 * Real.exp (b + 2) * Real.exp b * Real.exp (E + b + 2) * Real.exp b := by
          gcongr
          · linarith [Real.add_one_le_exp (8 : ℝ)]
          · exact hplus W hWexp
        _ = Real.exp (E + 4 * b + 12) := by
          simp only [← Real.exp_add]
          congr 1
          ring
        _ ≤ N := hN
    have hdiv : (8 * (1 + W) * q * Real.exp (E + b + 2)) / τ ≤ N := by
      simpa only [div_eq_mul_inv] using hside
    simpa only [mul_comm N τ] using (div_le_iff₀ hτ).mp hdiv

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

noncomputable def trimmedSpatialRootScale {X : Type*} (τ : ℝ) (N modulus : X → ℕ) (x : X) : ℝ :=
  τ * (N x : ℝ) / 8 / modulus x

noncomputable def trimmedSpatialSlopeScale {X : Type*} (B τ : ℝ) (N modulus : X → ℕ) (x : X) : ℝ :=
  τ * (N x : ℝ) / (8 * (1 + B)) / modulus x

theorem trimmedSpatial_residue_scale {K X : Type*} (B τ : ℝ) (N modulus : X → ℕ) (x : X) :
    (fun k => residueProfileWidth modulus (trimmedSpatialWidths (K := K) B τ N) (k, x)) =
      physicalSpatialInputScale K (trimmedSpatialRootScale τ N modulus x)
        (trimmedSpatialSlopeScale B τ N modulus x) := by
  funext k
  cases k <;> simp only [residueProfileWidth, trimmedSpatialWidths, centeredSpatialWidths,
    physicalSpatialInputScale, Option.elim', trimmedSpatialRootScale, trimmedSpatialSlopeScale, one_mul] <;> ring

theorem trimmedSpatial_scales_pos {X : Type*} {B τ : ℝ} (hB : 0 ≤ B) (hτ : 0 < τ)
    (N modulus : X → ℕ) (x : X) (hN : 0 < N x) (hq : 0 < modulus x) :
    0 < trimmedSpatialRootScale τ N modulus x ∧ 0 < trimmedSpatialSlopeScale B τ N modulus x := by
  have hn : (0 : ℝ) < N x := by exact_mod_cast hN
  have hq' : (0 : ℝ) < modulus x := by exact_mod_cast hq
  unfold trimmedSpatialRootScale trimmedSpatialSlopeScale
  constructor <;> positivity

theorem trimmedSpatial_scale_ratio {X : Type*} {B τ : ℝ} (hB : 0 ≤ B)
    (N modulus : X → ℕ) (x : X) :
    trimmedSpatialRootScale τ N modulus x =
      (1 + B) * trimmedSpatialSlopeScale B τ N modulus x := by
  have hb : 1 + B ≠ 0 := ne_of_gt (by linarith)
  unfold trimmedSpatialRootScale trimmedSpatialSlopeScale
  field_simp

theorem trimmedSpatial_root_control {K X : Type*} [Fintype K] {B τ : ℝ}
    (hB : 0 ≤ B) (hτ : 0 < τ) (N modulus : X → ℕ) (x : X)
    (hN : 0 < N x) (hq : 0 < modulus x) (root : K → ℤ)
    (hroot : (∑ k, |(root k : ℝ)|) ≤ B) (k : K) :
    |(root k : ℝ)| * trimmedSpatialSlopeScale B τ N modulus x ≤ trimmedSpatialRootScale τ N modulus x := by
  have hr : |(root k : ℝ)| ≤ B :=
    (Finset.single_le_sum (fun j _ => abs_nonneg (root j : ℝ)) (Finset.mem_univ k)).trans hroot
  rw [trimmedSpatial_scale_ratio hB]
  exact mul_le_mul_of_nonneg_right (by linarith) (trimmedSpatial_scales_pos hB hτ N modulus x hN hq).2.le

theorem trimmedSpatial_scale_lower {X : Type*} {B τ ρ : ℝ}
    (hB : 0 ≤ B) (hρ : 0 ≤ ρ) (N modulus : X → ℕ) (x : X) (hq : 0 < modulus x)
    (hlarge : 8 * (1 + B) * (modulus x : ℝ) * ρ ≤ τ * (N x : ℝ)) :
    ρ ≤ trimmedSpatialRootScale τ N modulus x ∧ ρ ≤ trimmedSpatialSlopeScale B τ N modulus x := by
  have hq' : (0 : ℝ) < modulus x := by exact_mod_cast hq
  have hb : (0 : ℝ) < 8 * (1 + B) := by positivity
  have hs : ρ ≤ trimmedSpatialSlopeScale B τ N modulus x := by
    unfold trimmedSpatialSlopeScale
    apply (le_div_iff₀ hq').mpr
    apply (le_div_iff₀ hb).mpr
    nlinarith [hlarge]
  refine ⟨?_, hs⟩
  unfold trimmedSpatialRootScale
  apply (le_div_iff₀ hq').mpr
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
  nlinarith [mul_nonneg hB (mul_nonneg hq'.le hρ)]

end Erdos3.BooleanCubeKernel

end

end OAI
