import OAI.Combinatorics.Progressions.Geometry.MinkowskiSecondBoxGlue

namespace OAI

section

namespace Erdos3.BohrLattice.MinkowskiDiagonalNormalization

open scoped BigOperators Matrix
open Erdos3.BohrLattice.BoxCertificate Set Submodule Module

noncomputable section

def divideCoordinates {n : ℕ} (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) where
  toFun x i := x i / r i
  invFun x i := x i * r i
  left_inv x := by
    funext i
    exact div_mul_cancel₀ (x i) (hr i).ne'
  right_inv x := by
    funext i
    exact mul_div_cancel_right₀ (x i) (hr i).ne'
  map_add' x y := by
    funext i
    exact add_div (x i) (y i) (r i)
  map_smul' a x := by
    funext i
    simp [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_assoc]

@[simp] theorem divideCoordinates_apply {n : ℕ} (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (x : Fin n → ℝ) (i : Fin n) :
    divideCoordinates r hr x i = x i / r i := rfl

@[simp] theorem divideCoordinates_symm_apply {n : ℕ} (r : Fin n → ℝ)
    (hr : ∀ i, 0 < r i) (x : Fin n → ℝ) (i : Fin n) :
    (divideCoordinates r hr).symm x i = x i * r i := rfl

def normalizedBasis {n : ℕ} (b : Basis (Fin n) ℝ (Fin n → ℝ))
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    Basis (Fin n) ℝ (Fin n → ℝ) :=
  b.map (divideCoordinates r hr)

@[simp] theorem normalizedBasis_apply {n : ℕ}
    (b : Basis (Fin n) ℝ (Fin n → ℝ))
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) (j i : Fin n) :
    normalizedBasis b r hr j i = b j i / r i := by
  simp [normalizedBasis]

theorem mem_realBox_mul_iff {n : ℕ} (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (s : ℝ) (_hs : 0 ≤ s) (x : Fin n → ℝ) :
    x ∈ realBox (fun i ↦ s * r i) ↔
      divideCoordinates r hr x ∈ realBox (fun _ ↦ s) := by
  constructor
  · intro hx
    constructor
    · intro i
      apply (le_div_iff₀ (hr i)).2
      simpa [mul_comm] using hx.1 i
    · intro i
      apply (div_le_iff₀ (hr i)).2
      simpa [mul_comm] using hx.2 i
  · intro hx
    constructor
    · intro i
      have hi := (le_div_iff₀ (hr i)).1 (hx.1 i)
      simpa [mul_comm] using hi
    · intro i
      have hi := (div_le_iff₀ (hr i)).1 (hx.2 i)
      simpa [mul_comm] using hi

theorem abs_det_normalizedBasis {n : ℕ}
    (b : Basis (Fin n) ℝ (Fin n → ℝ))
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    |(Matrix.of (normalizedBasis b r hr)).det| =
      |(Matrix.of b).det| * (∏ i, r i)⁻¹ := by
  let D : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (fun i ↦ (r i)⁻¹)
  have hmatrix : Matrix.of (normalizedBasis b r hr) = Matrix.of b * D := by
    ext j i
    change b j i / r i = ∑ k, b j k * D k i
    rw [Finset.sum_eq_single i]
    · simp [D, div_eq_mul_inv]
    · intro k _ hki
      simp [D, hki]
    · simp
  have hdetD : D.det = (∏ i, r i)⁻¹ := by
    simp [D, Finset.prod_inv_distrib]
  have hprod : 0 < ∏ i, r i := Finset.prod_pos fun i _ ↦ hr i
  rw [hmatrix, Matrix.det_mul, hdetD, abs_mul, abs_inv, abs_of_pos hprod]

theorem divideCoordinates_mem_span_iff {n : ℕ}
    (b : Basis (Fin n) ℝ (Fin n → ℝ))
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) (x : Fin n → ℝ) :
    divideCoordinates r hr x ∈ Submodule.span ℤ (Set.range (normalizedBasis b r hr)) ↔
      x ∈ Submodule.span ℤ (Set.range b) := by
  let e : (Fin n → ℝ) ≃ₗ[ℤ] (Fin n → ℝ) :=
    (divideCoordinates r hr).restrictScalars ℤ
  have hrange : Set.range (normalizedBasis b r hr) = e '' Set.range b := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨b i, ⟨i, rfl⟩, ?_⟩
      simp [e, normalizedBasis]
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      refine ⟨i, ?_⟩
      simp [e, normalizedBasis]
  change e x ∈ Submodule.span ℤ (Set.range (normalizedBasis b r hr)) ↔ _
  rw [hrange]
  exact Submodule.apply_mem_span_image_iff_mem_span e.injective

end

end Erdos3.BohrLattice.MinkowskiDiagonalNormalization

end

section

namespace Erdos3.BohrLattice.MinkowskiSecondBox

open scoped BigOperators Matrix
open Erdos3.BohrLattice.BoxCertificate Set Module Submodule

noncomputable section

theorem realBox_has_minkowskiSecondCertificate {n : ℕ}
    (b : Basis (Fin n) ℝ (Fin n → ℝ))
    (r : Fin n → ℝ) (hr : ∀ i, 0 < r i) :
    Nonempty (BoxCertificate.SuccessiveProductCertificate
      (Submodule.span ℤ (Set.range b)).toAddSubgroup r
      (minkowskiSecondConstant n * |(Matrix.of b).det| *
        (∏ i, r i)⁻¹)) := by
  classical
  open Erdos3.BohrLattice.MinkowskiDiagonalNormalization in
    let b' := normalizedBasis b r hr
    let e := divideCoordinates r hr
    obtain ⟨C⟩ := cube_has_successiveProductCertificate b'
    let point : Fin n → Fin n → ℝ := fun i ↦ e.symm (C.point i)
    refine ⟨{
      scale := C.scale
      point := point
      scale_nonneg := C.scale_nonneg
      point_mem := ?_
      independent := ?_
      mem_scaledBox := ?_
      product_le := ?_ }⟩
    · intro i
      change point i ∈ Submodule.span ℤ (Set.range b)
      apply (divideCoordinates_mem_span_iff b r hr (point i)).mp
      simpa [point, e, b'] using C.point_mem i
    · apply LinearIndependent.of_comp e.toLinearMap
      convert C.independent using 1
      funext i
      simp [point, e]
    · intro i
      change point i ∈ realBox (fun j ↦ C.scale i * r j)
      apply (mem_realBox_mul_iff r hr (C.scale i) (C.scale_nonneg i) (point i)).mpr
      have hi : C.point i ∈ realBox (fun _ ↦ C.scale i) := by
        rw [← realBox_smul_one_eq_const]
        exact C.mem_scaledBox i
      simpa [point, e] using hi
    · simpa [b', abs_det_normalizedBasis, mul_assoc] using C.product_le

end

end Erdos3.BohrLattice.MinkowskiSecondBox

end

end OAI
