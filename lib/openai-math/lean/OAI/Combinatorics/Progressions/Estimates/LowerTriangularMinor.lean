/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Use BlockTriangular OrderDual.toDual and det_of_lowerTriangular on Lean 4.32.
Mathematical statements are unchanged. -/
import OAI.Compat.Core
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Finset.Max
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

theorem exists_nonzero_row_minor {K ι : Type*} [Field K] [Fintype ι] {k : ℕ}
    (A : Matrix ι (Fin k) K) (hA : LinearIndependent K A.col) :
    ∃ p : Fin k → ι, (A.submatrix p id).det ≠ 0 := by
  classical
  have ht : LinearIndependent K A.transpose.row := hA
  have hr : Module.finrank K (Submodule.span K (Set.range A.row)) = k := by
    rw [← A.rank_eq_finrank_span_row, ← Matrix.rank_transpose]
    simpa only [Fintype.card_fin] using ht.rank_matrix
  have hex := Submodule.exists_fun_fin_finrank_span_eq K (Set.range A.row)
  rw [hr] at hex
  obtain ⟨v, hv, _, hli⟩ := hex
  choose p hp using hv
  have he : (A.submatrix p id).row = v := by
    funext i
    exact hp i
  have hind : LinearIndependent K (A.submatrix p id).row := he.symm ▸ hli
  exact ⟨p, ((A.submatrix p id).isUnit_iff_isUnit_det.mp
    (Matrix.linearIndependent_rows_iff_isUnit.mp hind)).ne_zero⟩

theorem nonzero_row_minor_injective {K ι : Type*} [Field K] {k : ℕ}
    (A : Matrix ι (Fin k) K) (p : Fin k → ι) (hp : (A.submatrix p id).det ≠ 0) :
    Function.Injective p := by
  have h := Matrix.linearIndependent_rows_of_det_ne_zero hp
  intro i j hij
  apply h.injective
  change A (p i) = A (p j)
  rw [hij]

end Erdos3

end

section

namespace Erdos3

theorem exists_minimal_row_minor {K : Type*} [Field K] {m k : ℕ}
    (A : Matrix (Fin m) (Fin k) K) (hA : LinearIndependent K A.col) :
    ∃ p : Fin k → Fin m, (A.submatrix p id).det ≠ 0 ∧
      ∀ q : Fin k → Fin m, (A.submatrix q id).det ≠ 0 →
        (∑ j, (p j).val) ≤ ∑ j, (q j).val := by
  classical
  let S := Finset.univ.filter (fun p : Fin k → Fin m => (A.submatrix p id).det ≠ 0)
  obtain ⟨p, hp⟩ := exists_nonzero_row_minor A hA
  have hS : S.Nonempty := ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩⟩
  obtain ⟨q, hq, hmin⟩ := S.exists_min_image (fun p => ∑ j, (p j).val) hS
  exact ⟨q, (Finset.mem_filter.mp hq).2,
    fun p hp => hmin p (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩)⟩

theorem row_minor_update_det {K ι : Type*} [Field K] {k : ℕ}
    (A : Matrix ι (Fin k) K) (p : Fin k → ι)
    (C : Matrix ι (Fin k) K) (hC : C * A.submatrix p id = A)
    (i : ι) (j : Fin k) :
    (A.submatrix (Function.update p j i) id).det = C i j * (A.submatrix p id).det := by
  have he : A.submatrix (Function.update p j i) id =
      (A.submatrix p id).updateRow j (fun b => A i b) := by
    ext a b
    by_cases h : a = j
    · subst a
      simp only [Matrix.submatrix_apply, Function.update_self, id_eq, Matrix.updateRow_apply,
        ite_true]
    · simp only [Matrix.submatrix_apply, Function.update_of_ne h, id_eq, Matrix.updateRow_apply,
        ite_eq_right h]
  have hr : (fun b => A i b) = ∑ a, C i a • (A.submatrix p id) a := by
    funext b
    simpa only [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] using (congrArg (fun M : Matrix ι (Fin k) K => M i b) hC).symm
  rw [he, hr]
  simpa only [smul_eq_mul] using
    Matrix.det_updateRow_sum (A.submatrix p id) j (fun a => C i a)

theorem minimal_row_minor_coordinate_zero {K : Type*} [Field K] {m k : ℕ}
    (A : Matrix (Fin m) (Fin k) K) (p : Fin k → Fin m)
    (hp : (A.submatrix p id).det ≠ 0)
    (hmin : ∀ q : Fin k → Fin m, (A.submatrix q id).det ≠ 0 →
      (∑ j, (p j).val) ≤ ∑ j, (q j).val)
    (C : Matrix (Fin m) (Fin k) K) (hC : C * A.submatrix p id = A)
    (i : Fin m) (j : Fin k) (hij : i < p j) : C i j = 0 := by
  classical
  by_contra hne
  have hdet : (A.submatrix (Function.update p j i) id).det ≠ 0 := by
    rw [row_minor_update_det A p C hC i j]
    exact mul_ne_zero hne hp
  have hle := hmin (Function.update p j i) hdet
  have hfun : (fun a => (Function.update p j i a).val) =
      Function.update (fun a => (p a).val) j i.val := by
    funext a
    by_cases h : a = j <;> simp [h]
  rw [hfun, Finset.sum_update_of_mem (Finset.mem_univ j)] at hle
  have hsum : (∑ a, (p a).val) =
      (p j).val + ∑ a ∈ Finset.univ \ {j}, (p a).val := by
    simpa only [Function.update_eq_self] using
      (Finset.sum_update_of_mem (Finset.mem_univ j) (fun a => (p a).val) (p j).val)
  rw [hsum] at hle
  exact (not_le_of_gt hij) (Nat.le_of_add_le_add_right hle)

end Erdos3

end

section

namespace Erdos3

theorem det_eq_one_of_triangular_labels {K ι α : Type*} [CommRing K]
    [Fintype ι] [DecidableEq ι] [LinearOrder α]
    (B : Matrix ι ι K) (p : ι → α) (hp : Function.Injective p)
    (htri : ∀ i j, p i < p j → B i j = 0) (hdiag : ∀ i, B i i = 1) : B.det = 1 := by
  let : LinearOrder ι := LinearOrder.lift' p hp
  have hB : B.BlockTriangular OrderDual.toDual := fun {i j} hij => htri i j hij
  rw [Matrix.det_of_lowerTriangular B hB]
  simp only [hdiag, Finset.prod_const_one]

theorem lower_unitriangular_preserves_minimal_minor
    {K : Type*} [Field K] {m k : ℕ}
    (A : Matrix (Fin m) (Fin k) K) (p : Fin k → Fin m)
    (hp : (A.submatrix p id).det ≠ 0)
    (hmin : ∀ q : Fin k → Fin m, (A.submatrix q id).det ≠ 0 →
      (∑ j, (p j).val) ≤ ∑ j, (q j).val)
    (M : Matrix (Fin m) (Fin m) K)
    (hM : ∀ i j, i < j → M i j = 0) (hdiag : ∀ i, M i i = 1) :
    ((M * A).submatrix p id).det = (A.submatrix p id).det := by
  classical
  let B := A.submatrix p id
  let C := A * B⁻¹
  have hB : IsUnit B.det := isUnit_iff_ne_zero.mpr hp
  have hC : C * B = A := Matrix.nonsing_inv_mul_cancel_right B A hB
  have hCp : C.submatrix p id = 1 := by
    change (A * B⁻¹).submatrix p id = 1
    rw [Matrix.submatrix_mul A B⁻¹ p id id Function.bijective_id, Matrix.submatrix_id_id]
    exact Matrix.mul_nonsing_inv B hB
  have hzero (a : Fin m) (j : Fin k) (haj : a < p j) : C a j = 0 :=
    minimal_row_minor_coordinate_zero A p hp hmin C hC a j haj
  let T := (M * C).submatrix p id
  have hTtri (i j : Fin k) (hij : p i < p j) : T i j = 0 := by
    change ∑ a, M (p i) a * C a j = 0
    apply Finset.sum_eq_zero
    intro a _
    by_cases ha : a ≤ p i
    · rw [hzero a j (lt_of_le_of_lt ha hij), mul_zero]
    · rw [hM (p i) a (lt_of_not_ge ha), zero_mul]
  have hTdiag (i : Fin k) : T i i = 1 := by
    change ∑ a, M (p i) a * C a i = 1
    rw [Finset.sum_eq_single (p i)]
    · have hc : C (p i) i = 1 := by
        simpa using congrArg (fun N : Matrix (Fin k) (Fin k) K => N i i) hCp
      rw [hdiag, hc, one_mul]
    · intro a _ hne
      by_cases ha : a < p i
      · rw [hzero a i ha, mul_zero]
      · have hi : p i < a := lt_of_le_of_ne (le_of_not_gt ha) (Ne.symm hne)
        rw [hM (p i) a hi, zero_mul]
    · simp
  have hT : T.det = 1 := det_eq_one_of_triangular_labels T p
    (nonzero_row_minor_injective A p hp) hTtri hTdiag
  have he : (M * A).submatrix p id = T * B := by
    rw [← hC, ← Matrix.mul_assoc]
    exact Matrix.submatrix_mul (M * C) B p id id Function.bijective_id
  rw [he, Matrix.det_mul, hT, one_mul]

theorem exists_preserved_nonzero_row_minor
    {K : Type*} [Field K] {m k : ℕ}
    (A : Matrix (Fin m) (Fin k) K) (hA : LinearIndependent K A.col) :
    ∃ p : Fin k → Fin m, Function.Injective p ∧ (A.submatrix p id).det ≠ 0 ∧
      ∀ M : Matrix (Fin m) (Fin m) K,
        (∀ i j, i < j → M i j = 0) → (∀ i, M i i = 1) →
        ((M * A).submatrix p id).det = (A.submatrix p id).det := by
  obtain ⟨p, hp, hmin⟩ := exists_minimal_row_minor A hA
  exact ⟨p, nonzero_row_minor_injective A p hp, hp,
    fun M hM hdiag => lower_unitriangular_preserves_minimal_minor A p hp hmin M hM hdiag⟩

end Erdos3

end

end OAI
