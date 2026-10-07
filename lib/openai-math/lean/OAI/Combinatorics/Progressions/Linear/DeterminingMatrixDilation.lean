import OAI.Combinatorics.Progressions.Estimates.AveragedModeledPatchTransfer

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {d m : ℕ}

def dilatedIntegerMatrix (q : ℕ) (M : Fin m → Fin d → ℤ) : Fin m → Fin d → ℤ :=
  fun i j => (q : ℤ) * M i j

theorem dilatedIntegerMatrix_entry_dvd (q : ℕ) (M : Fin m → Fin d → ℤ)
    (i : Fin m) (j : Fin d) : (q : ℤ) ∣ dilatedIntegerMatrix q M i j :=
  dvd_mul_right _ _

theorem dilatedIntegerMatrix_nonzero_original (q : ℕ) (M : Fin m → Fin d → ℤ)
    {i : Fin m} {j : Fin d} (h : dilatedIntegerMatrix q M i j ≠ 0) : M i j ≠ 0 := by
  intro hz
  exact h (by simp [dilatedIntegerMatrix, hz])

theorem dilatedIntegerMatrix_nonzero_iff (q : ℕ) (M : Fin m → Fin d → ℤ)
    (hq : 0 < q) (i : Fin m) (j : Fin d) :
    dilatedIntegerMatrix q M i j ≠ 0 ↔ M i j ≠ 0 := by
  have hqz : (q : ℤ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  simp only [dilatedIntegerMatrix, ne_eq, mul_eq_zero, hqz, false_or]

theorem dilatedIntegerMatrix_support_relation (q : ℕ) (M : Fin m → Fin d → ℤ)
    (R : Fin m → Fin d → Prop) (hR : ∀ i j, M i j ≠ 0 → R i j) :
    ∀ i j, dilatedIntegerMatrix q M i j ≠ 0 → R i j := by
  intro i j hij
  exact hR i j (dilatedIntegerMatrix_nonzero_original q M hij)

theorem dilatedIntegerMatrix_weights (q : ℕ) (M : Fin m → Fin d → ℤ)
    (v : Fin m → ℕ) (w : Fin d → ℕ)
    (hM : ∀ i j, M i j ≠ 0 → w j ≤ v i) :
    ∀ i j, dilatedIntegerMatrix q M i j ≠ 0 → w j ≤ v i :=
  dilatedIntegerMatrix_support_relation q M (fun i j => w j ≤ v i) hM

theorem realIntegerMatrix_dilated_div (q : ℕ) (M : Fin m → Fin d → ℤ)
    (hq : 0 < q) (x : Fin d → ℝ) :
    realIntegerMatrix (dilatedIntegerMatrix q M) (fun j => x j / (q : ℝ)) =
      realIntegerMatrix M x := by
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  funext i
  apply Finset.sum_congr rfl
  intro j hj
  simp only [dilatedIntegerMatrix, Int.cast_mul, Int.cast_natCast]
  field_simp

theorem dilatedIntegerMatrix_row_abs_sum (q : ℕ) (M : Fin m → Fin d → ℤ)
    (i : Fin m) :
    (∑ j, |(dilatedIntegerMatrix q M i j : ℝ)|) =
      (q : ℝ) * ∑ j, |(M i j : ℝ)| := by
  simp only [dilatedIntegerMatrix, Int.cast_mul, Int.cast_natCast, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg q : (0 : ℝ) ≤ q), Finset.mul_sum]

theorem dilatedIntegerMatrix_row_abs_sum_le (q : ℕ) (M : Fin m → Fin d → ℤ)
    (i : Fin m) {K : ℝ} (hK : (∑ j, |(M i j : ℝ)|) ≤ K) :
    (∑ j, |(dilatedIntegerMatrix q M i j : ℝ)|) ≤ (q : ℝ) * K := by
  rw [dilatedIntegerMatrix_row_abs_sum]
  exact mul_le_mul_of_nonneg_left hK (Nat.cast_nonneg q)

theorem dilatedIntegerMatrix_row_abs_sum_le_uniform (q : ℕ) (M : Fin m → Fin d → ℤ)
    (K : ℝ) (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) :
    ∀ i, (∑ j, |(dilatedIntegerMatrix q M i j : ℝ)|) ≤ (q : ℝ) * K :=
  fun i => dilatedIntegerMatrix_row_abs_sum_le q M i (hM i)

theorem dilatedIntegerMatrix_projection_columns {A : Type*} [AddCommGroup A]
    (q : ℕ) (M : Fin m → Fin d → ℤ) (π : (Fin m → ℤ) →+ A)
    (hπ : ∀ j, π (fun i => M i j) = 0) :
    ∀ j, π (fun i => dilatedIntegerMatrix q M i j) = 0 := by
  intro j
  change π ((q : ℤ) • (fun i => M i j)) = 0
  rw [map_zsmul, hπ, zsmul_zero]

theorem recoveredIntegerLift_dilated_residue (q : ℕ) (M : Fin m → Fin d → ℤ)
    (c : Fin m → ℤ) (k : Fin d → ℤ) :
    (fun i => (recoveredIntegerLift (dilatedIntegerMatrix q M) c k i : ZMod q)) =
      fun i => (c i : ZMod q) :=
  recoveredIntegerLift_residue _ q (dilatedIntegerMatrix_entry_dvd q M) c k

theorem recoveredIntegerLift_dilated_projection {A : Type*} [AddCommGroup A]
    (q : ℕ) (M : Fin m → Fin d → ℤ) (π : (Fin m → ℤ) →+ A)
    (hπ : ∀ j, π (fun i => M i j) = 0) (c : Fin m → ℤ) (k : Fin d → ℤ) :
    π (recoveredIntegerLift (dilatedIntegerMatrix q M) c k) = π c :=
  recoveredIntegerLift_projection _ π (dilatedIntegerMatrix_projection_columns q M π hπ) c k

theorem recoveredIntegerLift_dilated_discrete_data {A X : Type*} [AddCommGroup A]
    (q : ℕ) (M : Fin m → Fin d → ℤ) (π : (Fin m → ℤ) →+ A)
    (hπ : ∀ j, π (fun i => M i j) = 0)
    (F : (Fin m → ZMod q) → A → X) (c : Fin m → ℤ) (k : Fin d → ℤ) :
    F (fun i => (recoveredIntegerLift (dilatedIntegerMatrix q M) c k i : ZMod q))
      (π (recoveredIntegerLift (dilatedIntegerMatrix q M) c k)) =
      F (fun i => (c i : ZMod q)) (π c) :=
  recoveredIntegerLift_discrete_data _ q (dilatedIntegerMatrix_entry_dvd q M) π
    (dilatedIntegerMatrix_projection_columns q M π hπ) F c k

theorem recoveredSmallLift_dilated_div (q : ℕ) (M : Fin m → Fin d → ℤ)
    (hq : 0 < q) (a e : Fin d → ℝ) (c : Fin m → ℤ) :
    recoveredSmallLift (dilatedIntegerMatrix q M)
      (fun j => a j / (q : ℝ)) c (fun j => e j / (q : ℝ)) =
      recoveredSmallLift M a c e := by
  have hqr : (q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hq
  funext i
  apply congrArg (fun x : ℝ => x - c i)
  apply Finset.sum_congr rfl
  intro j hj
  simp only [dilatedIntegerMatrix, Int.cast_mul, Int.cast_natCast]
  field_simp

end Erdos3

end

end OAI
