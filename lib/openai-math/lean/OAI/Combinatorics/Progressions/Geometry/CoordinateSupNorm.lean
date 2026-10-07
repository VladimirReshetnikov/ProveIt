import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

noncomputable def coordinateL2Norm (v : ι → ℝ) : ℝ := Real.sqrt (∑ i, v i ^ 2)

theorem coordinateL2Norm_nonneg (v : ι → ℝ) : 0 ≤ coordinateL2Norm v := Real.sqrt_nonneg _

theorem coordinateL2Norm_le_card_bound (v : ι → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hv : ∀ i, |v i| ≤ B) : coordinateL2Norm v ≤ (Fintype.card ι + 1) * B := by
  unfold coordinateL2Norm
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hsum : (∑ i, v i ^ 2) ≤ (Fintype.card ι : ℝ) * B ^ 2 := by
    calc
      _ ≤ ∑ _i : ι, B ^ 2 := Finset.sum_le_sum fun i _ =>
        sq_le_sq.mpr ((hv i).trans_eq (abs_of_nonneg hB).symm)
      _ = _ := by simp
  apply hsum.trans
  rw [mul_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg B)
  nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card ι), sq_nonneg (Fintype.card ι : ℝ)]

theorem coordinateL2Norm_matrix_le (A : κ → ι → ℝ) (v : ι → ℝ) :
    coordinateL2Norm (fun k => ∑ i, A k i * v i) ≤
      Real.sqrt (∑ k, ∑ i, A k i ^ 2) * coordinateL2Norm v := by
  have h : (∑ k, (∑ i, A k i * v i) ^ 2) ≤
      (∑ k, ∑ i, A k i ^ 2) * ∑ i, v i ^ 2 := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun k _ => Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (A k) v)
  exact (Real.sqrt_le_sqrt h).trans_eq (Real.sqrt_mul
    (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _))) _)

theorem coordinateL2Norm_matrix_entry_bound (A : κ → ι → ℝ) (B : ℝ)
    (hB : 0 ≤ B) (hA : ∀ k i, |A k i| ≤ B) (v : ι → ℝ) :
    coordinateL2Norm (fun k => ∑ i, A k i * v i) ≤
      ((Fintype.card κ : ℝ) + Fintype.card ι + 1) * (B + 1) * coordinateL2Norm v := by
  have hsum : (∑ k, ∑ i, A k i ^ 2) ≤
      (Fintype.card κ : ℝ) * Fintype.card ι * B ^ 2 := by
    calc
      (∑ k, ∑ i, A k i ^ 2) ≤ ∑ _k : κ, ∑ _i : ι, B ^ 2 := by
        apply Finset.sum_le_sum
        intro k _
        apply Finset.sum_le_sum
        intro i _
        exact sq_le_sq.mpr ((hA k i).trans_eq (abs_of_nonneg hB).symm)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  have hn : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have hm : 0 ≤ (Fintype.card κ : ℝ) := Nat.cast_nonneg _
  have hdim : (Fintype.card κ : ℝ) * Fintype.card ι ≤
      ((Fintype.card κ : ℝ) + Fintype.card ι + 1) ^ 2 := by nlinarith [sq_nonneg ((Fintype.card κ : ℝ) - Fintype.card ι)]
  have hsq : B ^ 2 ≤ (B + 1) ^ 2 := by nlinarith
  have hroot : Real.sqrt (∑ k, ∑ i, A k i ^ 2) ≤
      ((Fintype.card κ : ℝ) + Fintype.card ι + 1) * (B + 1) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, hsum.trans ?_⟩
    rw [mul_pow]
    exact mul_le_mul hdim hsq (sq_nonneg _) (sq_nonneg _)
  exact (coordinateL2Norm_matrix_le A v).trans
    (mul_le_mul_of_nonneg_right hroot (coordinateL2Norm_nonneg v))

end Erdos3

end

section

namespace Erdos3

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

omit [Fintype κ] in
theorem coordinateLinearMap_apply_sum (A : (ι → ℝ) →L[ℝ] (κ → ℝ)) (v : ι → ℝ) (k : κ) :
    A v k = ∑ i, A (Pi.single i 1) k * v i := by
  have hv : v = ∑ i, v i • Pi.single i (1 : ℝ) := by
    simp only [← Pi.single_smul, smul_eq_mul, mul_one, LinearMap.sum_single_apply]
  calc
    A v k = A (∑ i, v i • Pi.single i (1 : ℝ)) k := congrArg (fun w => A w k) hv
    _ = _ := by simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem coordinateLinearMap_L2_bound (A : (ι → ℝ) →L[ℝ] (κ → ℝ)) (B : ℝ)
    (hB : 0 ≤ B) (hA : ∀ k i, |A (Pi.single i 1) k| ≤ B) (v : ι → ℝ) :
    coordinateL2Norm (A v) ≤
      ((Fintype.card κ : ℝ) + Fintype.card ι + 1) * (B + 1) * coordinateL2Norm v := by
  have heq : A v = fun k => ∑ i, A (Pi.single i 1) k * v i :=
    funext (coordinateLinearMap_apply_sum A v)
  rw [heq]
  exact coordinateL2Norm_matrix_entry_bound (fun k i => A (Pi.single i 1) k) B hB hA v

end Erdos3

end

section

namespace Erdos3

theorem abs_coordinate_le_coordinateL2Norm {ι : Type*} [Fintype ι] (v : ι → ℝ) (i : ι) :
    |v i| ≤ coordinateL2Norm v := by
  have hsq : (v i) ^ 2 ≤ ∑ j, (v j) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
  have hsum : 0 ≤ ∑ j, (v j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg (v j)
  have hroot := Real.sq_sqrt hsum
  have hnonneg := coordinateL2Norm_nonneg v
  unfold coordinateL2Norm at *
  nlinarith [sq_abs (v i), abs_nonneg (v i)]

theorem norm_le_coordinateL2Norm {ι : Type*} [Fintype ι] (v : ι → ℝ) :
    ‖v‖ ≤ coordinateL2Norm v := by
  apply (pi_norm_le_iff_of_nonneg (coordinateL2Norm_nonneg v)).mpr
  intro i
  simpa only [Real.norm_eq_abs] using abs_coordinate_le_coordinateL2Norm v i

end Erdos3

end

end OAI
