import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.LinearAlgebra.Basis.Defs
import OAI.Combinatorics.Progressions.Linear.FiniteSpanRounding
import OAI.Combinatorics.Progressions.Sampling.RealGridSeparation

namespace OAI

section

namespace Erdos3

theorem rational_abs_real_le_numerator (q : ℚ) :
    |(q : ℝ)| ≤ (q.num.natAbs : ℝ) := by
  have hdenabs : |(q.den : ℝ)| = (q.den : ℝ) := abs_of_nonneg (Nat.cast_nonneg _)
  rw [Rat.cast_def, abs_div, hdenabs]
  have hden : (1 : ℝ) ≤ q.den := by exact_mod_cast q.den_pos
  simpa only [Nat.cast_natAbs, Int.cast_abs] using div_le_self (abs_nonneg (q.num : ℝ)) hden

theorem RationalHeightLE.abs_real_le {q : ℚ} {H : ℕ} (hq : RationalHeightLE q H) :
    |(q : ℝ)| ≤ H :=
  (rational_abs_real_le_numerator q).trans (Nat.cast_le.mpr hq.1)

variable {ι κ V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]

theorem boundedSpanCell_linear_bound (v : ι → V) (f : V →ₗ[ℝ] ℝ) {c H : ℝ}
    (hc : 0 ≤ c) (hv : ∀ i, |f (v i)| ≤ H) {x : V} (hx : x ∈ boundedSpanCell v c) :
    |f x| ≤ Fintype.card ι * c * H := by
  classical
  obtain ⟨t, ht, rfl⟩ := hx
  simp only [map_sum, map_smul, smul_eq_mul]
  calc
    _ ≤ ∑ i, |t i * f (v i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : ι, c * H := by
      apply Finset.sum_le_sum
      intro i _
      have hi := ht i (Set.mem_univ i)
      rw [abs_mul, abs_of_nonneg hi.1]
      exact mul_le_mul hi.2 (hv i) (abs_nonneg _) hc
    _ = _ := by simp [mul_assoc]

theorem boundedSpanCell_coordinate_bound (e : Module.Basis κ ℝ V) (v : ι → V) {c H : ℝ}
    (hc : 0 ≤ c) (hv : ∀ i j, |e.repr (v i) j| ≤ H) {x : V}
    (hx : x ∈ boundedSpanCell v c) (j : κ) :
    |e.repr x j| ≤ Fintype.card ι * c * H :=
  boundedSpanCell_linear_bound v (e.coord j) hc (fun i => hv i j) hx

end Erdos3

end

section

namespace Erdos3

open scoped Matrix NNReal

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem real_matrix_denominator_grid (Q : Matrix ι κ ℚ) (l : ℕ) (x : κ → ℝ)
    (hx : x ∈ realDenominatorGrid l) :
    (fun i j => (Q i j : ℝ)) *ᵥ x ∈ realDenominatorGrid (matrixDenominator Q * l) := by
  classical
  obtain ⟨z, hz⟩ := hx
  have hcoef (i : ι) (j : κ) :
      ((clearedMatrix Q i j : ℤ) : ℝ) = (matrixDenominator Q : ℝ) * (Q i j : ℝ) := by
    have h := congrFun (congrFun (clearedMatrix_cast Q) i) j
    change ((clearedMatrix Q i j : ℤ) : ℚ) = (matrixDenominator Q : ℚ) * Q i j at h
    exact_mod_cast h
  refine ⟨clearedMatrix Q *ᵥ z, funext fun i => ?_⟩
  change (((clearedMatrix Q *ᵥ z) i : ℤ) : ℝ) =
    ((matrixDenominator Q * l : ℕ) : ℝ) * ((fun i j => (Q i j : ℝ)) *ᵥ x) i
  simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul, Nat.cast_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hj : (z j : ℝ) = (l : ℝ) * x j := congrFun hz j
  rw [hcoef, hj]
  ring

omit [Fintype ι] in

theorem abs_matrix_mulVec_le (Q : Matrix ι κ ℝ) (H : ℝ≥0)
    (hQ : ∀ i j, |Q i j| ≤ H) (x : κ → ℝ) (i : ι) :
    |(Q *ᵥ x) i| ≤ ((Fintype.card κ : ℝ) + 1) * (H + 1) * ‖x‖ := by
  classical
  calc
    _ ≤ ∑ j, |Q i j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : κ, (H : ℝ) * ‖x‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (hQ i j) (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j)
        (abs_nonneg _) H.coe_nonneg
    _ = (Fintype.card κ : ℝ) * H * ‖x‖ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ ≤ _ := by gcongr <;> linarith

theorem rational_matrix_kernel_separation (Q : Matrix ι κ ℚ) (H : ℝ≥0)
    (hQ : ∀ i j, |(Q i j : ℝ)| ≤ H) (l : ℕ) (hl : 0 < l) (x y : κ → ℝ)
    (hx : x ∈ realDenominatorGrid l)
    (hy : (fun i j => (Q i j : ℝ)) *ᵥ y = 0)
    (hnear : ((matrixDenominator Q * l : ℕ) : ℝ) *
      (((Fintype.card κ : ℝ) + 1) * (H + 1)) * dist x y < 1) :
    (fun i j => (Q i j : ℝ)) *ᵥ x = 0 := by
  have hD : 0 < matrixDenominator Q * l := Nat.mul_pos (matrixDenominator_pos Q) hl
  apply eq_zero_of_mem_realDenominatorGrid_of_abs_lt hD (real_matrix_denominator_grid Q l x hx)
  intro i
  have hbound := abs_matrix_mulVec_le (fun i j => (Q i j : ℝ)) H hQ (x - y) i
  have heq := Matrix.mulVec_sub (fun i j => (Q i j : ℝ)) x y
  rw [hy, sub_zero] at heq
  rw [heq, ← dist_eq_norm] at hbound
  apply (lt_div_iff₀ (show (0 : ℝ) < ((matrixDenominator Q * l : ℕ) : ℝ) by exact_mod_cast hD)).mpr
  calc
    |((fun i j => (Q i j : ℝ)) *ᵥ x) i| * ((matrixDenominator Q * l : ℕ) : ℝ) ≤
        (((Fintype.card κ : ℝ) + 1) * (H + 1) * dist x y) * ((matrixDenominator Q * l : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right hbound (by positivity)
    _ < 1 := by nlinarith [hnear]

end Erdos3

end

end OAI
