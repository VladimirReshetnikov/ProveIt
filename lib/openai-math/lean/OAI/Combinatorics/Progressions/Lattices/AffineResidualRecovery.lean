import OAI.Combinatorics.Progressions.Linear.WeightedPatchKernel

namespace OAI

section

namespace Erdos3

open scoped NNReal

def recoveredIntegerLift {d m : ℕ} (M : Fin m → Fin d → ℤ) (c : Fin m → ℤ)
    (k : Fin d → ℤ) : Fin m → ℤ := fun i => c i + ∑ j, M i j * k j

noncomputable def realIntegerMatrix {d m : ℕ} (M : Fin m → Fin d → ℤ)
    (x : Fin d → ℝ) : Fin m → ℝ := fun i => ∑ j, (M i j : ℝ) * x j

noncomputable def recoveredSmallLift {d m : ℕ} (M : Fin m → Fin d → ℤ)
    (a : Fin d → ℝ) (c : Fin m → ℤ) (e : Fin d → ℝ) : Fin m → ℝ :=
  fun i => (∑ j, (M i j : ℝ) * (a j - e j)) - c i

theorem recoveredSmallLift_at_integer {d m : ℕ} (M : Fin m → Fin d → ℤ)
    (a x : Fin d → ℝ) (c : Fin m → ℤ) (k : Fin d → ℤ) :
    recoveredSmallLift M a c (fun j => (k j : ℝ) - (x - a) j) =
      fun i => realIntegerMatrix M x i - (recoveredIntegerLift M c k i : ℝ) := by
  funext i
  simp only [recoveredSmallLift, realIntegerMatrix, recoveredIntegerLift, Pi.sub_apply]
  push_cast
  simp only [mul_sub, Finset.sum_sub_distrib]
  ring

theorem recoveredSmallLift_lipschitz {d m : ℕ} (M : Fin m → Fin d → ℤ)
    (a : Fin d → ℝ) (c : Fin m → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) : LipschitzWith K (recoveredSmallLift M a c) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  apply (dist_pi_le_iff (mul_nonneg K.coe_nonneg dist_nonneg)).mpr
  intro i
  simp only [recoveredSmallLift, Real.dist_eq]
  rw [sub_sub_sub_cancel_right, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j, |(M i j : ℝ) * (a j - x j) - (M i j : ℝ) * (a j - y j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |(M i j : ℝ)| * dist x y := by
      apply Finset.sum_le_sum
      intro j _
      rw [← mul_sub, abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa only [sub_sub_sub_cancel_left, abs_sub_comm, Real.dist_eq] using dist_le_pi_dist x y j
    _ = (∑ j, |(M i j : ℝ)|) * dist x y := (Finset.sum_mul _ _ _).symm
    _ ≤ K * dist x y := mul_le_mul_of_nonneg_right (hM i) dist_nonneg

noncomputable def recoveredCellKernel {d m : ℕ} (Φ : PatchKernel d) (Ψ : PatchKernel m)
    (M : Fin m → Fin d → ℤ) (a : Fin d → ℝ) (c : Fin m → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) : PatchKernel d :=
  Φ.weightAlong Ψ (recoveredSmallLift M a c) K (recoveredSmallLift_lipschitz M a c K hM)

@[simp] theorem recoveredCellKernel_lip {d m : ℕ} (Φ : PatchKernel d) (Ψ : PatchKernel m)
    (M : Fin m → Fin d → ℤ) (a : Fin d → ℝ) (c : Fin m → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) :
    (recoveredCellKernel Φ Ψ M a c K hM).lip = Φ.lip + Ψ.lip * K := rfl

@[simp] theorem recoveredCellKernel_value {d m : ℕ} (Φ : PatchKernel d) (Ψ : PatchKernel m)
    (M : Fin m → Fin d → ℤ) (a : Fin d → ℝ) (c : Fin m → ℤ) (K : ℝ≥0)
    (hM : ∀ i, (∑ j, |(M i j : ℝ)|) ≤ K) (e : Fin d → ℝ) :
    (recoveredCellKernel Φ Ψ M a c K hM).value e = Φ.value e * Ψ.value (recoveredSmallLift M a c e) := rfl

end Erdos3

end

end OAI
