import OAI.Combinatorics.Progressions.Dynamics.FlatPatchReset

namespace OAI

section

namespace Erdos3

noncomputable def nearestIntegerLift {m : ℕ} (x : Fin m → ℝ) : Fin m → ℤ :=
  fun i => round (x i)

theorem nearestIntegerLift_close {m : ℕ} (x : Fin m → ℝ) (i : Fin m) :
    |x i - (nearestIntegerLift x i : ℝ)| ≤ 1 / 2 := abs_sub_round (x i)

namespace PatchKernel

theorem buffered_lift_unique {m : ℕ} (Ψ : PatchKernel m) (x : Fin m → ℝ)
    (β γ : Fin m → ℤ) (hβ : ∀ i, |x i - (β i : ℝ)| ≤ 1 / 2)
    (hγ : Ψ.value (fun i => x i - (γ i : ℝ)) ≠ 0) : γ = β := by
  apply (constantSlots x).integer_unique (b := γ) (c := β) (by norm_num : (1 : ℝ) / 4 + 1 / 2 < 1)
  · intro i
    simpa only [TriangularSlots.residual, constantSlots, abs_sub_comm] using Ψ.support _ hγ i
  · intro i
    simpa only [TriangularSlots.residual, constantSlots, abs_sub_comm] using hβ i

theorem buffered_lift_value_eq {m : ℕ} (Ψ : PatchKernel m) (x : Fin m → ℝ)
    (β γ : Fin m → ℤ) (hβ : ∀ i, |x i - (β i : ℝ)| ≤ 1 / 2)
    (hmatch : Ψ.value (fun i => x i - (β i : ℝ)) ≠ 0 → γ = β)
    (f : (Fin m → ℤ) → ℝ) :
    Ψ.value (fun i => x i - (γ i : ℝ)) * f γ = Ψ.value (fun i => x i - (β i : ℝ)) * f β := by
  by_cases h : Ψ.value (fun i => x i - (β i : ℝ)) = 0
  · have hzero : Ψ.value (fun i => x i - (γ i : ℝ)) = 0 := by
      by_contra hγ
      exact hγ (by rw [Ψ.buffered_lift_unique x β γ hβ hγ, h])
    rw [hzero, h, zero_mul, zero_mul]
  · rw [hmatch h]

theorem buffered_sum_eq_nearest {m : ℕ} (Ψ : PatchKernel m) (x : Fin m → ℝ)
    (f : (Fin m → ℤ) → ℝ) :
    (∑' β, Ψ.value (fun i => x i - (β i : ℝ)) * f β) =
      Ψ.value (fun i => x i - (nearestIntegerLift x i : ℝ)) * f (nearestIntegerLift x) := by
  classical
  apply tsum_eq_single (nearestIntegerLift x)
  intro γ hγ
  have hzero : Ψ.value (fun i => x i - (γ i : ℝ)) = 0 := by
    by_contra hn
    exact hγ (Ψ.buffered_lift_unique x _ γ (nearestIntegerLift_close x) hn)
  rw [hzero, zero_mul]

end PatchKernel
end Erdos3

end

end OAI
