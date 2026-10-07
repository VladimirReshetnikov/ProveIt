import OAI.Combinatorics.Progressions.Lattices.BufferedIntegerLift

namespace OAI

section

namespace Erdos3.PatchKernel

theorem buffered_family_lift_value_eq {m : ℕ} (Ψ : (Fin m → ℤ) → PatchKernel m)
    (x : Fin m → ℝ) (β γ : Fin m → ℤ)
    (hβ : ∀ i, |x i - (β i : ℝ)| ≤ 1 / 2)
    (hmatch : (Ψ β).value (fun i => x i - (β i : ℝ)) ≠ 0 → γ = β)
    (f : (Fin m → ℤ) → ℝ) :
    (Ψ γ).value (fun i => x i - (γ i : ℝ)) * f γ =
      (Ψ β).value (fun i => x i - (β i : ℝ)) * f β := by
  by_cases h : (Ψ β).value (fun i => x i - (β i : ℝ)) = 0
  · have hzero : (Ψ γ).value (fun i => x i - (γ i : ℝ)) = 0 := by
      by_contra hγ
      have heq := (Ψ γ).buffered_lift_unique x β γ hβ hγ
      exact hγ (by simpa only [heq] using h)
    rw [hzero, h, zero_mul, zero_mul]
  · rw [hmatch h]

theorem buffered_family_sum_eq_nearest {m : ℕ} (Ψ : (Fin m → ℤ) → PatchKernel m)
    (x : Fin m → ℝ) (f : (Fin m → ℤ) → ℝ) :
    (∑' β, (Ψ β).value (fun i => x i - (β i : ℝ)) * f β) =
      (Ψ (nearestIntegerLift x)).value (fun i => x i - (nearestIntegerLift x i : ℝ)) *
        f (nearestIntegerLift x) := by
  classical
  apply tsum_eq_single (nearestIntegerLift x)
  intro γ hγ
  have hzero : (Ψ γ).value (fun i => x i - (γ i : ℝ)) = 0 := by
    by_contra hn
    exact hγ ((Ψ γ).buffered_lift_unique x _ γ (nearestIntegerLift_close x) hn)
  rw [hzero, zero_mul]

end Erdos3.PatchKernel

end

end OAI
