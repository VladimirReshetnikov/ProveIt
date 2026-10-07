import Mathlib

namespace OAI

section

namespace Erdos3

theorem symmetricInterval_card (N : ℕ) :
    (Finset.Icc (-(N : ℤ)) (N : ℤ)).card = 2 * N + 1 := by
  rw [Int.card_Icc]
  omega

theorem symmetricInterval_sum_dilation (f : ℤ → ℝ) (hf : ∀ n, 0 ≤ f n)
    (a : ℤ) (ha : a ≠ 0) (H N : ℕ) (hsize : |(a : ℝ)| * H ≤ N) :
    (∑ n ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), f (a * n)) ≤
      ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), f n := by
  classical
  have hsizeZ : |a| * (H : ℤ) ≤ (N : ℤ) := by exact_mod_cast hsize
  have hinj : Function.Injective (fun n : ℤ => a * n) := fun _ _ h => mul_left_cancel₀ ha h
  have hsub : (Finset.Icc (-(H : ℤ)) (H : ℤ)).image (fun n => a * n) ⊆
      Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    intro n hn
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hn
    have hmabs : |m| ≤ (H : ℤ) := abs_le.mpr (Finset.mem_Icc.mp hm)
    apply Finset.mem_Icc.mpr
    apply abs_le.mp
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hmabs (abs_nonneg a)).trans hsizeZ
  rw [← Finset.sum_image (fun _ _ _ _ h => hinj h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hf n)

end Erdos3

end

end OAI
