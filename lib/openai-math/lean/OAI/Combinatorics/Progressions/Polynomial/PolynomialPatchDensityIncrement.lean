import OAI.Combinatorics.Progressions.Dynamics.ConstructLayerResetScales

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem polynomial_patch_density_increment (s : ℕ) :
    ∃ (K : ℝ) (p : ℕ), 1 ≤ K ∧ 0 < p ∧
      ∀ (d N T : ℕ) (A : PolynomialPatch Unit s d), 0 < T →
        K * ((d : ℝ) + 1) ≤ T →
        (2 : ℝ) ^ (s + 1) * s < T → 24 * (d : ℝ) * s < T →
        T ^ ((2 * p) ^ s * (d + 1) ^ (2 * s * s)) ≤ N →
        ∀ f : ℕ → ℝ, (∀ n < N, f n ∈ Set.Icc (0 : ℝ) 1) →
        ∀ b σ : ℝ, b ∈ Set.Icc (0 : ℝ) 1 → 0 < σ →
        8 * (A.kernel.lip : ℝ) * d * s * (2 : ℝ) ^ s ≤ σ * T →
        (2 : ℝ) ^ (2 * s + 3) ≤ σ * T →
        σ ≤ (𝔼 n : Fin N, (f n.val - b) * A.value (fun _ => (n.val : ℝ))) →
        ∃ q a len : ℕ, 0 < q ∧ T ≤ len ∧
          (∀ n < len, a + q * n < N) ∧ b < 𝔼 n : Fin len, f (a + q * n.val) := by
  obtain ⟨K, p, hK, hp, hpartition⟩ := exists_uniform_coordinate_partition_bound.{0} s
  refine ⟨K, p, hK, hp, ?_⟩
  intro d N T A hT hscale hlift hfreeze hsize f hf b σ hb hσ hroom hlength hscore
  let S := powerLayerResetScales hp (by linarith : 0 ≤ K) A.kernel.lip.coe_nonneg
    hT hσ hpartition hscale hlift hfreeze hroom hlength
  have hN : S.threshold 1 ≤ N := by
    change T ^ ((2 * (p * (d + 1) ^ (2 * s))) ^ s) ≤ N
    rw [layerReset_exponent_polynomial]
    exact hsize
  have hs : S.score 1 ≤ 𝔼 n : Fin N, (f n.val - b) * A.value (fun _ => (n.val : ℝ)) := by
    change σ / (2 : ℝ) ^ 1 ≤ _
    exact (div_le_self hσ.le (by norm_num)).trans hscore
  obtain ⟨q, a, len, hq, hlen, hin, hdense⟩ := S.density_increment A le_rfl le_rfl hN f hf hb hs
  change layerResetThreshold s (p * (d + 1) ^ (2 * s)) T (s + 1) ≤ len at hlen
  rw [layerResetThreshold_terminal] at hlen
  exact ⟨q, a, len, hq, hlen, hin, hdense⟩

end Erdos3

end

end OAI
