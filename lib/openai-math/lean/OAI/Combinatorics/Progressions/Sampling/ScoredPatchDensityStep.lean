import OAI.Combinatorics.Progressions.Dynamics.ResourceControlledPatchReset
import OAI.Combinatorics.Progressions.Probability.RelativeSourceDensityParameter

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem positive_patch_score_target_lt_one {s d N : ℕ} (A : PolynomialPatch Unit s d)
    (f : ℕ → ℝ) (hf : ∀ n < N, f n ≤ 1) {b : ℝ}
    (hscore : 0 < 𝔼 n : Fin N, (f n.val - b) * A.value (fun _ => (n.val : ℝ))) : b < 1 := by
  by_contra hb
  have hb1 : 1 ≤ b := le_of_not_gt hb
  have hnonpos : (𝔼 n : Fin N, (f n.val - b) * A.value (fun _ => (n.val : ℝ))) ≤ 0 := by
    calc
      _ ≤ 𝔼 _n : Fin N, (0 : ℝ) := by
        apply Finset.expect_le_expect
        intro n _
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hf n.val n.isLt]) (A.value_mem_Icc _).1
      _ = 0 := by simp
  exact (not_lt_of_ge hnonpos) hscore

theorem scored_patch_density_step (s : ℕ) :
    ∃ (C : ℝ) (P : ℕ), 1 ≤ C ∧ 0 < P ∧
      ∀ (d N M a₀ q₀ : ℕ) (U R V G δ : ℝ) (A : PolynomialPatch Unit s d) (f : ℕ → ℝ),
        1 < N → 0 < q₀ → (∀ n < M, a₀ + q₀ * n < N) →
        (∀ n < N, f n ∈ Set.Icc (0 : ℝ) 1) → 1 ≤ U →
        Real.log N - U ≤ Real.log M → (A.kernel.lip : ℝ) + 1 ≤ Real.exp U →
        Real.log ((d : ℝ) + 1) ≤ R → Real.log U ≤ V →
        Real.log (4 * (P : ℝ) * (Real.log (2 * C) + 3)) + (2 * s * s + 1 : ℕ) * R + V ≤
          Real.log (Real.log N) →
        let α := 𝔼 n : Fin N, f n.val
        0 < α → 0 < G → δ ≤ Real.log G → 2 ≤ densityParameter α - δ →
        Real.exp (-U) ≤ (𝔼 n : Fin M,
          (f (a₀ + q₀ * n.val) - G * α) * A.value (fun _ => (n.val : ℝ))) →
        ∃ q a len : ℕ, 0 < q ∧ 1 < len ∧ (∀ n < len, a + q * n < N) ∧
          Real.log (Real.log N) - (Real.log (4 * (P : ℝ)) + (2 * s * s : ℕ) * R) ≤
            Real.log (Real.log len) ∧
          G * α < (𝔼 n : Fin len, f (a + q * n.val)) ∧
          densityParameter (𝔼 n : Fin len, f (a + q * n.val)) ≤ densityParameter α - δ := by
  obtain ⟨C, P, hC, hP, hreset⟩ := resource_controlled_patch_reset s
  refine ⟨C, P, hC, hP, ?_⟩
  intro d N M a₀ q₀ U R V G δ A f hN hq₀ hslice hf hU hM hLip hR hV hsize α hα hG hδ hroom hscore
  have hb1 : G * α < 1 := positive_patch_score_target_lt_one A
    (fun n => f (a₀ + q₀ * n)) (fun n hn => (hf _ (hslice n hn)).2)
    ((Real.exp_pos (-U)).trans_le hscore)
  have hb : G * α ∈ Set.Icc (0 : ℝ) 1 := ⟨(mul_pos hG hα).le, hb1.le⟩
  obtain ⟨q, a, len, hq, hlen, hin, hloss, hdense⟩ :=
    hreset d N M a₀ q₀ U R V A f hN hq₀ hslice hf hU hM hLip hR hV hsize (G * α) hb hscore
  refine ⟨q, a, len, hq, hlen, hin, hloss, hdense, ?_⟩
  exact densityParameter_drop hα hG hdense.le (le_max_right _ _) hδ hroom

end Erdos3

end

end OAI
