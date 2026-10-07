import OAI.Combinatorics.Progressions.Polynomial.SlicedPolynomialPatchReset

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem resource_controlled_patch_reset (s : ℕ) :
    ∃ (C : ℝ) (P : ℕ), 1 ≤ C ∧ 0 < P ∧
      ∀ (d N M a₀ q₀ : ℕ) (U R V : ℝ) (A : PolynomialPatch Unit s d) (f : ℕ → ℝ),
        1 < N → 0 < q₀ → (∀ n < M, a₀ + q₀ * n < N) →
        (∀ n < N, f n ∈ Set.Icc (0 : ℝ) 1) → 1 ≤ U →
        Real.log N - U ≤ Real.log M → (A.kernel.lip : ℝ) + 1 ≤ Real.exp U →
        Real.log ((d : ℝ) + 1) ≤ R → Real.log U ≤ V →
        Real.log (4 * (P : ℝ) * (Real.log (2 * C) + 3)) + (2 * s * s + 1 : ℕ) * R + V ≤
          Real.log (Real.log N) →
        ∀ b : ℝ, b ∈ Set.Icc (0 : ℝ) 1 →
        Real.exp (-U) ≤ (𝔼 n : Fin M,
          (f (a₀ + q₀ * n.val) - b) * A.value (fun _ => (n.val : ℝ))) →
        ∃ q a len : ℕ, 0 < q ∧ 1 < len ∧ (∀ n < len, a + q * n < N) ∧
          Real.log (Real.log N) - (Real.log (4 * (P : ℝ)) + (2 * s * s : ℕ) * R) ≤
            Real.log (Real.log len) ∧
          b < 𝔼 n : Fin len, f (a + q * n.val) := by
  obtain ⟨C, P, hC, hP, hreset⟩ := sliced_polynomial_patch_reset s
  refine ⟨C, P, hC, hP, ?_⟩
  intro d N M a₀ q₀ U R V A f hN hq₀ hslice hf hU hM hLip hR hV hsize b hb hscore
  have hcutoff := patch_reset_cutoff_of_loglog hC (by exact_mod_cast hP : (0 : ℝ) < P)
    hU hN d (2 * s * s) hR hV hsize
  have hcutoff' : 4 * (P * (d + 1) ^ (2 * s * s) : ℕ) *
      (Real.log (2 * C) + Real.log ((d : ℝ) + 1) + 2 * U) ≤ Real.log N := by
    push_cast
    simpa only [mul_assoc] using hcutoff
  obtain ⟨q, a, len, hq, hlen, hin, _, hloss, hdense⟩ :=
    hreset d N M a₀ q₀ U A f hq₀ hslice hf hU hM hLip b hb hcutoff' hscore
  refine ⟨q, a, len, hq, hlen, hin, ?_, hdense⟩
  have hR' := mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg (α := ℝ) (2 * s * s))
  linarith

end Erdos3

end

end OAI
