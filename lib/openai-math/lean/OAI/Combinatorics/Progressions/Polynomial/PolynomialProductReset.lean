import OAI.Combinatorics.Progressions.Dynamics.PatchResetBudget

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem polynomial_patch_score_le_one {s d N : ℕ} (A : PolynomialPatch Unit s d)
    (f : ℕ → ℝ) (hf : ∀ n < N, f n ∈ Set.Icc (0 : ℝ) 1)
    {b : ℝ} (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    (𝔼 n : Fin N, (f n.val - b) * A.value (fun _ => (n.val : ℝ))) ≤ 1 := by
  by_cases hN : N = 0
  · subst N
    simp
  · let : NeZero N := ⟨hN⟩
    apply Finset.expect_le Finset.univ_nonempty
    intro n _
    have hB := A.value_mem_Icc (fun _ => (n.val : ℝ))
    have hle : f n.val - b ≤ 1 := by linarith [(hf n.val n.isLt).2, hb.1]
    exact (mul_le_mul_of_nonneg_right hle hB.1).trans (by simpa using hB.2)

theorem quantitative_polynomial_patch_reset (s : ℕ) :
    ∃ (C : ℝ) (P : ℕ), 1 ≤ C ∧ 0 < P ∧
      ∀ (d N T : ℕ) (A : PolynomialPatch Unit s d) (f : ℕ → ℝ),
        (∀ n < N, f n ∈ Set.Icc (0 : ℝ) 1) →
        ∀ b σ : ℝ, b ∈ Set.Icc (0 : ℝ) 1 → 0 < σ →
        C * ((d : ℝ) + 1) * ((A.kernel.lip : ℝ) + 1) ≤ σ * T →
        T ^ (P * (d + 1) ^ (2 * s * s)) ≤ N →
        σ ≤ (𝔼 n : Fin N, (f n.val - b) * A.value (fun _ => (n.val : ℝ))) →
        ∃ q a len : ℕ, 0 < q ∧ T ≤ len ∧
          (∀ n < len, a + q * n < N) ∧ b < 𝔼 n : Fin len, f (a + q * n.val) := by
  obtain ⟨K, p, hK, hp, hreset⟩ := polynomial_patch_density_increment s
  obtain ⟨C, hC, hbudget⟩ := exists_patch_reset_budget s hK
  refine ⟨C, (2 * p) ^ s, hC, pow_pos (by omega) _, ?_⟩
  intro d N T A f hf b σ hb hσ hscale hsize hscore
  have hσ1 := hscore.trans (polynomial_patch_score_le_one A f hf hb)
  obtain ⟨hT, hKscale, hlift, hfreeze, hroom, hlength⟩ :=
    hbudget d T A.kernel.lip σ A.kernel.lip.coe_nonneg hσ hσ1 hscale
  exact hreset d N T A hT hKscale hlift hfreeze hsize f hf b σ hb hσ hroom hlength hscore

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem quantitative_lifted_patch_reset (s : ℕ) :
    ∃ (C : ℝ) (P : ℕ), 1 ≤ C ∧ 0 < P ∧
      ∀ (D E N T : ℕ) (A : PolynomialPatch Unit s D)
        (B : WeightedParameterPatch (Unit ⊕ Fin D) (Sum.elim (fun _ => 1) A.weight) s E)
        (f : ℕ → ℝ), (∀ n < N, f n ∈ Set.Icc (0 : ℝ) 1) →
        ∀ a σ : ℝ, a ∈ Set.Icc (0 : ℝ) 1 → 0 < σ →
        C * (((D + E : ℕ) : ℝ) + 1) * ((A.kernel.lip : ℝ) + B.kernel.lip + 1) ≤ σ * T →
        T ^ (P * (D + E + 1) ^ (2 * s * s)) ≤ N →
        σ ≤ (𝔼 n : Fin N, (f n.val - a) * ∑' b : Fin D → ℤ,
          A.kernel.value ((A.form.slots (fun _ => (n.val : ℝ))).residual b) *
            B.value (Sum.elim (fun _ => (n.val : ℝ)) (fun j => (b j : ℝ)))) →
        ∃ q a₀ len : ℕ, 0 < q ∧ T ≤ len ∧
          (∀ n < len, a₀ + q * n < N) ∧ a < 𝔼 n : Fin len, f (a₀ + q * n.val) := by
  obtain ⟨C, P, hC, hP, hreset⟩ := quantitative_polynomial_patch_reset s
  refine ⟨C, P, hC, hP, ?_⟩
  intro D E N T A B f hf a σ ha hσ hscale hsize hscore
  apply hreset (D + E) N T (A.insertLifts B) f hf a σ ha hσ
  · simpa only [PolynomialPatch.insertLifts_lip, NNReal.coe_add] using hscale
  · exact hsize
  · simpa only [PolynomialPatch.insertLifts_value] using hscore

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem quantitative_polynomial_product_reset (s : ℕ) :
    ∃ (C : ℝ) (P : ℕ), 1 ≤ C ∧ 0 < P ∧
      ∀ (m : ℕ) (d : Fin m → ℕ) (N T : ℕ)
        (A : ∀ i, PolynomialPatch Unit s (d i)) (f : ℕ → ℝ),
        (∀ n < N, f n ∈ Set.Icc (0 : ℝ) 1) →
        ∀ b σ : ℝ, b ∈ Set.Icc (0 : ℝ) 1 → 0 < σ →
        C * (((∑ i, d i : ℕ) : ℝ) + 1) * ((∑ i, ((A i).kernel.lip : ℝ)) + 1) ≤ σ * T →
        T ^ (P * ((∑ i, d i) + 1) ^ (2 * s * s)) ≤ N →
        σ ≤ (𝔼 n : Fin N, (f n.val - b) * ∏ i, (A i).value (fun _ => (n.val : ℝ))) →
        ∃ q a len : ℕ, 0 < q ∧ T ≤ len ∧
          (∀ n < len, a + q * n < N) ∧ b < 𝔼 n : Fin len, f (a + q * n.val) := by
  obtain ⟨C, P, hC, hP, hreset⟩ := quantitative_polynomial_patch_reset s
  refine ⟨C, P, hC, hP, ?_⟩
  intro m d N T A f hf b σ hb hσ hscale hsize hscore
  obtain ⟨B, hB, hBlip⟩ := PolynomialPatch.exists_finset_product Finset.univ d A
  have hlip : (B.kernel.lip : ℝ) = ∑ i, ((A i).kernel.lip : ℝ) := by
    rw [hBlip, NNReal.coe_sum]
  apply hreset (∑ i, d i) N T B f hf b σ hb hσ
  · simpa only [hlip] using hscale
  · exact hsize
  · simpa only [hB] using hscore

end Erdos3

end

end OAI
