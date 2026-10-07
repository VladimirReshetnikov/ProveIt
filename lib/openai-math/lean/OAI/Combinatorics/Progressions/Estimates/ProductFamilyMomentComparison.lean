/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Linear.ProductANOVAEnergyOrder

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
  {X : I → Type*} [∀ i, Fintype (X i)] (μ : ∀ i, FiniteProbabilityWeights (X i))

theorem productFamily_moment_comparison (rho : (∀ i, X i) → ℝ)
    (S : J → Finset I) (u : J → (∀ i, X i) → ℝ) (b q : ℕ) {eta C : ℝ}
    (heta : 0 ≤ eta) (_hC : 0 ≤ C) (hcard : ∀ j, (S j).card ≤ b)
    (hdep : ∀ j, ProductDependsOn (S j) (u j))
    (hcap : ∀ j x, (FiniteProbabilityWeights.pi μ).weight x ≠ 0 → |u j x| ≤ C)
    (hclose : ∀ T : Finset I, T.card ≤ q * b → ∀ x,
      (FiniteProbabilityWeights.pi μ).weight x ≠ 0 →
        |productConditionalMean μ T rho x - 1| ≤ eta) :
    |(FiniteProbabilityWeights.pi μ).mean (fun x => rho x * (∑ j, u j x) ^ q) -
      (FiniteProbabilityWeights.pi μ).mean (fun x => (∑ j, u j x) ^ q)| ≤
        eta * (Fintype.card J : ℝ) ^ q * C ^ q := by
  classical
  have hterm (a : Fin q → J) :
      |(FiniteProbabilityWeights.pi μ).mean (fun x => rho x * ∏ j, u (a j) x) -
        (FiniteProbabilityWeights.pi μ).mean (fun x => ∏ j, u (a j) x)| ≤ eta * C ^ q := by
    let T := Finset.univ.biUnion (fun j : Fin q => S (a j))
    have hT : T.card ≤ q * b := by
      calc
        T.card ≤ ∑ j : Fin q, (S (a j)).card := Finset.card_biUnion_le
        _ ≤ ∑ _j : Fin q, b := Finset.sum_le_sum (fun j _ => hcard (a j))
        _ = q * b := by simp
    apply productMarginal_test_error μ rho (fun x => ∏ j, u (a j) x) T heta ?_ (hclose T hT) ?_
    · apply ProductDependsOn.prod
      intro j _
      apply (hdep (a j)).mono
      intro i hi
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hi⟩
    · intro x hx
      rw [Finset.abs_prod]
      have h := Finset.prod_le_prod₀ (s := Finset.univ) (fun j _ => abs_nonneg (u (a j) x)) (fun j _ => hcap (a j) x hx)
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using h
  simp_rw [Fintype.sum_pow, Finset.mul_sum, FiniteProbabilityWeights.mean_sum]
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ a : Fin q → J,
        |(FiniteProbabilityWeights.pi μ).mean (fun x => rho x * ∏ j, u (a j) x) -
          (FiniteProbabilityWeights.pi μ).mean (fun x => ∏ j, u (a j) x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _a : Fin q → J, eta * C ^ q := Finset.sum_le_sum (fun a _ => hterm a)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
      ring

end Erdos3

end

end OAI
