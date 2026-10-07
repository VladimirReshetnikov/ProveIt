import OAI.Combinatorics.Progressions.Estimates.NativeGlobalErrorSplitting

namespace OAI

section

namespace Erdos3.NativeVectorEquivalence

open scoped BigOperators

attribute [local instance] NativeVectorCorrelation.lie NativeVectorCorrelation.algebra
  NativeVectorCorrelation.topology NativeVectorCorrelation.topologicalAdd
  NativeVectorCorrelation.continuousSMul NativeVectorCorrelation.hausdorff

theorem exists_transfer_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {I J K : Type*} [Fintype J] [Fintype K]
      {s N : ℕ} [NeZero N] {p : ℝ} {chi : J → ZMod N → ℂ} {chi' : K → ZMod N → ℂ},
      NativeVectorEquivalence s N p chi chi' → (∀ x, ∑ k, ‖chi' k x‖ ^ 2 = 1) →
      ∀ f : I → ZMod N → ℂ,
      NativeVectorCorrelation s N p (fun ij : I × J => fun x => f ij.1 x * star (chi ij.2 x)) →
      Nonempty (NativeVectorCorrelation s N ((p + C) ^ C)
        (fun ik : I × K => fun x => f ik.1 x * star (chi' ik.2 x))) := by
  obtain ⟨a, _, ha⟩ := exists_productNiltestBudget_bound
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((3 * X + 4 + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro I J K _ _ s N _ p chi chi' E hunit f W
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hcost : (3 * p + 4 + a) ^ a ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hbound : productNiltestBudget (3 * p + 4) ≤ (p + C) ^ C :=
    (ha _ (by linarith)).trans hcost
  obtain ⟨V⟩ := E.transfer_correlation hunit f W
  exact ⟨V.mono hbound⟩

end Erdos3.NativeVectorEquivalence

end

end OAI
