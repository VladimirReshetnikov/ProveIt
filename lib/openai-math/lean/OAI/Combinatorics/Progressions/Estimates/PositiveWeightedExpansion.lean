import OAI.Combinatorics.Progressions.Geometry.PositiveCyclicCoordinateProduct
import OAI.Combinatorics.Progressions.Lattices.NativeIntegerHalving

namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem exists_positive_weighted_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type} [Fintype σ] {s N : ℕ} [NeZero N]
      {p : ℝ} {L : Type} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} {D : RationalFilteredNilmanifold L s d}
      (T : D.Niltest (fun _ : σ => 1)), 0 ≤ p → (Fintype.card σ : ℝ) ≤ p →
      T.ComplexityLE p → ∀ f : σ → ZMod N → ℝ,
      (∀ i, PositiveCyclicNiltest.{0} s N p (f i)) →
      ∃ g : (σ → ℤ) → ℂ,
        Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s ((p + C) ^ C) g) ∧
        ∀ x : σ → ZMod N, g (fun i => ((x i).val : ℤ)) =
          (∏ i, (f i (x i) : ℂ)) * T.evalCyclic N x := by
  obtain ⟨A, _, hprod⟩ := exists_productNiltestBudget_bound
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let Y := X + (X + 2) ^ 2 + 3
  let Q := (Y + Polynomial.C A) ^ A + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((Q + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro σ _ s N _ p L _ _ _ _ _ _ d D T hp hσ hT f hf
  have hp' : 0 ≤ raisedNiltestBudget p := hp.trans (le_raisedNiltestBudget p)
  let q := (raisedNiltestBudget p + A) ^ A + p + 2
  have hpower : 0 ≤ (raisedNiltestBudget p + A) ^ A := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hweight : productNiltestBudget (raisedNiltestBudget p) ≤ q := by
    exact (hprod _ hp').trans (by dsimp [q]; linarith)
  have hqC : (q + B) ^ B ≤ (p + C) ^ C := by
    simpa [Q, Y, X, q, raisedNiltestBudget, Polynomial.eval₂_pow] using hbudget p hp
  obtain ⟨g, ⟨E⟩, he⟩ := exists_positive_coordinate_product hp hσ hf
  let F := NativeIntegerExpansion.ofTest T hT (fun _ => rfl)
  obtain ⟨G⟩ := hmul hq (E.mono hweight) (F.mono hpq)
  refine ⟨fun x => g x * T.eval x, ⟨G.mono hqC⟩, ?_⟩
  intro x
  change g (fun i => ((x i).val : ℤ)) * T.evalCyclic N x = _
  rw [he]

end Erdos3

end

end OAI
