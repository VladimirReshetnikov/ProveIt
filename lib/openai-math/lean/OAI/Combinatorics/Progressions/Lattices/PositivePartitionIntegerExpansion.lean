import OAI.Combinatorics.Progressions.Estimates.PositiveWeightedExpansion

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_positive_weighted_integer_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type} [Fintype σ] {s N : ℕ} [NeZero N]
      {p : ℝ} {f : (σ → ℤ) → ℂ}
      (_E : NativeIntegerExpansion (fun _ : σ => 1) s p f),
      0 ≤ p → (Fintype.card σ : ℝ) ≤ p → ∀ w : σ → ZMod N → ℝ,
      (∀ i, PositiveCyclicNiltest.{0} s N p (w i)) →
      ∃ g : (σ → ℤ) → ℂ,
        Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s ((p + C) ^ C) g) ∧
        ∀ x : σ → ZMod N, g (fun i => ((x i).val : ℤ)) =
          (∏ i, (w i (x i) : ℂ)) * f (fun i => ((x i).val : ℤ)) := by
  obtain ⟨A, _, hprod⟩ := exists_productNiltestBudget_bound
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let Y := X + (X + 2) ^ 2 + 3
  let Q := (Y + Polynomial.C A) ^ A + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((Q + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro σ _ s N _ p f E hp hσ w hw
  have hp' : 0 ≤ raisedNiltestBudget p := hp.trans (le_raisedNiltestBudget p)
  let q := (raisedNiltestBudget p + A) ^ A + p + 2
  have hpower : 0 ≤ (raisedNiltestBudget p + A) ^ A := by positivity
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hpq : p ≤ q := by dsimp only [q]; linarith only [hpower]
  have hweight : productNiltestBudget (raisedNiltestBudget p) ≤ q :=
    (hprod _ hp').trans (by dsimp only [q]; linarith only [hp])
  have hqC : (q + B) ^ B ≤ (p + C) ^ C := by
    simpa [Q, Y, X, q, raisedNiltestBudget, Polynomial.eval₂_pow] using hbudget p hp
  obtain ⟨g, ⟨W⟩, he⟩ := exists_positive_coordinate_product hp hσ hw
  obtain ⟨G⟩ := hmul hq (W.mono hweight) (E.mono hpq)
  refine ⟨fun x => g x * f x, ⟨G.mono hqC⟩, ?_⟩
  intro x
  exact congrArg (fun z : ℂ => z * f (fun i => ((x i).val : ℤ))) (he x)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_positive_partition_integer_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type} {I J : Type*} [Fintype σ] [Fintype I]
      {s N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card I : ℝ) ≤ Real.exp p →
      ∀ (w : I → σ → ZMod N → ℝ) (v : I → J → (σ → ℤ) → ℂ),
        (∀ i k, PositiveCyclicNiltest.{0} s N p (w i k)) →
        (∀ i j, Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s p (v i j))) →
        ∃ F : J → (σ → ℤ) → ℂ,
          (∀ j, Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s ((p + C) ^ C) (F j))) ∧
          ∀ j (x : σ → ZMod N), F j (fun k => ((x k).val : ℤ)) =
            ∑ i, ((∏ k, w i k (x k) : ℝ) : ℂ) * v i j (fun k => ((x k).val : ℤ)) := by
  obtain ⟨A, _, hweighted⟩ := exists_positive_weighted_integer_expansion
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((X + Polynomial.C A) ^ A + X)
  refine ⟨C, hC, ?_⟩
  intro σ I J _ _ s N _ p hp hσ hI w v hw hv
  classical
  have hfamily (i : I) (j : J) : ∃ g : (σ → ℤ) → ℂ,
      Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s ((p + A) ^ A) g) ∧
      ∀ x : σ → ZMod N, g (fun k => ((x k).val : ℤ)) =
        ((∏ k, w i k (x k) : ℝ) : ℂ) * v i j (fun k => ((x k).val : ℤ)) := by
    obtain ⟨g, hg, he⟩ := hweighted (Classical.choice (hv i j)) hp hσ (w i) (hw i)
    exact ⟨g, hg, fun x => by simpa only [Complex.ofReal_prod] using he x⟩
  choose g hg he using hfamily
  let F := fun (j : J) (x : σ → ℤ) => ∑ i, g i j x
  have hcost : (p + A) ^ A + p ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨F, ?_, ?_⟩
  · intro j
    have hc : (∑ _i : I, ‖(1 : ℂ)‖) ≤ Real.exp p := by simpa using hI
    exact ⟨by simpa only [F, one_mul] using
      ((NativeIntegerExpansion.weightedSum (fun i => Classical.choice (hg i j))
        (fun _ => 1) hp hI hc).mono hcost)⟩
  · intro j x
    exact Finset.sum_congr rfl (fun i _ => he i j x)

end Erdos3

end

end OAI
