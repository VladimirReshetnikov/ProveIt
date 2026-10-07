import OAI.Combinatorics.Progressions.Estimates.CocycleHorizontalNormalization

namespace OAI

section

namespace Erdos3

open scoped Matrix

variable {ι κ μ R : Type*} [CommRing R]

def constraintProjectionMatrix (Q : Matrix ι κ R) (P : Matrix μ κ R) :
    Matrix (ι ⊕ μ) κ R := fun i j => Sum.elim (fun k => Q k j) (fun k => P k j) i

def constraintProjectionInput (y : μ → R) : (ι ⊕ μ) → R := Sum.elim (fun _ => 0) y

theorem constraintProjectionMatrix_mulVec [Fintype κ]
    (Q : Matrix ι κ R) (P : Matrix μ κ R) (x : κ → R) :
    constraintProjectionMatrix Q P *ᵥ x = Sum.elim (Q *ᵥ x) (P *ᵥ x) := by
  funext i
  cases i <;> rfl

theorem mulVec_constraintProjectionInput [Fintype ι] [Fintype μ]
    (S : Matrix κ (ι ⊕ μ) R) (y : μ → R) :
    S *ᵥ constraintProjectionInput (ι := ι) y = (fun i j => S i (Sum.inr j)) *ᵥ y := by
  funext i
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, constraintProjectionInput]

theorem constraintProjectionInput_grid [Fintype ι] [Fintype μ]
    (l : ℕ) (y : μ → ℝ) (hy : y ∈ realDenominatorGrid l) :
    constraintProjectionInput (ι := ι) y ∈ realDenominatorGrid l := by
  obtain ⟨z, hz⟩ := hy
  refine ⟨Sum.elim (fun _ => (0 : ℤ)) z, ?_⟩
  funext i
  cases i with
  | inl i => simp [constraintProjectionInput]
  | inr i => exact congrFun hz i

theorem constraintProjectionInput_weighted {δ : Type*}
    (r : ι → δ) (c : μ → δ) (W : δ → ℝ) (hW : ∀ d, 0 < W d)
    {M : ℝ} (hM : 0 ≤ M) (y : μ → ℝ) (hy : ∀ i, |y i| ≤ M / W (c i)) :
    ∀ i, |constraintProjectionInput (ι := ι) y i| ≤ M / W (Sum.elim r c i) := by
  intro i
  cases i with
  | inl i =>
    change |(0 : ℝ)| ≤ M / W (r i)
    rw [abs_zero]
    exact div_nonneg hM (hW _).le
  | inr i => exact hy i

end Erdos3

end

end OAI
