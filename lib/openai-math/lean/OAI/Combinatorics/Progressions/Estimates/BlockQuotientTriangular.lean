import Mathlib.LinearAlgebra.Matrix.ToLin

namespace OAI

section

namespace Erdos3

open scoped Matrix

variable {K ι κ : Type*} [Field K] [Fintype ι] [DecidableEq ι] [DecidableEq κ]

theorem block_quotient_unitriangular (ω : ι → ℕ) (ν : κ → ℕ)
    (D : Matrix κ ι K) (M : Matrix ι ι K) (S : Matrix ι κ K)
    (hD : ∀ k i, ν k ≠ ω i → D k i = 0)
    (hS : ∀ i k, ω i ≠ ν k → S i k = 0)
    (hDS : D * S = 1)
    (hM : ∀ i j, ω i ≤ ω j → M i j = (1 : Matrix ι ι K) i j)
    (a b : κ) (hab : ν a ≤ ν b) :
    (D * M * S) a b = (1 : Matrix κ κ K) a b := by
  have he : (D * M * S) a b = (D * (1 : Matrix ι ι K) * S) a b := by
    simp only [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : ω j = ν b
    · apply congrArg (fun x => x * S j b)
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : ν a = ω i
      · rw [hM i j (by omega)]
      · rw [hD a i hi, zero_mul, zero_mul]
    · rw [hS j b hj, mul_zero, mul_zero]
  rw [he, Matrix.mul_one, hDS]

end Erdos3

end

end OAI
