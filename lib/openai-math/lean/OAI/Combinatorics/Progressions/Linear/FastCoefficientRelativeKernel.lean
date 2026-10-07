import OAI.Combinatorics.Progressions.Estimates.ReducedNativeFactorization

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

theorem firstCoefficientFastSubmodule_relative :
    F.firstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U) =
      F.firstCoefficientFastSubmodule w hw U.toSubmodule := by
  rw [F.firstCoefficientFastSubmodule_eq_image, F.firstCoefficientFastSubmodule_eq_image]
  simp only [reducedSquareFastRelativeSubmodule, inf_assoc, inf_idem]

theorem realFirstCoefficientFastSubmodule_relative :
    F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U) =
      F.realFirstCoefficientFastSubmodule w hw U.toSubmodule := by
  unfold realFirstCoefficientFastSubmodule
  rw [F.firstCoefficientFastSubmodule_relative]

end Erdos3.NilpotentLieFiltration

end

end OAI
