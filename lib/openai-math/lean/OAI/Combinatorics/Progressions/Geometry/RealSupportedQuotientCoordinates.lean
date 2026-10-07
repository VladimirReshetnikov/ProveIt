/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Estimates.RealifiedMultidegree
import OAI.Combinatorics.Progressions.Linear.BasisGradedCoordinateBasis

namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {V ι : Type*} [AddCommGroup V] [Module ℚ V]
  (b : Basis ι ℚ V) (P : Submodule ℚ V) (S : Set ι)
  (hP : P = Submodule.span ℚ (b '' S))

theorem realSupportedQuotientBasis_repr_mk (x : ℝ ⊗[ℚ] V) (i : {i // i ∉ S}) :
    ((supportedQuotientBasis b P S hP).baseChange ℝ).repr (P.mkQ.baseChange ℝ x) i =
      (b.baseChange ℝ).repr x i := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  | tmul r x =>
    rw [LinearMap.baseChange_tmul, Basis.baseChange_repr_tmul,
      Basis.baseChange_repr_tmul, supportedQuotientBasis_repr_mk]

end Erdos3

end

end OAI
