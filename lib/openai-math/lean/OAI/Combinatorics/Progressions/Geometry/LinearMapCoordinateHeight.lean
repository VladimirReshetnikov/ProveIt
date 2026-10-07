import Mathlib.LinearAlgebra.Basis.Defs
import OAI.Combinatorics.Progressions.Estimates.RationalRowReduction

namespace OAI

section

namespace Erdos3

open Module

variable {V W ι κ : Type*} [AddCommGroup V] [Module ℚ V]
  [AddCommGroup W] [Module ℚ W] [Fintype ι]

theorem linearMap_coordinate_height (e : Basis ι ℚ V) (f : Basis κ ℚ W)
    (T : V →ₗ[ℚ] W) {H K : ℕ}
    (hT : ∀ i j, RationalHeightLE (f.repr (T (e i)) j) H)
    (x : V) (hx : ∀ i, RationalHeightLE (e.repr x i) K) (j : κ) :
    RationalHeightLE (f.repr (T x) j) ((Fintype.card ι + 1) * (K * H) ^ Fintype.card ι) := by
  classical
  have he : f.repr (T x) j = ∑ i, e.repr x i * f.repr (T (e i)) j := by
    conv_lhs => rw [← e.sum_repr x]
    simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [he]
  exact rationalHeightLE_sum _ (fun i => (hx i).mul (hT i j))

end Erdos3

end

end OAI
