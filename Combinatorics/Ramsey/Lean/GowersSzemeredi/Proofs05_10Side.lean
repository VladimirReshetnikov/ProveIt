import GowersSzemeredi.Proofs05_10
import GowersSzemeredi.Sections08_09

/-! Declarations of `Proofs05_10` that the final route does not use and that
need modules outside it (moved here so that those modules can leave the route). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod Combinatorics.Additive
open Finset

namespace LeanProofs.GowersSzemeredi

/-- Lemma 9.1 is the weighted Hölder inequality with weight and function
both equal to `a i ^ 2`, and exponent seven. -/
theorem lemma_9_1_holds : lemma_9_1 := by
  intro n a _
  have h := Real.inner_le_weight_mul_Lp_of_nonneg
    (s := (Finset.univ : Finset (Fin n))) (p := (7 : ℝ)) (by norm_num)
    (fun i => a i ^ 2) (fun i => a i ^ 2)
    (fun i => sq_nonneg (a i)) (fun i => sq_nonneg (a i))
  have h4 : (∑ i, a i ^ 2 * a i ^ 2) = ∑ i, a i ^ 4 := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h4] at h
  norm_num [Real.rpow_natCast] at h
  ring_nf at h
  exact h

end LeanProofs.GowersSzemeredi
