import GowersSzemeredi.Proofs15Walsh

/-!
# Proven companion for Gowers (2001), Corollary 15.2
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-- **Corollary 15.2.** The ternary case of
`booleanWalsh_multiple_of_invariant`. -/
theorem corollary_15_2_holds : corollary_15_2 :=
  fun _ _ _ hprime hodd h eta hh _ hinvariant =>
    booleanWalsh_multiple_of_invariant hprime hodd h eta hh hinvariant

alias corollary_15_2_of_general := corollary_15_2_holds

lemma rangeDeg_sum_mul_sub_eq_one {N : Nat} {I : Type*}
    [Fintype I] [DecidableEq I] (a x y : I → ZMod N) (i : I)
    (hoff : ∀ t, t ≠ i → x t = y t) :
    (∑ t, a t * x t) - (∑ t, a t * y t) =
      a i * (x i - y i) := by
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ t, (a t * x t - a t * y t)) =
        ∑ t, a t * (x t - y t) := by
      apply Finset.sum_congr rfl
      intro t _
      ring
    _ = ∑ t ∈ ({i} : Finset I), a t * (x t - y t) := by
      symm
      apply Finset.sum_subset (by simp)
      intro t _ ht
      have hti : t ≠ i := by simpa using ht
      rw [hoff t hti, sub_self, mul_zero]
    _ = a i * (x i - y i) := by simp

end LeanProofs.GowersSzemeredi
