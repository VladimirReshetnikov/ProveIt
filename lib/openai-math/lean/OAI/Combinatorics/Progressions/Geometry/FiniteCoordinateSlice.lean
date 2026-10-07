import Mathlib.Logic.Equiv.Prod
import OAI.Combinatorics.Progressions.Estimates.ComplexFiniteMeans

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem expect_le_of_coordinate_slices {I X : Type*} [Fintype I] [DecidableEq I]
    [Fintype X] [Nonempty X] (i : I) (f : (I → X) → ℝ) (C : ℝ)
    (hslice : ∀ x : I → X, (𝔼 a : X, f (Function.update x i a)) ≤ C) :
    (𝔼 x : I → X, f x) ≤ C := by
  classical
  let e := Equiv.funSplitAt i X
  have he := Fintype.expect_equiv e f (fun p => f (e.symm p)) (fun x => by simp)
  rw [he, ← Finset.univ_product_univ, Finset.expect_product, Finset.expect_comm]
  apply Finset.expect_le Finset.univ_nonempty
  intro r _
  let x : I → X := e.symm (Classical.choice inferInstance, r)
  have hupdate (a : X) : e.symm (a, r) = Function.update x i a := by
    funext j
    by_cases hj : j = i
    · subst j
      simp [e, Equiv.funSplitAt, Equiv.piSplitAt]
    · simp [e, x, Equiv.funSplitAt, Equiv.piSplitAt, hj]
  simpa only [hupdate] using hslice x

end Erdos3

end

end OAI
