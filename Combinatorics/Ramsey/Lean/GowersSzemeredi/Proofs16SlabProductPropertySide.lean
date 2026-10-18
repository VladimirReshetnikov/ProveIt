import GowersSzemeredi.Proofs16SlabProductProperty

/-! Declarations of `Proofs16SlabProductProperty` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators Pointwise

namespace LeanProofs.GowersSzemeredi

/-- Arbitrary functions into S on a final-coordinate domain A have the
original weighted product property at gamma=1 when |A+A||S+S|<=N.
All parallel-family sizes, including zero, and all nonnegative weights
are included. This is a partial-domain theorem, with no primality premise. -/
theorem section16_slab_unit_product {N k : Nat} [NeZero N]
    (A S : Finset (ZMod N)) (f : ZMod N → ZMod N)
    (hf : ∀ x ∈ A, f x ∈ S) (hsize : (A + A).card * (S + S).card ≤ N) :
    HasProductProperty (lastProductSet (Finset.univ : Finset (Point N k)) A)
      (fun z => f (section16Last z)) 1 := by
  intro p j y E w _hw hE
  simp only [one_pow, one_mul]
  by_cases hj : j = Fin.last k
  · subst j
    by_cases hp : p = 0
    · subst p
      have heq : (fun i : Fin 0 => coordinateRestriction
          (fun z => f (section16Last z)) (y i) (Fin.last k)) = (fun _ : Fin 0 => fun _ => 0) := by
        funext i
        exact Fin.elim0 i
      rw [heq]
      exact section16_zero_parallel_energy E w
    · have hEA : E ⊆ A := by
        intro x hx
        have h := hE ⟨0, Nat.pos_of_ne_zero hp⟩ x hx
        simpa [lastProductSet, section16Last, replaceCoordinate] using h
      have heq : (fun i => coordinateRestriction (fun z => f (section16Last z)) (y i) (Fin.last k)) =
          (fun _ : Fin p => f) := by
        funext i x
        simp [coordinateRestriction, section16Last, replaceCoordinate]
      rw [heq]
      exact section16_weighted_graph_sum_bound A S E f w hEA hf hsize
  · have heq : (fun i => coordinateRestriction (fun z => f (section16Last z)) (y i) j) =
        (fun i : Fin p => fun _ => f (section16Last (y i))) := by
      funext i x
      simp [coordinateRestriction, section16Last, replaceCoordinate, Function.update_of_ne (Ne.symm hj)]
    rw [heq, weightedSimultaneousAdditiveEnergy_constants]
    exact section16_zero_parallel_energy E w

end LeanProofs.GowersSzemeredi
