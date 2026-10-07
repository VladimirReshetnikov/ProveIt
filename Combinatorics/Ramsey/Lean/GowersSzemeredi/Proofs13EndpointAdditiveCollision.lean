import GowersSzemeredi.Proofs13EndpointFiniteError

/-! The increment collision estimate underlying finite additive correction.
Two uniformly distributed addition tests control every fixed increment. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

def endpointAdditiveFailure {A H : Type*} [Fintype A] [Add A] [Add H] [DecidableEq H]
    (u : A → H) : Real :=
  endpointError (fun p : A × A => u (p.1 + p.2)) (fun p => u p.1 + u p.2)

def endpointIncrement {A H : Type*} [Add A] [Sub H] (u : A → H) (x y : A) : H := u (x + y) - u y

private def endpointAdditionTestEquiv {A : Type*} [AddCommGroup A] (x : A) : A × A ≃ A × A where
  toFun p := (x + p.1, p.2 - p.1)
  invFun p := (p.1 - x, p.2 + (p.1 - x))
  left_inv p := by apply Prod.ext <;> dsimp <;> abel
  right_inv p := by apply Prod.ext <;> dsimp <;> abel

theorem endpointIncrement_collision_le {A H : Type*} [Fintype A] [AddCommGroup A]
    [AddCommGroup H] [DecidableEq H] (u : A → H) (x : A) :
    endpointError (fun p : A × A => endpointIncrement u x p.1)
      (fun p => endpointIncrement u x p.2) ≤ 2 * endpointAdditiveFailure u := by
  let f : A × A → H := fun p => u (p.1 + p.2)
  let g : A × A → H := fun p => u p.1 + u p.2
  have hp (y z : A) :
      (if endpointIncrement u x y = endpointIncrement u x z then (0 : Real) else 1) ≤
        (if f (endpointAdditionTestEquiv x (y, z)) = g (endpointAdditionTestEquiv x (y, z)) then 0 else 1) +
        (if f (endpointAdditionTestEquiv 0 (y, z)) = g (endpointAdditionTestEquiv 0 (y, z)) then 0 else 1) := by
    by_cases h₁ : f (endpointAdditionTestEquiv x (y, z)) = g (endpointAdditionTestEquiv x (y, z))
    · by_cases h₂ : f (endpointAdditionTestEquiv 0 (y, z)) = g (endpointAdditionTestEquiv 0 (y, z))
      · have h₁' : u (x + z) = u (x + y) + u (z - y) := by
          simpa [f, g, endpointAdditionTestEquiv, add_sub_assoc, add_comm, add_left_comm, add_assoc] using h₁
        have h₂' : u z = u y + u (z - y) := by
          simpa [f, g, endpointAdditionTestEquiv, add_sub_assoc, add_comm, add_left_comm, add_assoc] using h₂
        have he : endpointIncrement u x y = endpointIncrement u x z := by
          unfold endpointIncrement
          rw [h₁', h₂']
          abel
        simp [h₁, h₂, he]
      · simp only [if_pos h₁, if_neg h₂, zero_add]
        split_ifs <;> norm_num
    · simp only [if_neg h₁]
      split_ifs <;> norm_num
  calc
    _ ≤ endpointError (f ∘ endpointAdditionTestEquiv x) (g ∘ endpointAdditionTestEquiv x) +
        endpointError (f ∘ endpointAdditionTestEquiv 0) (g ∘ endpointAdditionTestEquiv 0) := by
      unfold endpointError
      rw [← Finset.expect_add_distrib]
      apply Finset.expect_le_expect
      intro p _
      exact hp p.1 p.2
    _ = _ := by rw [endpointError_equiv, endpointError_equiv]; change _ = 2 * endpointError f g; ring

def endpointCorrectedMap {A H : Type*} [Fintype A] [AddCommGroup A]
    [Fintype H] [AddCommGroup H] [DecidableEq H] (u : A → H) (x : A) : H :=
  endpointModalValue (endpointIncrement u x)

theorem endpointCorrectedMap_local_error {A H : Type*} [Fintype A] [AddCommGroup A]
    [Fintype H] [AddCommGroup H] [DecidableEq H] (u : A → H) (x : A) :
    endpointError (endpointIncrement u x) (fun _ => endpointCorrectedMap u x) ≤
      2 * endpointAdditiveFailure u :=
  (endpointModalValue_error_le_collision (endpointIncrement u x)).trans (endpointIncrement_collision_le u x)

end LeanProofs.GowersSzemeredi
