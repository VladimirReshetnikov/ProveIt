import OAI.Combinatorics.Progressions.Estimates.ComplexFiniteMeans

namespace OAI

section

namespace Erdos3

open scoped BigOperators

def emptyCubeCoordinateEquiv (X : Type*) : (Option Empty → X) ≃ X where
  toFun x := x none
  invFun x := fun _ => x
  left_inv x := by
    funext i
    cases i with
    | none => rfl
    | some a => exact a.elim
  right_inv _ := rfl

theorem expect_emptyCubeCoordinate {X M : Type*} [Fintype X]
    [AddCommMonoid M] [Module ℚ≥0 M] (F : X → M) :
    (𝔼 x : Option Empty → X, F (x none)) = 𝔼 x : X, F x :=
  Fintype.expect_equiv (emptyCubeCoordinateEquiv X) _ _ (fun _ => rfl)

end Erdos3

end

end OAI
