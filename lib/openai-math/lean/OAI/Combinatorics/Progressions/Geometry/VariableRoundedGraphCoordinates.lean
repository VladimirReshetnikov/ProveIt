import Mathlib

namespace OAI

section

namespace Erdos3.FreimanModel

def variableRoundedGraphModuli {I : Type*} (N : ℕ) (M : I → ℕ) : Option I → ℕ
  | none => N
  | some i => M i

def variableRoundedGraphCoordinateEquiv {I : Type*} (N : ℕ) (M : I → ℕ) :
    (ZMod N × (∀ i, ZMod (M i))) ≃+ (∀ i : Option I, ZMod (variableRoundedGraphModuli N M i)) where
  toFun x i := match i with
    | none => x.1
    | some j => x.2 j
  invFun x := (x none, fun i => x (some i))
  left_inv x := rfl
  right_inv x := by funext i; cases i <;> rfl
  map_add' x y := by funext i; cases i <;> rfl

theorem variableRoundedGraphModuli_neZero {I : Type*} (N : ℕ) (M : I → ℕ) [NeZero N] [∀ i, NeZero (M i)] :
    ∀ i : Option I, NeZero (variableRoundedGraphModuli N M i) := by
  intro i
  cases i <;> dsimp [variableRoundedGraphModuli] <;> infer_instance

end Erdos3.FreimanModel

end

end OAI
