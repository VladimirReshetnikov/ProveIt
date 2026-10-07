import Mathlib

namespace OAI

section

namespace Erdos3.FreimanModel

def roundedGraphModuli {I : Type*} (N M : ℕ) : Option I → ℕ
  | none => N
  | some _ => M

def roundedGraphCoordinateEquiv {I : Type*} (N M : ℕ) :
    (ZMod N × (I → ZMod M)) ≃+ (∀ i : Option I, ZMod (roundedGraphModuli N M i)) where
  toFun x i := match i with
    | none => x.1
    | some j => x.2 j
  invFun x := (x none, fun i => x (some i))
  left_inv x := rfl
  right_inv x := by funext i; cases i <;> rfl
  map_add' x y := by funext i; cases i <;> rfl

theorem roundedGraphModuli_neZero {I : Type*} (N M : ℕ) [NeZero N] [NeZero M] :
    ∀ i : Option I, NeZero (roundedGraphModuli N M i) := by
  intro i
  cases i <;> dsimp [roundedGraphModuli] <;> infer_instance

end Erdos3.FreimanModel

end

end OAI
