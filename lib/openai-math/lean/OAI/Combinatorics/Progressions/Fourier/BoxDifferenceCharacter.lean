import OAI.Combinatorics.Progressions.Geometry.BoxDifferenceHom

namespace OAI

section

namespace Erdos3

open CircleFourier

theorem character_real_sub (a b : ℝ) :
    character ((a-b : ℝ) : CircleFourier.Circle) =
      character (a : CircleFourier.Circle) * star (character (b : CircleFourier.Circle)) := by
  rw [sub_eq_add_neg, AddCircle.coe_add, AddCircle.coe_neg, character_add, character_neg]

theorem iteratedBoxDifference_character (n : ℕ) {X : Fin n → Type*} {Z : Type*}
    (F : (∀ i, X i) → Z → ℝ) (u v : ∀ i, X i) (z : Z) :
    iteratedBoxDifference n (fun x t => character (F x t : CircleFourier.Circle)) u v z =
      character ((additiveBoxDifference n F u v z : ℝ) : CircleFourier.Circle) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [iteratedBoxDifference, additiveBoxDifference, ← character_real_sub]
    exact ih _ (Fin.tail u) (Fin.tail v)

end Erdos3

end

end OAI
