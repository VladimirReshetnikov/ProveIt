import OAI.Combinatorics.Progressions.Geometry.BoxDifferenceHom

namespace OAI

section

namespace Erdos3

theorem additiveBoxDifference_map {X Y Z R : Type*} [AddGroup R] (n : ℕ) :
    ∀ (f : Fin n → X → Y) (F : (Fin n → Y) → Z → R)
      (u v : Fin n → X) (z : Z),
      additiveBoxDifference n (fun x t => F (fun i => f i (x i)) t) u v z =
        additiveBoxDifference n F (fun i => f i (u i)) (fun i => f i (v i)) z := by
  induction n with
  | zero =>
    intro f F u v z
    simp only [additiveBoxDifference]
    congr 1
    funext i
    exact Fin.elim0 i
  | succ n ih =>
    intro f F u v z
    have hcons (a : X) (x : Fin n → X) :
        (fun i => f i ((Fin.cons a x : Fin (n + 1) → X) i)) =
          (Fin.cons (f 0 a) (fun i : Fin n => f i.succ (x i)) : Fin (n + 1) → Y) := by
      funext i
      cases i using Fin.cases <;> rfl
    simp only [additiveBoxDifference]
    simp_rw [hcons]
    exact ih (fun i => f i.succ)
      (fun y t => F (Fin.cons (f 0 (u 0)) y) t - F (Fin.cons (f 0 (v 0)) y) t)
      (Fin.tail u) (Fin.tail v) z

end Erdos3

end

end OAI
