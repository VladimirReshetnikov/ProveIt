import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.Pi

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem multilinear_coordinate_expansion {H I R : Type*} [Fintype H] [Fintype I]
    [DecidableEq H] [DecidableEq I] [CommRing R]
    (F : MultilinearMap R (fun _ : H => I → R) R) (u : H → I → R) :
    F u = ∑ j : H → I, F (fun i => Pi.single (j i) (1 : R)) * ∏ i, u i (j i) := by
  have hu : u = fun h => ∑ i, u h i • Pi.single i (1 : R) := by
    funext h i
    simp [Pi.single_apply]
  calc
    F u = F (fun h => ∑ i, u h i • Pi.single i (1 : R)) := congrArg F hu
    _ = ∑ j : H → I, F (fun h => u h (j h) • Pi.single (j h) (1 : R)) :=
      F.map_sum (fun h i => u h i • Pi.single i (1 : R))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [F.map_smul_univ, smul_eq_mul, mul_comm]

theorem multilinear_diagonal_expansion {H I R : Type*} [Fintype H] [Fintype I]
    [DecidableEq H] [DecidableEq I] [CommRing R]
    (F : MultilinearMap R (fun _ : H => I → R) R) (w : I → R) :
    F (fun _ => w) = ∑ j : H → I, F (fun i => Pi.single (j i) (1 : R)) * ∏ i, w (j i) :=
  multilinear_coordinate_expansion F (fun _ => w)

end Erdos3

end

end OAI
