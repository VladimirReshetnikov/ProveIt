import Mathlib.Data.Finset.Piecewise
import Mathlib.LinearAlgebra.Multilinear.Basic

namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem multilinear_affine_expansion {H R M : Type*} [Fintype H] [DecidableEq H] [CommRing R]
    [AddCommGroup M] [Module R M] (F : MultilinearMap R (fun _ : H => M) R)
    (b w : H → M) (x : H → R) :
    F (fun i => b i + x i • w i) =
      ∑ S : Finset H, F (S.piecewise w b) * ∏ i ∈ S, x i := by
  have he : (fun i => b i + x i • w i) = (fun i => x i • w i) + b := by
    funext i
    exact add_comm _ _
  rw [he, F.map_add_univ]
  apply Finset.sum_congr rfl
  intro S _
  have hs : S.piecewise (fun i => x i • w i) b =
      (fun i => (if i ∈ S then x i else 1) • S.piecewise w b i) := by
    funext i
    by_cases hi : i ∈ S <;> simp [Finset.piecewise, hi]
  rw [hs, F.map_smul_univ, Finset.prod_ite_mem_eq, smul_eq_mul, mul_comm]

end Erdos3

end

end OAI
