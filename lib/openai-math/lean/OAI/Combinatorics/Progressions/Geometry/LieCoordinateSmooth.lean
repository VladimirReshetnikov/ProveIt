import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.LinearAlgebra.Basis.Defs
import OAI.Combinatorics.Progressions.Nilpotent.LieBCHContinuity

namespace OAI

section

namespace Erdos3

open Module
open scoped ContDiff

variable {ι X E L : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [LieRing L] [LieAlgebra ℝ L] {n : ℕ∞ω}

theorem lie_coordinate_formula_real (e : Basis ι ℝ L) (a b : L) (k : ι) :
    e.repr ⁅a, b⁆ k =
      ∑ i, ∑ j, e.repr a i * e.repr b j * e.repr ⁅e i, e j⁆ k := by
  classical
  conv_lhs => rw [← e.sum_repr a, ← e.sum_repr b]
  simp only [sum_lie, lie_sum, smul_lie, lie_smul, map_sum, map_smul,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem contDiff_lie_coordinates (e : Basis ι ℝ L) (f g : E → L)
    (hf : ∀ i, ContDiff ℝ n (fun x => e.repr (f x) i))
    (hg : ∀ i, ContDiff ℝ n (fun x => e.repr (g x) i)) (k : ι) :
    ContDiff ℝ n (fun x => e.repr ⁅f x, g x⁆ k) := by
  have heq : (fun x => e.repr ⁅f x, g x⁆ k) =
      (fun x => ∑ i, ∑ j, e.repr (f x) i * e.repr (g x) j * e.repr ⁅e i, e j⁆ k) :=
    funext (fun x => lie_coordinate_formula_real e (f x) (g x) k)
  rw [heq]
  exact ContDiff.sum (fun i _ => ContDiff.sum (fun j _ =>
    ((hf i).mul (hg j)).mul contDiff_const))

variable [LieAlgebra ℚ L]

theorem contDiff_rightBracketList_coordinates (e : Basis ι ℝ L) (f : X → E → L)
    (hf : ∀ x i, ContDiff ℝ n (fun y => e.repr (f x y) i)) (xs : List X)
    (a : E → L) (ha : ∀ i, ContDiff ℝ n (fun y => e.repr (a y) i)) (k : ι) :
    ContDiff ℝ n (fun y => e.repr (rightBracketList (fun x => f x y) xs (a y)) k) := by
  induction xs generalizing a with
  | nil => exact ha k
  | cons x xs ih =>
    exact ih (fun y => ⁅a y, f x y⁆) (contDiff_lie_coordinates e a (f x) ha (hf x))

theorem contDiff_dynkinWord_coordinates (e : Basis ι ℝ L) (f : X → E → L)
    (hf : ∀ x i, ContDiff ℝ n (fun y => e.repr (f x y) i))
    (w : FreeSemigroup X) (k : ι) :
    ContDiff ℝ n (fun y => e.repr (dynkinWord (fun x => f x y) w) k) :=
  contDiff_rightBracketList_coordinates e f hf w.tail (f w.head) (hf w.head) k

variable [IsScalarTower ℚ ℝ L]

theorem contDiff_lieBCH_coordinates (e : Basis ι ℝ L) (s : ℕ) (f g : E → L)
    (hf : ∀ i, ContDiff ℝ n (fun x => e.repr (f x) i))
    (hg : ∀ i, ContDiff ℝ n (fun x => e.repr (g x) i)) (k : ι) :
    ContDiff ℝ n (fun x => e.repr (lieBCH s (f x) (g x)) k) := by
  change ContDiff ℝ n (fun x => e.coord k (lieBCH s (f x) (g x)))
  simp only [lieBCH_bracket_formula, map_sum, LinearMap.map_smul_of_tower,
    Algebra.smul_def, Basis.coord_apply]
  apply ContDiff.sum
  intro w _
  apply contDiff_const.mul
  exact contDiff_dynkinWord_coordinates e (fun i x => ![f x, g x] i)
    (by intro i k; fin_cases i; exact hf k; exact hg k) w k

theorem contDiff_coordinateBCH (e : Basis ι ℝ L) (s : ℕ) :
    ContDiff ℝ n (fun z : (ι → ℝ) × (ι → ℝ) =>
      e.equivFun (lieBCH s (e.equivFun.symm z.1) (e.equivFun.symm z.2))) := by
  apply contDiff_pi.mpr
  intro k
  apply contDiff_lieBCH_coordinates e s
  · intro i
    change ContDiff ℝ n (fun z : (ι → ℝ) × (ι → ℝ) =>
      e.equivFun (e.equivFun.symm z.1) i)
    simp only [LinearEquiv.apply_symm_apply]
    exact (contDiff_apply ℝ ℝ i).comp contDiff_fst
  · intro i
    change ContDiff ℝ n (fun z : (ι → ℝ) × (ι → ℝ) =>
      e.equivFun (e.equivFun.symm z.2) i)
    simp only [LinearEquiv.apply_symm_apply]
    exact (contDiff_apply ℝ ℝ i).comp contDiff_snd

end Erdos3

end

end OAI
