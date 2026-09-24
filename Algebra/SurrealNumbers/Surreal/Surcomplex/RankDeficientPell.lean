import Surreal.Surcomplex.PellRigidity
import Surreal.Foundations.OmnificRealScaling
import Surreal.Foundations.OmnificConstantRigidity
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# A rank-deficient Pell level with nonordinary omnific solutions

The example `odg:dec:ex:rankdeficient`. The two linear factors have the
common real kernel R(1,0,-1). Nonzero Pell rigidity applied to (x+z,y)
gives the exact purely infinite parametrization of the three-variable
fiber. The explicit point (3-omega,2,omega) has an infinite coordinate.
-/

universe u
namespace Surreal.Surcomplex

open Foundations SignSequence

noncomputable section

/-- Coefficients of X + Z + rY and X + Z - rY. -/
def splitPellMatrix (r : ℝ) : Matrix (Fin 2) (Fin 3) ℝ :=
  ![![1, r, 1], ![1, -r, 1]]

/-- The common kernel of the two linear factors is exactly the direction (1,0,-1). -/
theorem splitPellMatrix_kernel_iff (r : ℝ) (hr : r ≠ 0) (v : Fin 3 → ℝ) :
    v ∈ LinearMap.ker (splitPellMatrix r).mulVecLin ↔
      ∃ t : ℝ, v = ![t, 0, -t] := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    change (splitPellMatrix r).mulVec v 0 = 0 at h0
    change (splitPellMatrix r).mulVec v 1 = 0 at h1
    simp [Matrix.mulVec, dotProduct, splitPellMatrix, Fin.sum_univ_three] at h0 h1
    have hy : v 1 = 0 := by
      apply (mul_eq_zero.mp (show r * v 1 = 0 by linarith)).resolve_left hr
    refine ⟨v 0, ?_⟩
    ext k
    fin_cases k
    · rfl
    · exact hy
    · change v 2 = -(v 0)
      rw [hy] at h0
      linarith
  · rintro ⟨t, rfl⟩
    ext j
    fin_cases j <;> simp [Matrix.mulVec, dotProduct, splitPellMatrix, Fin.sum_univ_three]

/-- The actual square-root-of-two factors have precisely the source's one-dimensional kernel. -/
theorem rankDeficientPell_kernel_iff (v : Fin 3 → ℝ) :
    v ∈ LinearMap.ker (splitPellMatrix (Real.sqrt 2)).mulVecLin ↔
      ∃ t : ℝ, v = ![t, 0, -t] :=
  splitPellMatrix_kernel_iff _ (ne_of_gt (Real.sqrt_pos.mpr (by norm_num))) v

/-- The two displayed real factors multiply to the three-variable Pell form. -/
theorem rankDeficientPell_factor (x y z : ℝ) :
    (x + z + Real.sqrt 2 * y) * (x + z - Real.sqrt 2 * y) = (x + z) ^ 2 - 2 * y ^ 2 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [sq_nonneg (x + z - Real.sqrt 2 * y)]

/-- The exact three-variable fiber, for any nonzero ordinary norm parameter and level. -/
theorem omnific_rankDeficient_pell_solutions_iff (D c : ℤ) (hD : D ≠ 0) (hc : c ≠ 0)
    (x y z : OmnificInteger.{u}) :
    (x + z) ^ 2 - omnificIntCast D * y ^ 2 = omnificIntCast c ↔
      ∃ a b d : ℤ, ∃ t : omnificPurelyInfiniteIdeal.{u},
        (a + d) ^ 2 - D * b ^ 2 = c ∧
          x = omnificIntCast a + t.val ∧ y = omnificIntCast b ∧
            z = omnificIntCast d - t.val := by
  constructor
  · intro h
    obtain ⟨hxz, hy⟩ := omnific_pell_rigidity D c hD hc (x + z) y h
    obtain ⟨t, ht, hx⟩ := omnific_constant_decomposition x
    refine ⟨omnificConstantCoeff x, omnificConstantCoeff y, omnificConstantCoeff z,
      ⟨t, ht⟩, ?_, hx, hy, ?_⟩
    · have he := congrArg omnificConstantCoeff h
      simpa only [map_sub, map_pow, map_mul, map_add, omnificConstantCoeff_intCast] using he
    · rw [map_add, map_add] at hxz
      rw [hx] at hxz
      simp only [map_add, omnificConstantCoeff_intCast, show omnificConstantCoeff t = 0 from ht,
        _root_.add_zero] at hxz
      linear_combination hxz
  · rintro ⟨a, b, d, t, he, rfl, rfl, rfl⟩
    have hs : omnificIntCast a + t.val + (omnificIntCast d - t.val) =
        omnificIntCast (a + d) := by rw [map_add]; ring
    rw [hs, ← map_pow, ← map_pow, ← map_mul, ← map_sub, he]

/-- The exact displayed family in the manuscript's rank-deficient example. -/
theorem omnific_rankDeficient_pell_two_iff (x y z : OmnificInteger.{u}) :
    (x + z) ^ 2 - omnificIntCast 2 * y ^ 2 = omnificIntCast 1 ↔
      ∃ a b d : ℤ, ∃ t : omnificPurelyInfiniteIdeal.{u},
        (a + d) ^ 2 - 2 * b ^ 2 = 1 ∧
          x = omnificIntCast a + t.val ∧ y = omnificIntCast b ∧
            z = omnificIntCast d - t.val :=
  omnific_rankDeficient_pell_solutions_iff 2 1 (by norm_num) (by norm_num) x y z

/-- The point (3-omega,2,omega) solves the level-one equation and is nonordinary. -/
theorem omnific_rankDeficient_pell_omega :
    let w : OmnificInteger.{u} := omnificMonomial 1 SignSequence.zero_lt_one
    ((omnificIntCast 3 - w) + w) ^ 2 - omnificIntCast 2 * (omnificIntCast 2) ^ 2 =
      omnificIntCast 1 ∧ ¬ SignSequence.IsFinite (omnificToSurreal w) := by
  dsimp only
  constructor
  · rw [sub_add_cancel, ← map_pow, ← map_pow, ← map_mul, ← map_sub]
    norm_num
  · exact omnific_purelyInfinite_not_finite _
      (omnificMonomial_mem_purelyInfinite 1 SignSequence.zero_lt_one)
      (omnificMonomial_ne_zero 1 SignSequence.zero_lt_one)

end
end Surreal.Surcomplex
