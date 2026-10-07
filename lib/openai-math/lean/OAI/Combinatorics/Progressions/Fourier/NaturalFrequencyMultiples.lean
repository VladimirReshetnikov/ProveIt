/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Estimates.NativeCentralSeed

namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem rationalLogHeight_nat_mul (n : ℕ) {x : ℚ} {p : ℝ}
    (hx : rationalLogHeight x ≤ p) : rationalLogHeight ((n : ℚ) * x) ≤ p + n + 1 := by
  have hp : 0 ≤ p := (rationalLogHeight_nonneg x).trans hx
  have hn : RationalHeightLE (n : ℚ) (n + 1) := by
    simp [RationalHeightLE]
  apply rationalLogHeight_le_of_height (hn.mul (rationalHeightLE_ceil_exp hx))
  calc
    (((n + 1) * ⌈Real.exp p⌉₊ : ℕ) : ℝ) = ((n : ℝ) + 1) * (⌈Real.exp p⌉₊ : ℝ) := by push_cast; rfl
    _ ≤ Real.exp (n : ℝ) * Real.exp (p + 1) :=
      mul_le_mul (Real.add_one_le_exp _) (ceil_exp_le_exp_add_one hp)
        (Nat.cast_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (p + n + 1) := by rw [← Real.exp_add]; congr 1; ring

theorem realifyFunctional_nsmul {L : Type*} [AddCommGroup L] [Module ℚ L]
    (n : ℕ) (η : L →ₗ[ℚ] ℚ) (x : ℝ ⊗[ℚ] L) :
    realifyFunctional (n • η) x = n • realifyFunctional η x := by
  induction x using TensorProduct.inductionOn with
  | tmul r x =>
    simp only [realifyFunctional_tmul, LinearMap.smul_apply, nsmul_eq_mul,
      Rat.cast_mul, Rat.cast_natCast]
    ring
  | add x y hx hy => simp only [map_add, hx, hy, smul_add]

end Erdos3

end

end OAI
