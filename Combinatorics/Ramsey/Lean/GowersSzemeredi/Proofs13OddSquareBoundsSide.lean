import GowersSzemeredi.Proofs13OddSquareBounds

/-! Declarations of `Proofs13OddSquareBounds` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

namespace LeanProofs.GowersSzemeredi

/-- The explicit Fourier extraction exponent lies in (0,1/2]. -/
theorem section13_explicit_exponent_bounds {alpha : Real}
    (hα : 0 < alpha) (hαone : alpha ≤ 1) :
    0 < (1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 88)) ∧
      (1 / 2 : Real) ^ ((2 / alpha) ^ ((2 : Nat) ^ 88)) ≤ 1 / 2 := by
  refine ⟨Real.rpow_pos_of_pos (by norm_num) _, ?_⟩
  have ht : (1 : Real) ≤ 2 / alpha := (le_div_iff₀ hα).mpr (by linarith only [hαone])
  have hexp := one_le_pow₀ ht (n := (2 : Nat) ^ 88)
  simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge
    (by norm_num : (0 : Real) < 1 / 2) (by norm_num : (1 / 2 : Real) ≤ 1) hexp

end LeanProofs.GowersSzemeredi
