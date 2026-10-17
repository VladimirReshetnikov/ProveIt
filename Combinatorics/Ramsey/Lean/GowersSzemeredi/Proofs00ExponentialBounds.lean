import GowersSzemeredi.Proofs00Basics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! Phase estimates for `exponential`: `‖e(x) − 1‖ ≤ 2π|x|/N` and `≤ 2`, and the
resulting bound `‖e(rd) − 1‖ ≤ 2πε` for `d ∈ Bohr(K, ε)`, `r ∈ K`. They need
`Real.norm_exp_I_mul_ofReal_sub_one_le`, which `Proofs00Basics` does not see. -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

/-- `‖e(x) − 1‖ ≤ 2π|x|/N`, with `|x|` the centered absolute value. -/
lemma cor57_norm_exponential_sub_one_le {N : Nat} [NeZero N]
    (x : ZMod N) :
    ‖exponential x - 1‖ ≤ 2 * Real.pi * centeredAbs x / N := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have habsval : |(x.valMinAbs : Real)| = (centeredAbs x : Real) := by
    rw [centeredAbs, ← Int.cast_abs, Int.abs_eq_natAbs]
    rfl
  rw [cor24_exponential_eq_exp_valMinAbs]
  calc
    ‖Complex.exp
        (Complex.I * (2 * Real.pi * (x.valMinAbs : Real) / N : Real)) - 1‖ ≤
        ‖2 * Real.pi * (x.valMinAbs : Real) / N‖ :=
      Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = 2 * Real.pi * centeredAbs x / N := by
      rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul,
        abs_of_nonneg (by norm_num : (0 : Real) ≤ 2),
        abs_of_pos Real.pi_pos, habsval, abs_of_pos hN]

/-- `‖e(x) − 1‖ ≤ 2`. -/
lemma norm_exponential_sub_one_le_two {N : Nat} [NeZero N] (x : ZMod N) :
    ‖exponential x - 1‖ ≤ 2 := by
  calc
    ‖exponential x - 1‖ ≤ ‖exponential x‖ + ‖(1 : Complex)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [cor57_norm_exponential]

/-- On `Bohr(K, ε)`, every character of `K` is within `2πε` of `1`. -/
lemma bohr_phase_bound {N : Nat} [NeZero N]
    (K : Finset (ZMod N)) (epsilon : Real) (d : ZMod N)
    (hd : d ∈ bohr K epsilon) (r : ZMod N) (hr : r ∈ K) :
    ‖exponential (r * d) - 1‖ ≤ 2 * Real.pi * epsilon := by
  rw [bohr, Finset.mem_filter] at hd
  have hcenter := hd.2 r hr
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  calc
    ‖exponential (r * d) - 1‖ ≤
        2 * Real.pi * centeredAbs (r * d) / N :=
      cor57_norm_exponential_sub_one_le (r * d)
    _ ≤ 2 * Real.pi * epsilon := by
      apply (div_le_iff₀ hN).2
      nlinarith [Real.pi_pos]

end LeanProofs.GowersSzemeredi
